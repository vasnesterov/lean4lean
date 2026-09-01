import Lean4Lean.Verify.Inductive.AddDeclWF

set_option linter.unusedSimpArgs false

/-!
# `AddInductiveStepWF`: the decomposition, and the half of it that is closed

`Verify/Inductive/AddDeclWF.lean` §5 replaces the refuted `inductDecl` branch of `addDecl.WF`
by `addDecl.WF_honest`, which is proved from the single obligation

```
def AddInductiveStepWF : Prop :=
  ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
    ∀ lp np types ap fuel,
      (Environment.addInductive env lp np types false ap fuel).WF fun env' =>
        AddInductPost env env' ves lp np types
```

This file measures that obligation against the executable and closes its first half.

## The finding: under `ves.WF env`, `numNested` is forced to `0`

**The nested apparatus of `Environment.addInductive` is unreachable under the premise.**  The
chain, all machine-checked below:

* `ves.WF env` gives `env.find? n ≠ some (.inductInfo v)` for every `n` and `v`
  (`VEnvs.WF.no_inductInfo` composed with `SMap.WF.find?'_eq_find?`) — §2.
* `ElimNestedInductive.isNestedInductiveApp?` returns `none` unless
  `env.find? fn = some (.inductInfo ci)`, so it returns `none` everywhere; hence
  `replaceIfNested` declines every subterm, hence `replaceAllNested` is the identity and never
  pushes to `State.nestedAux` — §3.
* `nestedAux` therefore stays `#[]` through `ElimNestedInductive.run` (whose loop writes only
  `newTypes`), so `res.aux2nested = []` and `numNested = res.aux2nested.length = 0` — §4.
* So `Environment.addInductive` collapses to its `numNested = 0` exit: the guard loop, then
  `ElimNestedInductive.run`, then `AddInductive.run`, then `return env'`.  The whole
  `mkAuxRecNameMap`/`restoreNested` rebuild and its three re-check passes are **dead code**
  under this premise — §5, `addInductive_WF_of_run`.

This is a **correction to any framing that treats the nested machinery as live content of
`AddInductiveStepWF`**: it is not, and cannot be, until `VEnvs.WF` is satisfiable at an
environment that already holds an `.inductInfo`.  The same observation shows the premise is
close to vacuous — `ves.WF env` holds only at environments with no `.inductInfo` at all, so
`AddInductiveStepWF` is only ever applied to the *first* inductive block of an environment.
Both facts make the obligation easier than it looks, and limit what closing it buys: the
nested-aware `numNested` of `AddInductPost` is witnessed by `0` here, so the nested content of
`InductStepNested` is discharged by the conservativity bridges (`TrIndDecl.toN`,
`AddInductStages.toR`) rather than by anything about nesting.

## What is left

§6 states the residue as one named `def`, `AddInductiveRunRealises`, which is entirely about
`AddInductive.run` — no nesting, no `ElimNestedInductive` — and proves

```
theorem addInductiveStepWF_of_run : AddInductiveRunRealises → AddInductiveStepWF
```

`AddInductiveRunRealises` is an explicit hypothesis of that theorem, not an axiom.  Nothing
here weakens `AddInductiveStepWF`, introduces an axiom, or adds a `sorry`; `AddInductiveStepWF`
is used verbatim as `AddDeclWF.lean` states it.

Note on `Verify/Guard.lean` check 3: `ElimNestedInductive.run.loop` and
`ElimNestedInductive.withParams.loop` appear in `implGapWhitelist` marked `-- partial`, but
neither carries the `partial` keyword — they are structural/WF-compiled definitions with
bodies and equation lemmas, which is exactly why §1 and §4 below can reason about them by
`rw [run.loop]` and induction.  Check 3's test is `env.contains (n ++ "_unsafe_rec")`, which
over-approximates.  Guard is frozen and the entries must stay (removing them would make check
3 throw); this is a comment on the labels, not a request to change the file.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-- `Except.WF.bind` with the first component's postcondition taken to be its own success
equation — the shape needed to name the intermediate value of a `do` block. -/
theorem Except.WF.bind_self {ε α β} {x : Except ε α} {f : α → Except ε β} {R}
    (h : ∀ a, x = .ok a → (f a).WF R) : (x >>= f).WF R :=
  Except.WF.bind (Q := fun a => x = .ok a) (fun _ ha => ha) h

/-! ## 1. A `WF`-style toolkit for `ElimNestedInductive.M`

`ElimNestedInductive.M = ReaderT Environment <| StateT State <| Except Exception`.  The
`_eq` lemmas are the applied forms of the monad operations — proved by `with_unfolding_all
rfl`, so they are definitional — and `EWF` is the only postcondition this file needs: *on
success from a state with empty `nestedAux`, `nestedAux` is still empty and the value
satisfies `Q`*.  `nestedAux` is where `replaceIfNested` records nested occurrences and
`ElimNestedInductive.run`'s output `aux2nested` is a fold of it, so `EWF` is exactly what
propagates "no nesting happened". -/

namespace ElimNestedInductive

variable {α β : Type}

theorem get_eq (env : Environment) (s : State) : (get : M State) env s = .ok (s, s) := by
  with_unfolding_all rfl

theorem modify_eq (env : Environment) (f : State → State) (s : State) :
    (modify f : M PUnit) env s = .ok ((), f s) := by with_unfolding_all rfl

theorem mkFreshId_eq (env : Environment) (s : State) :
    (mkFreshId : M Name) env s = .ok (s.ngen.curr, { s with ngen := s.ngen.next }) := by
  with_unfolding_all rfl

theorem bind_eq (env : Environment) (x : M α) (f : α → M β) (s : State) :
    (x >>= f) env s = (x env s).bind (fun p => f p.1 env p.2) := by with_unfolding_all rfl

theorem pure_eq (env : Environment) (a : α) (s : State) :
    (Pure.pure a : M α) env s = .ok (a, s) := by with_unfolding_all rfl

theorem throw_eq (env : Environment) (e : Exception) (s : State) :
    (throw e : M α) env s = .error e := by with_unfolding_all rfl

theorem run'_eq (env : Environment) (x : M α) (s : State) :
    (x env).run' s = (x env s).map Prod.fst := by with_unfolding_all rfl

theorem bind_ok {env : Environment} {x : M α} {f : α → M β} {s a s'}
    (h : (x >>= f) env s = .ok (a, s')) :
    ∃ b s'', x env s = .ok (b, s'') ∧ f b env s'' = .ok (a, s') := by
  rw [bind_eq] at h
  cases hx : x env s with
  | error e => rw [hx] at h; exact absurd h nofun
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem run'_ok {env : Environment} {x : M α} {s a} (h : (x env).run' s = .ok a) :
    ∃ s', x env s = .ok (a, s') := by
  rw [run'_eq] at h
  cases hx : x env s with
  | error e => rw [hx] at h; simp [Except.map] at h
  | ok p =>
    rw [hx] at h
    refine ⟨p.2, ?_⟩
    have e : p.1 = a := by simpa [Except.map] using h
    rw [← e]

/-- On success from a state whose `nestedAux` is empty, `nestedAux` is still empty and the
returned value satisfies `Q`. -/
def EWF (env : Environment) (x : M α) (Q : α → Prop) : Prop :=
  ∀ s a s', s.nestedAux = #[] → x env s = .ok (a, s') → s'.nestedAux = #[] ∧ Q a

variable {env : Environment} {Q : α → Prop}

theorem EWF.pure' {a : α} (h : Q a) : EWF env (Pure.pure a) Q := by
  intro s b s' hs hb; rw [pure_eq] at hb; cases hb; exact ⟨hs, h⟩

theorem EWF.throw' (e : Exception) : EWF env (throw e : M α) Q := by
  intro s b s' _ hb; rw [throw_eq] at hb; exact absurd hb nofun

theorem EWF.get' : EWF env (get : M State) (fun s => s.nestedAux = #[]) := by
  intro s a s' hs h; rw [get_eq] at h; cases h; exact ⟨hs, hs⟩

theorem EWF.modify' {f : State → State} (hf : ∀ s, (f s).nestedAux = s.nestedAux) :
    EWF env (modify f : M PUnit) (fun _ => True) := by
  intro s a s' hs h; rw [modify_eq] at h; cases h; exact ⟨(hf s).trans hs, trivial⟩

theorem EWF.mkFreshId' : EWF env (mkFreshId : M Name) (fun _ => True) := by
  intro s a s' hs h; rw [mkFreshId_eq] at h; cases h; exact ⟨hs, trivial⟩

theorem EWF.bind' {x : M α} {f : α → M β} {R : β → Prop} (hx : EWF env x Q)
    (hf : ∀ a, Q a → EWF env (f a) R) : EWF env (x >>= f) R := by
  intro s b s' hs h
  obtain ⟨a, s'', h1, h2⟩ := bind_ok h
  obtain ⟨hs'', ha⟩ := hx s a s'' hs h1
  exact hf a ha s'' b s' hs'' h2

theorem EWF.mono {x : M α} {R : α → Prop} (hx : EWF env x Q) (h : ∀ a, Q a → R a) :
    EWF env x R := fun s a s' hs hr => let ⟨h1, h2⟩ := hx s a s' hs hr; ⟨h1, h _ h2⟩

theorem EWF.mapM' {f : α → M β} (hf : ∀ a, EWF env (f a) (fun _ => True)) :
    ∀ l : List α, EWF env (l.mapM f) (fun _ => True)
  | [] => by rw [List.mapM_nil]; exact EWF.pure' trivial
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind' fun _ _ => (EWF.mapM' hf l).bind' fun _ _ => EWF.pure' trivial

/-- `withParams` calls its continuation with exactly `n` parameters — which is what makes the
`assert!` inside `run.loop` unreachable — and transports `EWF`.

**Corrected 2026-09-01; the paragraph that stood here was wrong on both counts.**  It said the
`ps.size = n` conclusion is load-bearing because `assert!` elaborates to
`panicWithPosWithDecl`, which "in this monad returns `.ok (default, default)` rather than an
error", and that `(default : State).nestedAux = #[]` is not the incoming state.  In fact
`Inhabited (M α)` does **not** resolve through `Inhabited (Except ε α)` — that instance needs
`[Inhabited ε]` and `Inhabited Kernel.Exception` does not synthesise — so it resolves through
`instInhabitedOfMonad`, i.e. `pure default`: the value is `default` and the **incoming state is
untouched**.  Machine-checked as `ElimNestedInductive.panic_eq`
(`Verify/Inductive/NestedRunInvariant.lean`).

Consequences: on the panic branch `s' = s`, so `EWF`'s postcondition holds there for free and
`ps.size = n` is *not* load-bearing for the stated reason; and all five panic sites reachable
from `replaceAllNested` are invariant-preserving, which is what makes
`ElimNestedInductive.replaceAppendsOnly` provable with **no** environment or arity side
condition.  The conclusion is kept because callers use it, not because the assert forces it. -/
theorem EWF.withParams' {k : LocalContext → Expr → Array Expr → M α}
    (n : Nat) (hk : ∀ lctx t ps, ps.size = n → EWF env (k lctx t ps) Q) (type : Expr) :
    EWF env (withParams type n k) Q := by
  have main : ∀ i lctx t ps, ps.size + i = n → EWF env (withParams.loop k lctx t ps i) Q := by
    intro i
    induction i with
    | zero => intro lctx t ps hps; rw [withParams.loop]; exact hk lctx t ps (by omega)
    | succ i ih =>
      intro lctx t ps hps
      cases t with
      | forallE name dom body bi =>
        rw [withParams.loop]
        exact EWF.bind' EWF.mkFreshId' fun _ _ =>
          ih _ _ _ (by simp only [Array.size_push]; omega)
      | _ => rw [withParams.loop] <;> first | exact EWF.throw' _ | nofun
  exact main n {} type #[] (by simp)

end ElimNestedInductive

/-! ## 2. The premise, transported to the executable's `Environment.find?`

`VEnvs.WF.no_inductInfo` is stated about `env.constants.find?`; the executable reads the
environment through `Kernel.Environment.find? = env.constants.find?'`.  `TrEnv'.map_wf`
supplies the `SMap.WF` that identifies the two. -/

/-- **The premise of `AddInductiveStepWF` rules out every `.inductInfo`.**  This is
`VEnvs.WF.no_inductInfo` at the executable's own lookup function.  It is also the reason the
premise is nearly vacuous: `ves.WF env` cannot hold at an environment that already contains an
inductive type. -/
theorem VEnvs.WF.find?_ne_inductInfo {ves : VEnvs} {env : Environment} (wf : ves.WF env)
    {n : Name} {v : InductiveVal} : env.find? n ≠ some (.inductInfo v) := by
  rw [Kernel.Environment.find?, (wf.tr (safety := .unsafe)).map_wf.find?'_eq_find?]
  exact wf.no_inductInfo

/-! ## 3. No `.inductInfo` in the environment ⇒ `replaceAllNested` is the identity

`isNestedInductiveApp?` is the *only* entry to the nested path, and its second guard is
`let some (.inductInfo ci) := env.find? fn | return none`. -/

namespace ElimNestedInductive

/-- With no `.inductInfo` in the environment, nothing is a nested inductive application. -/
theorem isNestedInductiveApp?_none {env : Environment}
    (h : ∀ n v, env.find? n ≠ some (.inductInfo v)) (e : Expr) (s : State) :
    isNestedInductiveApp? e env s = .ok (none, s) := by
  by_cases h1 : e.isApp
  case neg =>
    simp [isNestedInductiveApp?, h1, bind, Except.bind, ReaderT.bind, StateT.bind,
      pure, Except.pure, ReaderT.pure, StateT.pure]
  case pos =>
    cases hfn : e.getAppFn with
    | const fn us =>
      cases hc : env.find? fn with
      | none =>
        simp [isNestedInductiveApp?, h1, hfn, hc, bind, Except.bind, ReaderT.bind, StateT.bind,
          pure, Except.pure, ReaderT.pure, StateT.pure, read, readThe, MonadReaderOf.read,
          ReaderT.read]
      | some c =>
        cases c with
        | inductInfo v => exact absurd hc (h _ _)
        | _ =>
          simp [isNestedInductiveApp?, h1, hfn, hc, bind, Except.bind, ReaderT.bind, StateT.bind,
            pure, Except.pure, ReaderT.pure, StateT.pure, read, readThe, MonadReaderOf.read,
            ReaderT.read]
    | _ =>
      simp [isNestedInductiveApp?, h1, hfn, bind, Except.bind, ReaderT.bind, StateT.bind,
        pure, Except.pure, ReaderT.pure, StateT.pure, read, readThe, MonadReaderOf.read,
        ReaderT.read]

/-- Hence `replaceIfNested` declines every subterm, without touching the state — in particular
without pushing to `nestedAux`, its only writer. -/
theorem replaceIfNested_none {env : Environment}
    (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    (lctx : LocalContext) (params As : Array Expr) (e : Expr) (s : State) :
    replaceIfNested lctx params As e env s = .ok (none, s) := by
  simp [replaceIfNested, isNestedInductiveApp?_none h, bind, Except.bind, ReaderT.bind,
    StateT.bind, pure, Except.pure, ReaderT.pure, StateT.pure]

/-- Hence the whole traversal is the identity. -/
theorem replaceAllNested_id {env : Environment}
    (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    (lctx : LocalContext) (params As : Array Expr) (e : Expr) (s : State) :
    replaceAllNested lctx params As e env s = .ok (e, s) := by
  unfold replaceAllNested
  induction e generalizing s with
  | _ =>
    rw [Lean.Expr.replaceNoCacheT]
    simp only [bind, ReaderT.bind, StateT.bind, Except.bind, replaceIfNested_none h,
      pure, ReaderT.pure, StateT.pure, Except.pure, *]
    all_goals first
      | rfl
      | simp [Lean.Expr.updateApp!, Lean.Expr.updateForallE!, Lean.Expr.updateLambdaE!,
          Lean.Expr.updateMData!, Lean.Expr.updateLet!, Lean.Expr.updateProj!]

theorem EWF.replaceAllNested' {env : Environment}
    (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    (lctx : LocalContext) (params As : Array Expr) (e : Expr) :
    EWF env (replaceAllNested lctx params As e) (fun _ => True) := by
  intro s a s' hs h'
  rw [replaceAllNested_id h] at h'
  cases h'; exact ⟨hs, trivial⟩

/-! ## 4. `nestedAux` stays empty, so `numNested = 0` -/

/-- The loop of `ElimNestedInductive.run` never populates `nestedAux`, so it returns an empty
`aux2nested`. -/
theorem run_loop_EWF {env : Environment}
    (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    (nparams : Nat) (lctx : LocalContext) (params : Array Expr) : ∀ fuel i : Nat,
      EWF env (run.loop nparams lctx params i fuel) (fun r => r.aux2nested = []) := by
  intro fuel
  induction fuel with
  | zero => intro i; rw [run.loop]; exact EWF.throw' _
  | succ fuel ih =>
    intro i
    rw [run.loop]
    refine EWF.bind' EWF.get' fun s hs => ?_
    split
    · refine EWF.bind' (EWF.mapM' (fun ctor => ?_) _) fun ctors _ => ?_
      · refine EWF.withParams' nparams (fun lctx' t As hAs => ?_) _
        rw [hAs]
        simp only [beq_self_eq_true, if_true]
        exact (EWF.replaceAllNested' h _ _ _ _).bind' fun _ _ => EWF.pure' trivial
      · exact EWF.bind' (EWF.modify' fun _ => rfl) fun _ _ => ih (i+1)
    · refine EWF.pure' ?_
      show Array.foldl _ [] s.nestedAux = []
      rw [hs]; rfl

/-- **`ElimNestedInductive.run` reports no nesting.** -/
theorem run_EWF {env : Environment} (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    (fuel nparams : Nat) (types : List InductiveType) :
    EWF env (run fuel nparams types) (fun r => r.aux2nested = []) := by
  unfold run
  split
  · refine EWF.bind' (EWF.modify' fun _ => rfl) fun _ _ => ?_
    exact EWF.withParams' nparams (fun lctx t ps _ => run_loop_EWF h _ _ _ fuel 0) _
  · exact EWF.throw' _

/-- The `run'` form, as `Environment.addInductive` calls it. -/
theorem run_run'_aux2nested {env : Environment} (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    (fuel nparams : Nat) (types : List InductiveType) (s : State) (hs : s.nestedAux = #[])
    (r : Result) (hr : (run fuel nparams types env).run' s = .ok r) : r.aux2nested = [] :=
  let ⟨_, hr⟩ := run'_ok hr; (run_EWF h fuel nparams types s r _ hs hr).2

end ElimNestedInductive

/-! ## 5. `Environment.addInductive` collapses to `AddInductive.run`

Everything after `if numNested = 0 then return env'` is unreachable when the environment holds
no `.inductInfo`, so the postcondition of `addInductive` follows from a postcondition of
`AddInductive.run` alone. -/

/-- **The collapse.**  Under the no-`.inductInfo` hypothesis, any postcondition `Q` of the
single call `AddInductive.run np res.types 0 …` is a postcondition of the whole of
`Environment.addInductive`.  The nested rebuild — `mkAuxRecNameMap`, `restoreNested`, and the
three `TypeChecker.M.run` re-check passes — never runs. -/
theorem addInductive_WF_of_run {env : Environment} {lparams : List Name} {np : Nat}
    {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig} {Q : Environment → Prop}
    (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    (H : ∀ res : ElimNestedInductive.Result,
        (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
            { lvls := lparams.map .param, newTypes := types.toArray } = .ok res →
        res.aux2nested = [] →
        (AddInductive.run np res.types 0
          { env, allowPrimitive := ap, lparams,
            safety := if iu then .unsafe else .safe, fuel }).WF Q) :
    (Environment.addInductive env lparams np types iu ap fuel).WF Q := by
  unfold Environment.addInductive
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
  refine Except.WF.bind_self fun res hres => ?_
  have hz : res.aux2nested = [] :=
    ElimNestedInductive.run_run'_aux2nested h _ _ _ _ rfl _ hres
  simp only [hz, List.length_nil]
  refine Except.WF.bind (H res hres hz) fun env' hq => ?_
  simp only [if_true]
  exact Except.WF.pure hq

/-! ## 6. The residue

What is left is entirely about `AddInductive.run`: it must realise one abstract `AddInductStages`
step, for a canonical `VInductDecl'` translating the block.  `D.Canonical` appears explicitly
because the conservativity bridges `TrIndDecl.toN` and `AddInductStages.toR` both need it, and
`InductStepNested` hides `D` under an existential, so it cannot be recovered afterwards.

**The next lemma to prove, and the one thing §4 does not give.**  `AddInductive.run` is called
on `res.types`, while `TrIndDecl` speaks of the *input* `types`.  With `replaceAllNested` the
identity (§3), each constructor type of `res.types` is `lctx.mkForall As ctorType` where `As`
are the `nparams` fvars `withParams` introduced by `instantiate1` — i.e. `types` put through an
abstract/instantiate round trip.  `res.types = types` looks provable and would remove
`ElimNestedInductive` from the residue entirely, but it needs `Expr.abstract`/`instantiate`
inverse lemmas (whose executable forms are frozen axioms here), so it is left as stated:
`AddInductiveRunRealises` mentions `res` and its success equation, and any proof of it may use
that equation to identify `res.types`. -/

/-- **The remaining obligation, named.**  `AddInductive.run` — with no nesting, no
`ElimNestedInductive`, and `numNested = 0` — produces an environment that realises an
`AddInductStages` step for a canonical translation of the block.

This is an explicit hypothesis of `addInductiveStepWF_of_run` below, **not** an axiom: nothing
in this file assumes it. -/
def AddInductiveRunRealises : Prop :=
  ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
    ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (ap : Bool) (fuel : FuelConfig)
      (res : ElimNestedInductive.Result),
      (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
          { lvls := lp.map .param, newTypes := types.toArray } = .ok res →
      res.aux2nested = [] →
      (AddInductive.run np res.types 0
          { env, allowPrimitive := ap, lparams := lp, safety := .safe, fuel }).WF fun env' =>
        ∃ ves' : VEnvs, ∀ safety, ∃ D : VInductDecl',
          TrIndDecl (ves.venv safety) lp np types false D ∧
          D.WF (ves.venv safety) ∧ D.Canonical ∧
          AddInductStages env.constants (ves.venv safety) D env'.constants (ves'.venv safety)

/-- **`AddInductiveStepWF` reduces to `AddInductive.run`.**  The statement of
`AddInductiveStepWF` is `AddDeclWF.lean`'s, unchanged and unweakened; `numNested` is witnessed
by `0` because §4 forces it. -/
theorem addInductiveStepWF_of_run (H : AddInductiveRunRealises) : AddInductiveStepWF := by
  intro env ves wf lp np types ap fuel
  refine addInductive_WF_of_run (fun _ _ => wf.find?_ne_inductInfo) fun res hres hz => ?_
  refine (H wf lp np types ap fuel res hres hz).mono fun env' h' => ?_
  obtain ⟨ves', hves⟩ := h'
  refine ⟨ves', 0, fun safety => ?_⟩
  obtain ⟨D, htr, hwf, hc, hadd⟩ := hves safety
  exact ⟨D, [], D.idRestore, htr.toN hc, hadd.addIndTypes, hwf, hadd.toR hc⟩

/-- **The chain, end to end.**  The residue implies `addDecl.WF_honest` — the honest
restatement of `addDecl.WF` — with nothing else added.

`#print axioms` on this one reports `sorryAx`, inherited from `addDecl.WF_honest`'s six
non-inductive branches (`inferProj.WF`, `isDefEqUnitLike.WF`, `tryEtaStructCore.WF`,
`TrProj.uniq`, …).  Nothing in *this* file contains a `sorry`: every other theorem here has
axioms `{propext, Classical.choice, Quot.sound}` only. -/
theorem addDecl.WF_honest_of_run (H : AddInductiveRunRealises) {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) (decl : Declaration) (fuel : FuelConfig := {}) :
    (Lean4Lean.addDecl env decl (check := true) (fuel := fuel)).WF (AddDeclPost env decl ves) :=
  addDecl.WF_honest (addInductiveStepWF_of_run H) wf decl fuel
