import Lean4Lean.Verify.Inductive.NestedRebuild
import Lean4Lean.Verify.Inductive.NoNestedAll

/-!
# Residual B, finished: the nested rebuild block assembled

`Verify/Inductive/InductMap.lean` reduced `InductiveMapGate` to one hypothesis, `GB`, the nested
rebuild branch (`numNested ≠ 0`).  `NestedRebuild.lean` named the freshness barrier
(`RunFreshGate`), budgeted the four `add` sites and built a `StateT Environment (Except Exception)`
delta calculus (`SWF`); `NIndices.lean` discharged the barrier, so `runFreshGate` is a closed term
and every `G`-parametrised result there is unconditional.  What was left is the *assembly*: apply the
calculus to the actual `do`-block at `Inductive/Add.lean`:1156-1211 and remove `GB`.

## §0 The measurement that decided this file's shape

The handed-over itemisation priced the remainder as "`forIn` loop rules + block assembly 130,
`run_prefix` bridging 30".  Reading the block first (`docs/handoff-rebuildfinish.md` M1) turned up
**six** `unreachable!`s inside it — three of them between two `add` sites — and none of them is in
that itemisation.  A `panic` in a monad had already cost `NIndices.lean` its whole §1, and its prose
says a panic branch proves nothing at all.

Measured, that prose is wrong, and the branches are **free**:

```lean
example (env : Environment) :
    (unreachable! : StateT Environment (Except Exception) Unit) env = .ok (default, env) := rfl
```

Two reasons, both needed: `panicCore` is an `@[extern] def` with body `default`, not a body-less
`opaque`, so it unfolds in the logic; and the `Inhabited` instance at a monadic type is
`instInhabitedOfMonad = pure default`, **not** `fun _ => default`, so the state is preserved by
construction of the instance.  (The proof that it is the monad instance: the `rfl` above needs no
`Inhabited Kernel.Environment`, which the function instance would have demanded — and no such
instance exists.)  `Verify/Inductive/NestedRunInvariant.lean` §4 says the same thing for
`ElimNestedInductive.M`; this is that observation at the rebuild's monad, and §1 below is the rule.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

variable {α β : Type} {e₀ : Environment} {B : Name → Prop} {P : Environment → Prop}

/-! ## §1 `panic` in the rebuild's monad: state-preserving, value `default`

The rebuild's three state-affecting `unreachable!`s (`Inductive/Add.lean`:1157, :1170, :1174) sit
between `add` sites, so a delta calculus that could not pass through them would have to *exclude*
them — i.e. prove that `AddInductive.run` positively stored an `.inductInfo`/`.ctorInfo`/`.recInfo`
at each key read back.  Nothing in the tree proves that (`grep "some (.recInfo"` over `Verify/`
finds only witness-specific instances at concrete environments), and it would be a fourth field of
`RunFreshGate`.  §1 makes all of that unnecessary. -/

/-- **The panic value in `StateT Environment (Except Exception)`**: the state is untouched. -/
theorem panic_stateT_eq {α} [Inhabited α] (m d : String) (l c : Nat) (msg : String)
    (env : Environment) :
    (panicWithPosWithDecl m d l c msg : StateT Environment (Except Exception) α) env
      = .ok (default, env) := rfl

/-- **The `SWF` rule for a panic branch.**  No side condition, and the postcondition even reports
the value, so a caller that needs `a = default` (as the `mkAuxRecNameMap` call site does) has it. -/
theorem SWF.panic' {α} [Inhabited α] {m d : String} {l c : Nat} {msg : String} :
    SWF e₀ B P (panicWithPosWithDecl m d l c msg : StateT Environment (Except Exception) α)
      (fun a env => a = default ∧ P env) := by
  intro env a env' hd hp hok
  rw [panic_stateT_eq] at hok
  obtain ⟨rfl, rfl⟩ : (default : α) = a ∧ env = env' := by
    have h2 := Except.ok.inj hok
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  exact ⟨hd, rfl, hp⟩

/-- The weakened form used at every match branch: a panic preserves the invariant. -/
theorem SWF.panic_weak {α} [Inhabited α] {m d : String} {l c : Nat} {msg : String}
    {Q : α → Environment → Prop} (h : ∀ env, P env → Q default env) :
    SWF e₀ B P (panicWithPosWithDecl m d l c msg : StateT Environment (Except Exception) α) Q :=
  SWF.panic'.mono fun _a env => fun ⟨he, hp⟩ => he ▸ h env hp

/-! ## §2 The loop rules the block actually needs

`SWF.forM'` (`NestedRebuild.lean` §3) is `List.forM` at a trivial pre/postcondition.  The block uses
`forIn` in **four** places — `for indType in types`, the inner `for ctorName in ind.ctors`, and two
accumulator loops building `recNames` — plus a `List.mapM` inside `processRec`.  One rule covers all
four `for`s, at an arbitrary *preserved* invariant `P` rather than at `True`, because the `mapM`
inside `processRec` sits under `checkName`'s postcondition. -/

/-- **The `forIn` rule.**  `β` is the accumulator; the body may `.done` or `.yield`. -/
theorem SWF.forIn' {l : List α} {init : β}
    {f : α → β → StateT Environment (Except Exception) (ForInStep β)}
    (h : ∀ a ∈ l, ∀ b, SWF e₀ B P (f a b) (fun _ env => P env)) :
    SWF e₀ B P (forIn l init f) (fun _ env => P env) := by
  induction l generalizing init with
  | nil => exact SWF.pure' fun _ hp => hp
  | cons a l ih =>
    rw [List.forIn_cons]
    refine SWF.bind' (Q := fun _ env => P env) (h a (.head _) init) fun s => ?_
    cases s with
    | done b => exact SWF.pure' fun _ hp => hp
    | yield b => exact ih fun a' ha' b' => h a' (.tail _ ha') b'

/-- **The `mapM` rule**, at the same preserved invariant. -/
theorem SWF.mapM' {l : List α} {f : α → StateT Environment (Except Exception) β}
    (h : ∀ a ∈ l, SWF e₀ B P (f a) (fun _ env => P env)) :
    SWF e₀ B P (l.mapM f) (fun _ env => P env) := by
  induction l with
  | nil => rw [List.mapM_nil]; exact SWF.pure' fun _ hp => hp
  | cons a l ih =>
    rw [List.mapM_cons]
    refine SWF.bind' (Q := fun _ env => P env) (h a (.head _)) fun _ => ?_
    refine SWF.bind' (Q := fun _ env => P env) (ih fun a' ha' => h a' (.tail _ ha')) fun _ => ?_
    exact SWF.pure' fun _ hp => hp

/-- Lifting an `Except` whose value is irrelevant — the shape of the two `TypeChecker.M.run`
re-check passes, which `handoff-nestedrebuild.md` M5.4 recorded as an *unverified inspection*.
This is the verification: they are `liftM`s, so the state is untouched. -/
theorem SWF.liftTriv {y : Except Exception α} :
    SWF e₀ B P (liftM y : StateT Environment (Except Exception) α) (fun _ env => P env) :=
  SWF.lift' fun _ _ _ hp => hp

/-- The top-level bridge: an `SWF` at the *start* environment is a `DeltaCore`. -/
theorem SWF.toDelta {x : StateT Environment (Except Exception) α} {env env' : Environment} {a : α}
    (h : SWF env B (fun _ => True) x (fun _ _ => True)) (wf : env.constants.WF)
    (hok : x env = .ok (a, env')) : DeltaCore env env' B :=
  (h env a env' (DeltaCore.rfl' wf) trivial hok).1

/-! ## §3 `run_prefix`, in the form the write-site lemmas consume

`NestedRebuild.lean`'s two gated write-site lemmas want `t ∈ res.types` together with
`∃ u ∈ types, u.name = t.name` (resp. the constructor-name list).  The rebuild's loop runs over
`types`, so what is needed is the *other* direction: every `u ∈ types` has a member of `res.types`
with its name and constructor names.  `ElimNestedInductive.run_prefix` gives the entrywise form at an
index; `runSkelExtends` supplies the length that makes the index available. -/

theorem ElimNestedInductive.run_mem {fuel np : Nat} {types : List InductiveType}
    {env : Environment} {s : ElimNestedInductive.State} {res : ElimNestedInductive.Result}
    (hs : s.newTypes.toList = types)
    (hres : (ElimNestedInductive.run fuel np types env).run' s = .ok res) :
    ∀ u ∈ types, ∃ t ∈ res.types, t.name = u.name ∧
      t.ctors.map (·.name) = u.ctors.map (·.name) := by
  obtain ⟨s', hrun⟩ : ∃ s', ElimNestedInductive.run fuel np types env s = .ok (res, s') := by
    rw [show ((ElimNestedInductive.run fuel np types env).run' s)
        = (Prod.fst <$> ElimNestedInductive.run fuel np types env s) from rfl] at hres
    cases h : ElimNestedInductive.run fuel np types env s with
    | error e => rw [h] at hres; exact absurd hres nofun
    | ok p =>
      rw [h] at hres
      obtain ⟨a, s'⟩ := p
      have ha : a = res := Except.ok.inj hres
      subst ha
      exact ⟨s', rfl⟩
  obtain ⟨tail, htail⟩ := ElimNestedInductive.runSkelExtends env fuel np types s res s' hrun
  rw [hs] at htail
  have hlen : types.length ≤ res.types.length := by
    have h := congrArg List.length htail
    simp only [ElimNestedInductive.nameSkel, List.length_map, List.length_append] at h
    omega
  intro u hu
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hu
  have hjlen : j < types.length := by
    rcases List.getElem?_eq_some_iff.1 hj with ⟨h, -⟩; exact h
  have ht : res.types[j]? = some res.types[j] :=
    List.getElem?_eq_getElem (by omega)
  obtain ⟨u', hu', hn, hc⟩ := ElimNestedInductive.run_prefix hs hrun j _ ht hjlen
  rw [hj] at hu'
  cases Option.some.inj hu'
  exact ⟨_, List.mem_of_getElem? ht, hn, hc⟩

/-! ## §4 Two things the calculus was missing, and one docstring made honest

`SWF.checkName'` is stated for `get >>= fun e => liftM (checkName e n ap)`, but the `do`-elaborator
emits `get >>= fun e => (liftM (checkName e n ap) >>= rest)` — the same term only up to
associativity, which is *not* definitional in `Except`.  Hence `checkName_bind`.

And `mkAuxRecNameMap_spec` needs `hmain`/`hlen`, which at the call site would demand that
`AddInductive.run` positively stored an `.inductInfo` at the first member's key.  §1 makes that
unnecessary: on either failure branch the function's value **is** `default`, provably, so the spec
holds unconditionally.  `NestedRebuild.lean`'s `mkAuxRecNameMap_panic` was already stated at
`default` with the docstring "which is what the two panic branches return"; that was an assertion
about a term (`panicCore …`) that no lemma connected to `default`.  `mkAuxRecNameMap_spec'` is the
connection. -/

/-- A `panic` at *any* type is `default` — `panicCore` is an `@[extern] def` with body `default`,
not a body-less `opaque`. -/
theorem panic_eq_default {α} [Inhabited α] (m d : String) (l c : Nat) (msg : String) :
    (panicWithPosWithDecl m d l c msg : α) = default := rfl

/-- `checkName` followed by anything, at the association the `do`-elaborator produces. -/
theorem SWF.checkName_bind {n : Name} {ap : Bool}
    {f : PUnit → StateT Environment (Except Exception) β} {Q : β → Environment → Prop}
    (hf : ∀ u, SWF e₀ B (fun env => P env ∧ env.find? n = none) (f u) Q) :
    SWF e₀ B P
      ((get : StateT Environment (Except Exception) Environment) >>= fun e =>
        (liftM (Environment.checkName e n ap) : StateT Environment (Except Exception) PUnit) >>= f)
      Q := by
  intro env a env' hd hp hok
  have hx : (((get : StateT Environment (Except Exception) Environment) >>= fun e =>
      (liftM (Environment.checkName e n ap) : StateT Environment (Except Exception) PUnit) >>= f))
        env = ((Environment.checkName env n ap >>= fun u => pure (u, env))
          >>= fun p => f p.1 p.2) := rfl
  rw [hx] at hok
  cases hc : Environment.checkName env n ap with
  | error x => rw [hc] at hok; exact absurd hok nofun
  | ok u =>
    rw [hc] at hok
    exact hf u env a env' hd ⟨hp, (checkName.WF hd.wf n ap u hc).1⟩ hok

/-- **`mkAuxRecNameMap_spec` without its two hypotheses.** -/
theorem mkAuxRecNameMap_spec' (env' : Environment) (types : List InductiveType) :
    (∀ p ∈ (mkAuxRecNameMap env' types).2, ∃ j, p.2 = auxRecName types j) ∧
      (∀ n ∈ (mkAuxRecNameMap env' types).1,
        ((mkAuxRecNameMap env' types).2.lookup n).isSome) := by
  by_cases h : ∃ (mainType : InductiveType) (tail : List InductiveType) (mainInfo : InductiveVal),
      types = mainType :: tail ∧ env'.find? mainType.name = some (.inductInfo mainInfo) ∧
      mainInfo.all.length > types.length
  · obtain ⟨mt, tl, mi, rfl, h1, h2⟩ := h
    exact mkAuxRecNameMap_spec h1 h2
  · have hdef : mkAuxRecNameMap env' types = default := by
      unfold mkAuxRecNameMap
      match types with
      | [] => rfl
      | mt :: tl =>
        cases hfx : env'.find? mt.name with
        | none => simp [hfx, Id.run]
        | some ci =>
          match ci with
          | .inductInfo mi =>
            have hn : ¬ (tl.length + 1 < mi.all.length) := fun hh =>
              h ⟨mt, tl, mi, rfl, hfx, by simpa using hh⟩
            simp [hfx, hn, Id.run]
          | .axiomInfo _ | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .quotInfo _
          | .ctorInfo _ | .recInfo _ => simp [hfx, Id.run]
    rw [hdef]; exact mkAuxRecNameMap_panic

/-! ## §5 The assembly -/

set_option maxHeartbeats 1000000 in
theorem addInductive_delta_nested {env : Environment} {lparams : List Name} {np : Nat}
    {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig}
    (mapWF : env.constants.WF)
    (hne : ∀ res, (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
        { lvls := lparams.map .param, newTypes := types.toArray } = .ok res →
        res.aux2nested ≠ []) :
    (Environment.addInductive env lparams np types iu ap fuel).WF
      fun env' => DeltaCore env env' (indBudget types) := by
  unfold Environment.addInductive
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
  refine Except.WF.bind_self fun res hres => ?_
  refine Except.WF.bind_self fun env2 henv2 => ?_
  have hnn : ¬ (res.aux2nested.length = 0) :=
    fun h => hne res hres (List.length_eq_zero_iff.1 h)
  rw [if_neg hnn]
  obtain ⟨hrange, hdom⟩ := mkAuxRecNameMap_spec' env2 types
  have hmem := ElimNestedInductive.run_mem
    (s := { lvls := lparams.map .param, newTypes := types.toArray }) (by simp) hres
  -- Abstract `mkAuxRecNameMap env2 types` *before* any `split`: it contains a `match` on `types`
  -- of its own (`Add.lean`:902), and `split` picks the outermost match it finds, not the one
  -- meant.  With the pair generalised, every `split` below lands on an `env2.find?`.
  generalize hgen : mkAuxRecNameMap env2 types = M at hrange hdom ⊢
  obtain ⟨rn, rm⟩ := M
  refine Except.WF.map (Q := fun p => DeltaCore env p.2 (indBudget types)) (fun p hp => ?_)
    (fun _ hp => hp)
  refine SWF.toDelta (B := indBudget types) ?_ mapWF hp
  -- the member loop
  refine SWF.bind' (Q := fun _ _ => True) (SWF.forIn' fun indType hit b => ?_) fun _ => ?_
  · split
    next ind hfind =>
      obtain ⟨t, htmem, htn, htc⟩ := hmem indType hit
      have hf2 : env2.find? t.name = some (.inductInfo ind) := by rw [htn]; exact hfind
      refine SWF.checkName_bind fun _ => ?_
      refine SWF.bind' (Q := fun _ _ => True)
        ((SWF.addStep (B := indBudget types) ?_).weaken fun _ h => h.2) fun _ => ?_
      · exact rebuild_indWrite_budget runFreshGate mapWF henv2 htmem ⟨indType, hit, htn.symm⟩ hf2
      -- the constructor loop, then the user recursor
      refine SWF.bind' (Q := fun _ _ => True) (SWF.forIn' fun cn hcn b => ?_) fun _ => ?_
      · split
        next cv hcv =>
          refine SWF.checkName_bind fun _ => ?_
          refine SWF.bind' (Q := fun _ _ => True)
            ((SWF.addStep (B := indBudget types) ?_).weaken fun _ h => h.2) fun _ =>
              SWF.pure' fun _ _ => trivial
          exact rebuild_ctorWrite_budget runFreshGate mapWF henv2 htmem ⟨indType, hit, htc⟩
            hf2 hcn hcv
        next =>
          exact SWF.bind' (Q := fun _ _ => True)
            (SWF.panic_weak (Q := fun _ _ => True) fun _ _ => trivial)
            fun _ => SWF.pure' fun _ _ => trivial
      refine SWF.bind' (Q := fun _ _ => True) ?_ fun _ => SWF.pure' fun _ _ => trivial
      dsimp only
      split
      next recInfo hrf =>
        refine SWF.bind' (Q := fun _ _ => True)
          (SWF.mapM' fun rule _ => SWF.pure' fun _ h => h) fun newRules => ?_
        refine SWF.checkName_bind fun _ => ?_
        refine (SWF.addStep (B := indBudget types) ?_).weaken fun _ h => h.2
        exact rebuild_recWrite_budget_user hrange hit
      next => exact SWF.panic_weak (Q := fun _ _ => True) fun _ _ => trivial
    next =>
      exact SWF.bind' (Q := fun _ _ => True)
        (SWF.panic_weak (Q := fun _ _ => True) fun _ _ => trivial)
        fun _ => SWF.pure' fun _ _ => trivial
  -- the auxiliary recursors
  refine SWF.bind' (Q := fun _ _ => True) (SWF.forM' fun recName hrn => ?_) fun _ => ?_
  · split
    next recInfo hrf =>
      refine SWF.bind' (Q := fun _ _ => True)
        (SWF.mapM' fun rule _ => SWF.pure' fun _ h => h) fun newRules => ?_
      refine SWF.checkName_bind fun _ => ?_
      refine (SWF.addStep (B := indBudget types) ?_).weaken fun _ h => h.2
      exact indBudget_processRec hrange (.inl (hdom recName hrn))
    next => exact SWF.panic_weak (Q := fun _ _ => True) fun _ _ => trivial
  -- the tail: three `TypeChecker.M.run` passes and two accumulator loops, no `add`
  refine SWF.bind' (Q := fun _ _ => True) (SWF.get'.mono fun _ _ _ => trivial) fun _ => ?_
  refine SWF.bind' (Q := fun _ _ => True) (SWF.liftTriv.mono fun _ _ _ => trivial) fun _ => ?_
  refine SWF.bind' (Q := fun _ _ => True) (SWF.get'.mono fun _ _ _ => trivial) fun final => ?_
  refine SWF.bind' (Q := fun _ _ => True)
    ((SWF.forIn' fun _ _ _ => SWF.pure' fun _ h => h).mono fun _ _ _ => trivial) fun s1 => ?_
  refine SWF.bind' (Q := fun _ _ => True)
    ((SWF.forIn' fun _ _ _ => SWF.pure' fun _ h => h).mono fun _ _ _ => trivial) fun s2 => ?_
  refine SWF.bind' (Q := fun _ _ => True) (SWF.liftTriv.mono fun _ _ _ => trivial) fun _ => ?_
  refine SWF.bind' (Q := fun _ _ => True) ?_ fun _ => SWF.pure' fun _ _ => trivial
  rw [← Array.forIn_toList]
  refine SWF.forIn' fun recName _ b => ?_
  split
  next recInfo hrf =>
    exact SWF.bind' (Q := fun _ _ => True) (SWF.liftTriv.mono fun _ _ _ => trivial)
      fun _ => SWF.pure' fun _ h => h
  next =>
    exact SWF.bind' (Q := fun _ _ => True)
      (SWF.panic_weak (Q := fun _ _ => True) fun _ _ => trivial)
      fun _ => SWF.pure' fun _ h => h

/-! ## §6 `InductiveMapGate`, discharged — and its four consumers, unconditional

`InductMap.lean`'s `inductiveMapGate_of` restates `NoNestedAll.lean`'s `InductiveMapGate` verbatim
(deliberately: it is where `DeltaCore` meets the gate's `constants.find?` phrasing).  §5 supplies its
only remaining hypothesis, so the gate is a **closed term**.

`NoNestedAll.lean` is not on this file's import path *from* the other side — nothing there imports
`InductMap.lean` — so the four theorems that take `Gi : InductiveMapGate` cannot be restated there
without an edit to a file this stream does not own.  What is provided instead is the closed gate plus
an unconditional corollary of each consumer, named with a prime.  Whoever owns `NoNestedAll.lean` can
delete the `Gi` binders and use `inductiveMapGate`; until then the primed names are the
unconditional forms, and the unprimed ones are unchanged. -/

/-- **The residual, discharged.**  `GB` supplied by §5. -/
theorem inductiveMapGate : InductiveMapGate :=
  inductiveMapGate_of fun mapWF h hne => addInductive_delta_nested mapWF hne _ h

theorem addInductive_noNestedEnv' {env env' : Environment}
    {lparams : List Name} {np : Nat} {types : List InductiveType} {iu ap : Bool}
    {fuel : FuelConfig} (hC : NoNestedEnv env)
    (h : Environment.addInductive env lparams np types iu ap fuel = .ok env') :
    NoNestedEnv env' := addInductive_noNestedEnv inductiveMapGate hC h

theorem addDecl_noNestedEnv' {env env' : Environment} {d : Declaration} {fuel : FuelConfig}
    (hC : NoNestedEnv env) (h : Lean4Lean.addDecl env d true fuel = .ok env') :
    NoNestedEnv env' := addDecl_noNestedEnv inductiveMapGate hC h

/-- **The headline, unconditional.** -/
theorem VEnv.NoNestedN.of_addDecl' {env env' : Environment} {d : Declaration} {fuel : FuelConfig}
    {safety : DefinitionSafety} {venv : VEnv} (hC : NoNestedEnv env)
    (h : Lean4Lean.addDecl env d true fuel = .ok env') (H : TrEnv safety env' venv) :
    venv.NoNestedN := VEnv.NoNestedN.of_addDecl inductiveMapGate hC h H

theorem addDecls_noNestedEnv' {fuel : FuelConfig} {ds : List Declaration}
    {env env' : Environment} (hC : NoNestedEnv env)
    (h : ds.foldlM (fun e d => Lean4Lean.addDecl e d true fuel) env = .ok env') :
    NoNestedEnv env' := addDecls_noNestedEnv inductiveMapGate hC h

/-! ## §7 The axiom trail -/

#print axioms Lean4Lean.SWF.panic'
#print axioms Lean4Lean.SWF.forIn'
#print axioms Lean4Lean.SWF.mapM'
#print axioms Lean4Lean.SWF.checkName_bind
#print axioms Lean4Lean.mkAuxRecNameMap_spec'
#print axioms Lean4Lean.ElimNestedInductive.run_mem
#print axioms Lean4Lean.addInductive_delta_nested
#print axioms Lean4Lean.inductiveMapGate
#print axioms Lean4Lean.VEnv.NoNestedN.of_addDecl'
#print axioms Lean4Lean.addDecls_noNestedEnv'

end Lean4Lean
