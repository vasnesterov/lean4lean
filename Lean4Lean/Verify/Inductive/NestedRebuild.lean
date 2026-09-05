import Lean4Lean.Verify.Inductive.NIndices

/-!
# Residual B: the nested rebuild branch of `Environment.addInductive`

`Verify/Inductive/InductMap.lean` reduced `InductiveMapGate` to **one** hypothesis, the `GB` of
`addInductive_mapDelta` / `inductiveMapGate_of`: on inputs where `ElimNestedInductive.run` reports
`res.aux2nested ≠ []`, `Environment.addInductive`'s delta stays inside `indBudget types`.  This file
attacks it.

## §0 The first thing that had to be checked, and was not

`docs/handoff-inductmap.md` §5 gap 4 says it in the previous round's own words: *"I did not check
whether residual B is **satisfiable** at a real nested block."*  §1 below is that check, as a
build-time guard rather than a claim: `Environment.addInductive` is run on

```
inductive NTreeX | node : List NTreeX → NTreeX
```

from the running kernel environment, and the `#eval` **throws** unless (a) `ElimNestedInductive.run`
reports `aux2nested.length = 1`, so residual B's third hypothesis holds, (b) `addInductive`
**accepts**, so its second hypothesis holds, and (c) the names the accepted run adds are exactly the
four `indDeclNamesN [ntreeIndType] 1` allows.  So residual B is not vacuous, and the ~400 lines
behind it are not wasted.

`Verify/Inductive/NestedRestoreWit.lean` §1.1's `NFn` witness cannot be used for this: `NFn` is
already declared in the environment that witness runs in, so `addInductive`'s `checkName` rejects it.
That witness exercises `ElimNestedInductive.run`, which performs no name check; this one exercises the
whole function, rebuild and both re-check passes included.

## §1.1 A measured correction to `handoff-inductmap.md` §3.2

That doc grades sub-obligation 4 — `stats.nindices.size = its.size` — as machinery needed to *use*
`DeclareStages.lean`'s positive clause, and closes "nothing in it looks false".  Measured, it is
stronger than that: **it is the only barrier between residual B and outright falsity.**  The gate
quantifies over every `env` with `env.constants.WF`, and `SMap.WF` does not forbid a **mis-keyed**
entry (`InductMap.lean` §1, second design point).  An `env` holding `.inductInfo ind` under key
`types[0].name` with `ind.name` outside every `indDeclNamesN types k` would be inherited by `env'`,
would pass the rebuild's `checkName ind.name` (nothing holds that key), and the rebuild would then
`add` at `ind.name` — refuting `DeltaCore.keyed`.  The *only* thing rejecting such an `env` is
`checkName info.name` inside `declareInductiveTypes` (`Inductive/Add.lean`:298), which fires at index
`j` only if `Array.zipWith indTypes stats.nindices` (`:289`) reaches `j`.  §4 below names that
barrier as a `Prop` and proves the member half of the rebuild's budget from it.

## §2 What is proved here

* §1 the satisfiability guard.
* §2 the auxiliary-recursor budget, and the **gap** in `handoff-inductmap.md` §3.2's claim that the
  last two `add` sites are "budgeted by inspection": `processRec` is also run over `recNames'`, whose
  elements are `mkRecName` of the *auxiliary* members — `_nested.….rec`, outside `indDeclNamesN` for
  every `k`.  Their budget-safety is a **loop invariant** of `mkAuxRecNameMap`, not an inspection.
* §3 the `StateT Environment (Except Exception)` delta calculus (§3.2's sub-obligation 5).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-! ## §1 Residual B is satisfiable: `inductive NTreeX | node : List NTreeX → NTreeX`

A genuinely nested block whose names are **fresh** in the running environment, which is what lets
`addInductive`'s `checkName` be reached rather than short-circuited. -/

/-- `inductive NTreeX | node : List NTreeX → NTreeX`, spelled as the kernel sees it. -/
def ntreeIndType : InductiveType :=
  { name := `NTreeX, type := .sort (.succ .zero),
    ctors := [{ name := `NTreeX.node,
                type := .forallE `a (.app (.const `List [.zero]) (.const `NTreeX []))
                          (.const `NTreeX []) .default }] }

/-- The four names residual B must let through, and no more. -/
example : indDeclNamesN [ntreeIndType] 1
    = [`NTreeX, `NTreeX.node, `NTreeX.rec, `NTreeX.rec_1] := rfl

/-- **The negative control**: the renamed auxiliary recursor is outside the `k = 0` budget, so the
`∃ k` in the gate is doing work at this input. -/
example : (`NTreeX.rec_1 : Name) ∉ indDeclNamesN [ntreeIndType] 0 := by decide

#eval show Lean.CoreM Unit from do
  let kenv := (← getEnv).toKernelEnv
  let st : ElimNestedInductive.State := { lvls := [], newTypes := #[ntreeIndType] }
  let .ok res := (ElimNestedInductive.run 1000 0 [ntreeIndType] kenv).run' st
    | throwError "NestedRebuild/§1: ElimNestedInductive.run REJECTS the nested NTreeX block -- \
        residual B's third hypothesis cannot be exhibited here"
  unless res.aux2nested.length = 1 do
    throwError "NestedRebuild/§1: aux2nested.length = {res.aux2nested.length}, expected 1 -- \
      the block is no longer nested, so this is not a witness for residual B"
  let .ok env' := Lean4Lean.Environment.addInductive kenv [] 0 [ntreeIndType] false false
    | throwError "NestedRebuild/§1: Environment.addInductive REJECTS the nested NTreeX block -- \
        residual B is VACUOUS at this input and the round's premise is gone"
  let added := env'.constants.toList.map (·.1) |>.filter fun n => (kenv.find? n).isNone
  let budget := indDeclNamesN [ntreeIndType] 1
  let extra := added.filter fun n => !budget.contains n
  unless extra.isEmpty do
    throwError "NestedRebuild/§1: the nested rebuild wrote {extra.length} names outside \
      indDeclNamesN [ntreeIndType] 1 -- residual B is FALSE at this input: {extra}"
  let missing := budget.filter fun n => !added.contains n
  unless missing.isEmpty do
    throwError "NestedRebuild/§1: the accepted nested run stored none of {missing} -- the witness \
      does not exercise the renamed auxiliary recursor, which is the whole point of the branch"
  Lean.logInfo m!"NestedRebuild/§1: `inductive NTreeX | node : List NTreeX → NTreeX` is ACCEPTED, \
    aux2nested = {res.aux2nested.map (·.1)} (numNested = 1 ≠ 0), and the {added.length} names it \
    adds are exactly indDeclNamesN [ntreeIndType] 1 -- residual B is SATISFIABLE and its \
    conclusion is non-trivial ✓"

/-! ## §2 The auxiliary-recursor budget

`mkAuxRecNameMap` (`Inductive/Add.lean`:901) returns `(oldRecNames, recMap)`; `processRec` is run
once per user member on `mkRecName indType.name`, and once per element of `oldRecNames`, and in each
case writes at `(recMap.lookup recName).getD recName`.  Three facts are needed and they are not the
same fact:

* `mkRecName indType.name` is in the budget outright (`indDeclNames`' third component);
* every **value** `recMap` carries is an `auxRecName`, hence in the budget at a large enough `k`;
* every **key** in `oldRecNames` is found by `recMap.lookup` — because a *miss* falls back to
  `recName` itself, which for an element of `oldRecNames` is `mkRecName` of an *auxiliary* member,
  i.e. `_nested.….rec`, outside `indDeclNamesN types k` for every `k`.

The third is the one `handoff-inductmap.md` §3.2 calls "by inspection". It is not: it is the
statement that the two outputs of a loop with two accumulators stay in step. -/

theorem auxRecName_mem_indDeclNamesN {types : List InductiveType} {j k : Nat} (h : j < k) :
    auxRecName types j ∈ indDeclNamesN types k := by
  refine List.mem_append_right _ (List.mem_map.2 ⟨j, ?_, rfl⟩)
  exact List.mem_range.2 h

theorem indBudget_auxRecName (types : List InductiveType) (j : Nat) :
    indBudget types (auxRecName types j) :=
  ⟨j + 1, auxRecName_mem_indDeclNamesN (Nat.lt_succ_self j)⟩

theorem indBudget_mkRecName {types : List InductiveType} {t : InductiveType} (ht : t ∈ types) :
    indBudget types (Lean.mkRecName t.name) :=
  indBudget_of_runBudget (.inr (.inr ⟨t, ht, rfl⟩))

theorem indBudget_name {types : List InductiveType} {t : InductiveType} (ht : t ∈ types) :
    indBudget types t.name :=
  indBudget_of_runBudget (.inl ⟨t, ht, rfl⟩)

theorem indBudget_ctorName {types : List InductiveType} {t : InductiveType} (ht : t ∈ types)
    {ct : Constructor} (hct : ct ∈ t.ctors) : indBudget types ct.name :=
  indBudget_of_runBudget (.inr (.inl ⟨t, ht, ct, hct, rfl⟩))

/-! ## §3 The `StateT Environment (Except Exception)` delta calculus

`handoff-inductmap.md` §3.2's sub-obligation 5.  The nested rebuild is a
`StateT Environment (Except Exception)` block (`Inductive/Add.lean`:1156), so §1's `DeltaCore`
needs a Hoare calculus in that monad.  Two design points:

* **The budget is fixed and the start environment is fixed**, so the loop invariant is the *constant*
  `DeltaCore e₀ · B` and `DeltaCore.trans` never has to be invoked inside a loop body — the
  bind rule carries the same proposition through.  That is the whole reason the calculus is short.
* **A precondition on the state is a parameter.**  Every `add` in the rebuild is preceded by a
  `checkName` against the *same* state, and `DeltaCore.add_of` needs that freshness; a delta-only
  predicate cannot express it, because its state is universally quantified.  So `SWF` carries
  `P : Environment → Prop`, and `checkName'` is what moves freshness from the check to the `add`. -/

/-- **The delta Hoare triple in `StateT Environment (Except Exception)`.**  `e₀` is the rebuild's
start environment (the *original* `env`, which is what `StateT.run (s := env)` restores), `B` the
fixed budget, `P`/`Q` pre- and postconditions on the threaded environment. -/
def SWF (e₀ : Environment) (B : Name → Prop) (P : Environment → Prop)
    (x : StateT Environment (Except Exception) α) (Q : α → Environment → Prop) : Prop :=
  ∀ env a env', DeltaCore e₀ env B → P env → x env = .ok (a, env') →
    DeltaCore e₀ env' B ∧ Q a env'

variable {α β : Type} {e₀ : Environment} {B : Name → Prop} {P : Environment → Prop}

theorem SWF.mono {x : StateT Environment (Except Exception) α} {Q Q' : α → Environment → Prop}
    (h : SWF e₀ B P x Q) (hQ : ∀ a env, Q a env → Q' a env) : SWF e₀ B P x Q' :=
  fun env a env' hd hp hok => ((h env a env' hd hp hok).imp id (hQ a env'))

theorem SWF.weaken {x : StateT Environment (Except Exception) α} {Q : α → Environment → Prop}
    {P' : Environment → Prop} (h : SWF e₀ B P x Q) (hP : ∀ env, P' env → P env) :
    SWF e₀ B P' x Q :=
  fun env a env' hd hp hok => h env a env' hd (hP env hp) hok

theorem SWF.pure' {a : α} {Q : α → Environment → Prop} (h : ∀ env, P env → Q a env) :
    SWF e₀ B P (pure a) Q := by
  intro env b env' hd hp hok
  cases hok
  exact ⟨hd, h env hp⟩

theorem SWF.bind' {x : StateT Environment (Except Exception) α}
    {f : α → StateT Environment (Except Exception) β}
    {Q : α → Environment → Prop} {R : β → Environment → Prop}
    (hx : SWF e₀ B P x Q) (hf : ∀ a, SWF e₀ B (Q a) (f a) R) :
    SWF e₀ B P (x >>= f) R := by
  intro env b env' hd hp hok
  rw [show (x >>= f) env = (x env >>= fun p => f p.1 p.2) from rfl] at hok
  cases hx' : x env with
  | error e => rw [hx'] at hok; exact absurd hok nofun
  | ok p =>
    obtain ⟨a, env₁⟩ := p
    obtain ⟨hd₁, hq⟩ := hx env a env₁ hd hp hx'
    rw [hx'] at hok
    exact hf a env₁ b env' hd₁ hq hok

/-- Reading the state exposes it to the postcondition — which is how `checkName`'s argument and the
`add`'s `ConstantInfo` come to be about the *same* environment. -/
theorem SWF.get' : SWF e₀ B P (get : StateT Environment (Except Exception) Environment)
    (fun a env => a = env ∧ P env) := by
  intro env a env' hd hp hok
  cases hok
  exact ⟨hd, rfl, hp⟩

/-- Lifting an `Except`: the state is untouched, so the delta is unchanged. -/
theorem SWF.lift' {y : Except Exception α} {Q : α → Environment → Prop}
    (h : ∀ a, y = .ok a → ∀ env, P env → Q a env) :
    SWF e₀ B P (liftM y : StateT Environment (Except Exception) α) Q := by
  intro env a env' hd hp hok
  have hx : (liftM y : StateT Environment (Except Exception) α) env
      = (y >>= fun b => pure (b, env)) := rfl
  rw [hx] at hok
  cases hy : y with
  | error e => rw [hy] at hok; exact absurd hok nofun
  | ok b =>
    rw [hy] at hok
    obtain ⟨rfl, rfl⟩ : b = a ∧ env = env' := by
      have h2 := Except.ok.inj hok
      exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
    exact ⟨hd, h b hy env hp⟩

/-- **`checkName`, in the state monad.**  `env.constants.WF` is *not* a hypothesis: the delta
supplies it (`DeltaCore.wf` at `e₀ → env`), which is `InductMap.lean` §1's freshness-free `add`
paying off a second time. -/
theorem SWF.checkName' (n : Name) (ap : Bool) :
    SWF e₀ B P
      ((get : StateT Environment (Except Exception) Environment) >>= fun e =>
        (liftM (Environment.checkName e n ap) : StateT Environment (Except Exception) Unit))
      (fun _ env => P env ∧ env.find? n = none) := by
  intro env a env' hd hp hok
  have hx : ((get : StateT Environment (Except Exception) Environment) >>= fun e =>
      (liftM (Environment.checkName e n ap) : StateT Environment (Except Exception) Unit)) env
      = (Environment.checkName env n ap >>= fun u => pure (u, env)) := rfl
  rw [hx] at hok
  cases hc : Environment.checkName env n ap with
  | error x => rw [hc] at hok; exact absurd hok nofun
  | ok u =>
    rw [hc] at hok
    obtain ⟨rfl, rfl⟩ : u = a ∧ env = env' := by
      have h2 := Except.ok.inj hok
      exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
    exact ⟨hd, hp, (checkName.WF hd.wf n ap u hc).1⟩

/-- **The `add` step.**  Its precondition is exactly what `checkName'` leaves behind. -/
theorem SWF.addStep {ci : ConstantInfo} (hB : B ci.name) :
    SWF e₀ B (fun env => env.find? ci.name = none)
      (modify (·.add ci) : StateT Environment (Except Exception) PUnit)
      (fun _ _ => True) := by
  intro env a env' hd hp hok
  cases hok
  exact ⟨hd.add_of hB hp, trivial⟩

/-- The loop rule: a body that preserves the delta and asks nothing of the state. -/
theorem SWF.forM' {l : List α} {f : α → StateT Environment (Except Exception) PUnit}
    (h : ∀ a ∈ l, SWF e₀ B (fun _ => True) (f a) (fun _ _ => True)) :
    SWF e₀ B (fun _ => True) (l.forM f) (fun _ _ => True) := by
  induction l with
  | nil => exact SWF.pure' fun _ _ => trivial
  | cons a l ih =>
    refine SWF.bind' (Q := fun _ _ => True) (h a (.head _)) fun _ => ?_
    exact (ih fun b hb => h b (.tail _ hb)).weaken fun _ _ => trivial



/-! ## §4 `mkAuxRecNameMap`'s loop invariant — the gap in "budgeted by inspection"

`handoff-inductmap.md` §3.2 item 2 says the last two `add` sites of the rebuild are "budgeted by
inspection".  Half of that is true: `mkAuxRecNameMap` writes `appendIndexAfter' (mkRecName mainName)`
at indices `1, 2, …`, and `auxRecName types k` is `appendIndexAfter' (mkRecName (types.headD default).name) (k+1)`,
so every **value** of the map is in the budget.  The other half is not an inspection.  `processRec`
is run on every element of `recNames'`, and those are `mkRecName` of the **auxiliary** members —
`_nested.….rec`, outside `indDeclNamesN types k` for every `k`.  A `lookup` *miss* there writes that
name verbatim and refutes the gate.  So what is owed is that the two accumulators stay in step:
every key `oldRecNames` collects is a key `recMap` carries.  That is §4. -/

/-- `mkAuxRecNameMap`'s loop, as a plain fold: `(oldRecNames, recMap, nextIdx)`. -/
def auxRecFold (mainName : Name) :
    List Name → Array Name × List (Name × Name) × Nat → Array Name × List (Name × Name) × Nat
  | [], s => s
  | indName :: l, s =>
    auxRecFold mainName l
      (s.1.push (Lean.mkRecName indName),
        (Lean.mkRecName indName, appendIndexAfter' (Lean.mkRecName mainName) s.2.2) :: s.2.1,
        s.2.2 + 1)

/-- The `for` loop **is** that fold.  (`Id.run do` with two `mut`s elaborates to `forIn` at the
product of the accumulators; `handoff-inductmap.md` §5 gap 3 records that `split` cannot see through
the join points the `do`-elaborator emits, so the loop is converted rather than split.) -/
theorem forIn_auxRecFold (mainName : Name) :
    ∀ (l : List Name) (s : Array Name × List (Name × Name) × Nat),
      (forIn (m := Id) l s (fun indName s =>
          ForInStep.yield (s.1.push (Lean.mkRecName indName),
            (Lean.mkRecName indName, appendIndexAfter' (Lean.mkRecName mainName) s.2.2) :: s.2.1,
            s.2.2 + 1)))
        = auxRecFold mainName l s
  | [], s => rfl
  | a :: l, s => by
    rw [List.forIn_cons]
    exact forIn_auxRecFold mainName l _

/-- **The invariant, all three clauses.**  `range` is the budget half, `dom` is the half that is not
an inspection, and `idx` is what keeps `range`'s witness available at the next step. -/
theorem auxRecFold_inv (mainName : Name) :
    ∀ (l : List Name) (s : Array Name × List (Name × Name) × Nat),
      (∀ p ∈ s.2.1, ∃ i, p.2 = appendIndexAfter' (Lean.mkRecName mainName) (i + 1)) →
      (∀ n ∈ s.1, ((s.2.1).lookup n).isSome) → 1 ≤ s.2.2 →
      (∀ p ∈ (auxRecFold mainName l s).2.1,
          ∃ i, p.2 = appendIndexAfter' (Lean.mkRecName mainName) (i + 1)) ∧
        (∀ n ∈ (auxRecFold mainName l s).1, (((auxRecFold mainName l s).2.1).lookup n).isSome) ∧
        1 ≤ (auxRecFold mainName l s).2.2
  | [], s, hr, hd, hi => ⟨hr, hd, hi⟩
  | a :: l, s, hr, hd, hi => by
    rw [auxRecFold]
    refine auxRecFold_inv mainName l _ ?_ ?_ (by simp)
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨s.2.2 - 1, ?_⟩
        show appendIndexAfter' (Lean.mkRecName mainName) s.2.2 = _
        congr 1; omega
      · exact hr p hp
    · intro n hn
      by_cases he : Lean.mkRecName a = n
      · subst he; simp
      · have hn' : n ∈ s.1 := by
          rcases Array.mem_push.1 hn with h | h
          · exact h
          · exact absurd h.symm he
        have hne : (n == Lean.mkRecName a) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun h => he h.symm
        rw [List.lookup_cons, hne]
        exact hd n hn'

/-- **The two facts residual B needs about `mkAuxRecNameMap`**, at the branch where it does not
panic.  `hmain` is what `Add.lean`:906's `unreachable!` demands and `hlen` what `:908`'s `assert!`
demands; on either failure branch the function returns `default = (∅, [])`, for which both
conclusions hold trivially (`mkAuxRecNameMap_panic` below). -/
theorem mkAuxRecNameMap_spec {env' : Environment} {mainType : InductiveType}
    {tail : List InductiveType} {mainInfo : InductiveVal}
    (hmain : env'.find? mainType.name = some (.inductInfo mainInfo))
    (hlen : mainInfo.all.length > (mainType :: tail).length) :
    (∀ p ∈ (mkAuxRecNameMap env' (mainType :: tail)).2,
        ∃ j, p.2 = auxRecName (mainType :: tail) j) ∧
      (∀ n ∈ (mkAuxRecNameMap env' (mainType :: tail)).1,
        ((mkAuxRecNameMap env' (mainType :: tail)).2.lookup n).isSome) := by
  have he : mkAuxRecNameMap env' (mainType :: tail)
      = (((auxRecFold mainType.name (mainInfo.all.drop (mainType :: tail).length)
            (#[], [], 1)).1).toList,
         (auxRecFold mainType.name (mainInfo.all.drop (mainType :: tail).length) (#[], [], 1)).2.1) := by
    unfold mkAuxRecNameMap
    simp only [Id.run, bind, pure, hmain, hlen, if_true, forIn_auxRecFold]
  obtain ⟨hr, hd, -⟩ := auxRecFold_inv mainType.name
    (mainInfo.all.drop (mainType :: tail).length) (#[], [], 1) nofun nofun (by simp)
  rw [he]
  exact ⟨fun p hp => (hr p hp).imp fun _ h => h, fun n hn => hd n (by simpa using hn)⟩

/-- Both conclusions of `mkAuxRecNameMap_spec` at `default`, which is what the two panic branches
return — so the spec needs no side condition at the call site.

*Correction, 2026-09-05.*  "Which is what the two panic branches return" was an assertion relating two
**different terms**: a panic branch returns `panicCore …`, and no lemma here connected that to
`default`.  It is now a theorem — `Lean4Lean.panic_eq_default` in `Verify/Inductive/RebuildFinish.lean`,
by `rfl`, because `panicCore` is an `@[extern] def` with body `default` rather than a body-less
`opaque`.  With it, `mkAuxRecNameMap_spec`'s two hypotheses are not merely dischargeable at the call
site but **unnecessary**: `Lean4Lean.mkAuxRecNameMap_spec'` (arity 2) is the unconditional form, and it
is what the block assembly uses. -/
theorem mkAuxRecNameMap_panic {types : List InductiveType} :
    (∀ p ∈ (default : List Name × List (Name × Name)).2, ∃ j, p.2 = auxRecName types j) ∧
      (∀ n ∈ (default : List Name × List (Name × Name)).1,
        ((default : List Name × List (Name × Name)).2.lookup n).isSome) :=
  ⟨nofun, nofun⟩

/-- **The budget for a `processRec` write.**  `processRec recName` writes at
`(recNameMap'.lookup recName).getD recName`; this says that name is in `indBudget types` whenever the
map's values are `auxRecName`s and the fallback name is itself budgeted.  Both `processRec` call
sites supply the second premise: `mkRecName indType.name` by `indBudget_mkRecName`, and an element of
`recNames'` by `mkAuxRecNameMap_spec`'s `dom` clause, which makes the fallback unreachable. -/
theorem indBudget_processRec {types : List InductiveType} {recMap : List (Name × Name)}
    {recName : Name} (hr : ∀ p ∈ recMap, ∃ j, p.2 = auxRecName types j)
    (hfb : (recMap.lookup recName).isSome ∨ indBudget types recName) :
    indBudget types ((recMap.lookup recName).getD recName) := by
  cases hl : recMap.lookup recName with
  | none =>
    rcases hfb with h | h
    · rw [hl] at h; exact absurd h (by simp)
    · simpa [hl] using h
  | some m =>
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 hl
    obtain ⟨j, rfl⟩ := hr (recName, m) (List.mem_append_right _ (.head _))
    simpa using indBudget_auxRecName types j

/-! ## §5 The freshness barrier, named, and the reduction it buys

§1.1 measured that residual B is **false** without member-name freshness in the input environment,
so the barrier deserves a name rather than a footnote.  `RunFreshGate` is that name; its three fields
are graded, and they are *not* equally hard:

* `member` — the one that needs `stats.nindices.size = indTypes.size`
  (`handoff-inductmap.md` §3.2 item 4, `Inductive/Add.lean`:254's own `assert!`), because
  `AddInductive.M.WF.declareInductiveTypes`' freshness clause is guarded by `stats.nindices[j]?`.
  **This is the falsity barrier.**
* `ctor` — needs nothing of the kind: `r113e_ctorOuter_WF`'s freshness clause is
  `∀ t ∈ ts, ∀ ctor ∈ t.ctors, env.find? ctor.name = none`, quantified over the member list
  **directly**.  `handoff-inductmap.md` §3.2 item 3 treats the two halves as one obligation; measured,
  they are not.
* `ctors` — the `.ctors` field of the stored `InductiveVal`, which `r113eIndVal` pins to
  `indType.ctors.map (·.name)`; same zip guard as `member`.

What is proved below is the **reduction**: given the gate, every name the nested rebuild's four `add`
sites write is in `indBudget types`.  That is residual B minus the monadic plumbing (§3's calculus
applied to the actual `do`-block, plus `run_prefix` to move from `res.types` to `types`).

*Update, 2026-09-05.*  That plumbing is done, in `Verify/Inductive/RebuildFinish.lean`: `run_prefix`
becomes `ElimNestedInductive.run_mem`, §3's calculus gains seven rules it lacked (a `forIn` rule, a
`mapM` rule, a `panic` rule, and — the one that mattered — `SWF.checkName_bind`, because `checkName'`
is stated at an association the `do`-elaborator does not produce and `Except`'s bind is not
associative definitionally), and residual B lands as `addInductive_delta_nested`. -/

/-- **The barrier.**  Everything residual B needs from `AddInductive.run` beyond `WF_run`. -/
structure RunFreshGate : Prop where
  /-- the block's member names were absent from the input environment -/
  member : ∀ {c : AddInductive.Context} {np nn : Nat} {its : List InductiveType}
    {env' : Environment}, c.env.constants.WF → AddInductive.run np its nn c = .ok env' →
    ∀ t ∈ its, c.env.find? t.name = none
  /-- and so were its constructor names -/
  ctor : ∀ {c : AddInductive.Context} {np nn : Nat} {its : List InductiveType}
    {env' : Environment}, c.env.constants.WF → AddInductive.run np its nn c = .ok env' →
    ∀ t ∈ its, ∀ ct ∈ t.ctors, c.env.find? ct.name = none
  /-- the stored `InductiveVal` lists exactly the member's own constructors -/
  ctors : ∀ {c : AddInductive.Context} {np nn : Nat} {its : List InductiveType}
    {env' : Environment}, c.env.constants.WF → AddInductive.run np its nn c = .ok env' →
    ∀ t ∈ its, ∀ ind, env'.find? t.name = some (.inductInfo ind) →
      ind.ctors = t.ctors.map (·.name)

section
variable (G : RunFreshGate) {c : AddInductive.Context} {np nn : Nat} {its : List InductiveType}
  {env' : Environment} (mapWF : c.env.constants.WF)
  (hrun : AddInductive.run np its nn c = .ok env')

include G mapWF hrun

/-- **The mis-keying hole, closed.**  Without `G.member` this is exactly the step that fails, and
§1.1's counterexample is what fails through it. -/
theorem inductInfo_name_eq {t : InductiveType} (ht : t ∈ its) {ind : InductiveVal}
    (hf : env'.find? t.name = some (.inductInfo ind)) : ind.name = t.name := by
  rcases (AddInductive.WF_run mapWF np its nn env' hrun).keyed _ _ hf with h | ⟨-, h⟩
  · rw [G.member mapWF hrun t ht] at h; exact absurd h nofun
  · exact h

/-- Same step at a constructor read back out of `env'`. -/
theorem ctorInfo_name_eq {t : InductiveType} (ht : t ∈ its) {ct : Constructor} (hct : ct ∈ t.ctors)
    {cv : ConstructorVal} (hf : env'.find? ct.name = some (.ctorInfo cv)) : cv.name = ct.name := by
  rcases (AddInductive.WF_run mapWF np its nn env' hrun).keyed _ _ hf with h | ⟨-, h⟩
  · rw [G.ctor mapWF hrun t ht ct hct] at h; exact absurd h nofun
  · exact h

/-- **Write site 1** (`Inductive/Add.lean`:1172): the `.inductInfo` the rebuild re-adds is keyed by a
member name of the block. -/
theorem rebuild_indWrite_budget {types : List InductiveType} {t : InductiveType} (ht : t ∈ its)
    (htt : ∃ u ∈ types, u.name = t.name) {ind : InductiveVal}
    (hf : env'.find? t.name = some (.inductInfo ind)) :
    indBudget types ({ ind with all := types.map (·.name) } : InductiveVal).name := by
  obtain ⟨u, hu, hun⟩ := htt
  show indBudget types ind.name
  rw [inductInfo_name_eq G mapWF hrun ht hf, ← hun]
  exact indBudget_name hu

/-- **Write site 2** (`:1177`): each `.ctorInfo` is keyed by a constructor name of the block.  The
`ctors` field of the stored `InductiveVal` is what turns "some name in `ind.ctors`" into "a
constructor name of `t`", which is why `G.ctors` is a field of the gate and not a convenience. -/
theorem rebuild_ctorWrite_budget {types : List InductiveType} {t : InductiveType} (ht : t ∈ its)
    (htt : ∃ u ∈ types, t.ctors.map (·.name) = u.ctors.map (·.name)) {ind : InductiveVal}
    (hf : env'.find? t.name = some (.inductInfo ind)) {cn : Name} (hcn : cn ∈ ind.ctors)
    {cv : ConstructorVal} (hcv : env'.find? cn = some (.ctorInfo cv)) {ty : Expr} :
    indBudget types ({ cv with type := ty } : ConstructorVal).name := by
  rw [G.ctors mapWF hrun t ht ind hf] at hcn
  obtain ⟨ct, hct, rfl⟩ := List.mem_map.1 hcn
  obtain ⟨u, hu, hmap⟩ := htt
  have : ct.name ∈ u.ctors.map (·.name) := hmap ▸ List.mem_map_of_mem hct
  obtain ⟨ct', hct', he⟩ := List.mem_map.1 this
  show indBudget types cv.name
  rw [ctorInfo_name_eq G mapWF hrun ht hct hcv, ← he]
  exact indBudget_ctorName hu hct'

end

/-! ### §5.1 Write sites 3 and 4, which need no gate

`processRec` is the only writer of the remaining two, and §4 already budgets it.  Both call sites are
covered by one lemma: the `mkRecName indType.name` call by `indBudget_mkRecName`, and the
`recNames'.forM processRec` call by `mkAuxRecNameMap_spec`'s `dom` clause. -/

theorem rebuild_recWrite_budget_user {types : List InductiveType} {recMap : List (Name × Name)}
    (hr : ∀ p ∈ recMap, ∃ j, p.2 = auxRecName types j) {t : InductiveType} (ht : t ∈ types) :
    indBudget types ((recMap.lookup (Lean.mkRecName t.name)).getD (Lean.mkRecName t.name)) :=
  indBudget_processRec hr (.inr (indBudget_mkRecName ht))

theorem rebuild_recWrite_budget_aux {types : List InductiveType} {env'' : Environment}
    {mainType : InductiveType} {tail : List InductiveType} {mainInfo : InductiveVal}
    (hmain : env''.find? mainType.name = some (.inductInfo mainInfo))
    (hlen : mainInfo.all.length > (mainType :: tail).length)
    (hty : ∀ p ∈ (mkAuxRecNameMap env'' (mainType :: tail)).2, ∃ j, p.2 = auxRecName types j)
    {recName : Name} (hrn : recName ∈ (mkAuxRecNameMap env'' (mainType :: tail)).1) :
    indBudget types
      (((mkAuxRecNameMap env'' (mainType :: tail)).2.lookup recName).getD recName) :=
  indBudget_processRec hty (.inl ((mkAuxRecNameMap_spec hmain hlen).2 recName hrn))

/-! ### §5.1a **The gate is discharged.**

`Verify/Inductive/NIndices.lean` proves all three fields, so `RunFreshGate` is no longer a barrier and
every `G`-parametrised result above is unconditional.  The field that needed
`stats.nindices.size = indTypes.size` is `member` — the one §1.1 measured as the only thing between
residual B and outright falsity; `NIndices.lean` §1 supplies it, at the cost of also discharging the
other three `assert!`s of `checkInductiveTypes` (see that file's §1 header for why all four are
forced). -/

theorem runFreshGate : RunFreshGate where
  member mapWF hrun := AddInductive.WF_run_member mapWF _ _ _ _ hrun
  ctor mapWF hrun := AddInductive.WF_run_ctor mapWF _ _ _ _ hrun
  ctors mapWF hrun := AddInductive.WF_run_ctors mapWF _ _ _ _ hrun

/-! ### §5.2 `RunFreshGate` is not asking for something false

`scripts/exists.lean` reports a bare `Prop` with no proof term as *unpriced*: its cone says nothing
about satisfiability.  This `#eval` prices it, at the same nested block as §1: it runs
`AddInductive.run` on the block `ElimNestedInductive.run` produced and **throws** unless all three
fields' instances hold there — member names fresh in the input environment, constructor names fresh,
and the stored `InductiveVal.ctors` equal to the member's own constructor names.  That is not a proof
of the gate (§5.1a is); since §5.1a's proof is `M.WF`-shaped — vacuous if `run` never accepted — this
`#eval` is now the check that the **accepting** case exists at a *name-fresh* block, which is what
keeps `runFreshGate` from being vacuously true. -/
#eval show Lean.CoreM Unit from do
  let kenv := (← getEnv).toKernelEnv
  let st : ElimNestedInductive.State := { lvls := [], newTypes := #[ntreeIndType] }
  let .ok res := (ElimNestedInductive.run 1000 0 [ntreeIndType] kenv).run' st
    | throwError "NestedRebuild/§5.2: ElimNestedInductive.run rejected the block"
  let c : AddInductive.Context :=
    { env := kenv, allowPrimitive := false, lparams := [], safety := .safe }
  let .ok env₁ := AddInductive.run 0 res.types res.aux2nested.length c
    | throwError "NestedRebuild/§5.2: AddInductive.run REJECTS the expanded block -- the gate's \
        own hypothesis cannot be exhibited, so it is unpriced"
  for t in res.types do
    unless (kenv.find? t.name).isNone do
      throwError "NestedRebuild/§5.2: RunFreshGate.member FAILS at {t.name} -- the input \
        environment already holds it, so the field is false at a run AddInductive accepts"
    for ct in t.ctors do
      unless (kenv.find? ct.name).isNone do
        throwError "NestedRebuild/§5.2: RunFreshGate.ctor FAILS at {ct.name}"
    let some (.inductInfo ind) := env₁.find? t.name
      | throwError "NestedRebuild/§5.2: AddInductive.run stored no .inductInfo at {t.name} -- \
          RunFreshGate.ctors is vacuous there and the rebuild's `unreachable!` is reachable"
    unless ind.name = t.name do
      throwError "NestedRebuild/§5.2: the entry at key {t.name} is MIS-KEYED (name = {ind.name}) \
        -- this is exactly the shape §1.1 says refutes residual B"
    unless ind.ctors = t.ctors.map (·.name) do
      throwError "NestedRebuild/§5.2: RunFreshGate.ctors FAILS at {t.name}: stored \
        {ind.ctors}, expected {t.ctors.map (·.name)}"
  Lean.logInfo m!"NestedRebuild/§5.2: all three RunFreshGate fields hold at the {res.types.length} \
    members of the expanded NTreeX block ({res.types.map (·.name)}), at a run AddInductive.run \
    accepts -- the gate is priced and asks for nothing false ✓"

/-! ## §6 The axiom trail -/

#print axioms Lean4Lean.auxRecName_mem_indDeclNamesN
#print axioms Lean4Lean.indBudget_auxRecName
#print axioms Lean4Lean.SWF.bind'
#print axioms Lean4Lean.SWF.checkName'
#print axioms Lean4Lean.SWF.addStep
#print axioms Lean4Lean.SWF.forM'
#print axioms Lean4Lean.forIn_auxRecFold
#print axioms Lean4Lean.auxRecFold_inv
#print axioms Lean4Lean.mkAuxRecNameMap_spec
#print axioms Lean4Lean.indBudget_processRec
#print axioms Lean4Lean.AddInductive.WF_checkInductiveTypes_ni
#print axioms Lean4Lean.AddInductive.WF_run_member
#print axioms Lean4Lean.AddInductive.WF_run_ctor
#print axioms Lean4Lean.AddInductive.WF_run_ctors
#print axioms Lean4Lean.runFreshGate
#print axioms Lean4Lean.inductInfo_name_eq
#print axioms Lean4Lean.ctorInfo_name_eq
#print axioms Lean4Lean.rebuild_indWrite_budget
#print axioms Lean4Lean.rebuild_ctorWrite_budget
#print axioms Lean4Lean.rebuild_recWrite_budget_user
#print axioms Lean4Lean.rebuild_recWrite_budget_aux

end Lean4Lean
