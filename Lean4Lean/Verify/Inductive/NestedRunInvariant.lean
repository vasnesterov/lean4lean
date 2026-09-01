import Lean4Lean.Verify.Inductive.AddInductiveStep

/-!
# A postcondition calculus for `ElimNestedInductive.M` that survives the nested branch

`Verify/Inductive/AddInductiveStep.lean` §1 builds a postcondition calculus for
`ElimNestedInductive.M` — `EWF` with `pure'`, `throw'`, `get'`, `modify'`, `mkFreshId'`, `bind'`,
`mono`, `mapM'`, `withParams'` — and §3–§4 use it to prove `run_EWF` (`:313`) via `run_loop_EWF`
(`:290`).  Those two theorems take `∀ n v, env.find? n ≠ some (.inductInfo v)` as a hypothesis,
which under `ves.WF env` is forced, so they describe the **degenerate** branch: `numNested = 0`.

## The correction this file records

The received summary of that situation is that *"the calculus transfers; its theorems do not"*.
Measured against the file, that is too generous by one step.  `EWF` is **not** a parameter of the
calculus — it is a closed definition with the degenerate invariant written into both halves
(`AddInductiveStep.lean:139`):

```
def EWF (env : Environment) (x : M α) (Q : α → Prop) : Prop :=
  ∀ s a s', s.nestedAux = #[] → x env s = .ok (a, s') → s'.nestedAux = #[] ∧ Q a
```

So every one of the nine combinators is a statement *about that predicate*, and in the nested
branch each is either unusable or false as stated:

* `EWF.modify'` requires `∀ s, (f s).nestedAux = s.nestedAux`.  `replaceIfNested`'s
  `modify fun st => { st with nestedAux := st.nestedAux.push (JAs', auxJ_name) }`
  (`Lean4Lean/Inductive/Add.lean:845`) is precisely a `modify` that violates it — it is the *only*
  writer of `nestedAux`, and pushing is what "the nested branch fired" means.
* `EWF.get'`'s postcondition is `s.nestedAux = #[]`, so any proof that reads the state through it
  inherits the degenerate hypothesis.
* `run_EWF`'s conclusion `r.aux2nested = []` is **false** at a nested block: the fidelity `#eval`
  in `Verify/Inductive/NestedRestoreWit.lean` §1.1 executes `ElimNestedInductive.run` on
  `inductive NFn | node : PFn NFn → NFn` and reads a one-entry `aux2nested` off the result.

What does transfer is the *shape*: the four `_eq` reduction lemmas, `bind_ok` and `run'_ok`
(`AddInductiveStep.lean:107-136`) are invariant-free and are re-used verbatim below.

## What this file adds

§1 `MWF` — the same Hoare triple with the state invariant made a **parameter** on both sides,
plus the nine combinators re-proved for it, and §2 `EWF_iff`, which exhibits `EWF` as the
instance at `P s := s.nestedAux = #[]`, `Q' a s := s.nestedAux = #[] ∧ Q a`.  So nothing is lost
and the degenerate branch stays available.

§3 names the residue.  Every `r`-side field of `RestoreData`/`OccData` that talks about the
*prefix* of `r.types` — `name`, `ctor`, `ownName`, `ownCtor` — follows from a single statement
about `replaceIfNested`: **it only appends to `newTypes`, never rewrites an existing entry's
names.**  `ReplaceAppendsOnly` is that statement as one `def`, and `MWF` is the vehicle in which
it composes.  It is *not* proved here: `replaceIfNested`'s body is a `for J_name in I_val.all`
loop, i.e. a `forIn` in `M`, and no `forIn` combinator exists for either calculus yet — that is
the next concrete step, and it is a `forIn` lemma, not a typing one.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace ElimNestedInductive

variable {α β : Type}

/-! ## 1. `MWF`: the calculus with the invariant as a parameter -/

/-- **A Hoare triple for `ElimNestedInductive.M`.**  `MWF env P x Q` says: started in a state
satisfying `P`, if `x` succeeds with value `a` and final state `s'` then `Q a s'`.

Unlike `EWF` (`Verify/Inductive/AddInductiveStep.lean:139`) neither side mentions `nestedAux`, so
the predicate is usable on the branch where `replaceIfNested` fires. -/
def MWF (env : Environment) (P : State → Prop) (x : M α) (Q : α → State → Prop) : Prop :=
  ∀ s a s', P s → x env s = .ok (a, s') → Q a s'

variable {env : Environment} {P : State → Prop} {Q : α → State → Prop}

theorem MWF.pure' {a : α} (h : ∀ s, P s → Q a s) : MWF env P (Pure.pure a) Q := by
  intro s b s' hs hb; rw [pure_eq] at hb; cases hb; exact h _ hs

theorem MWF.throw' (e : Exception) : MWF env P (throw e : M α) Q := by
  intro s b s' _ hb; rw [throw_eq] at hb; exact absurd hb nofun

/-- `get` hands the state to the continuation **together with `P`** — the clause `EWF.get'`
could only state at the degenerate invariant. -/
theorem MWF.get' : MWF env P (get : M State) (fun a s' => P s' ∧ a = s') := by
  intro s a s' hs h; rw [get_eq] at h; cases h; exact ⟨hs, rfl⟩

/-- `modify` with **no** side condition on `f`: the obligation is discharged where the caller
knows what `f` does, instead of being a blanket "`f` does not touch `nestedAux`". -/
theorem MWF.modify' {Q : PUnit → State → Prop} {f : State → State}
    (h : ∀ s, P s → Q () (f s)) : MWF env P (modify f : M PUnit) Q := by
  intro s a s' hs hb; rw [modify_eq] at hb; cases hb; exact h _ hs

theorem MWF.mkFreshId' {Q : Name → State → Prop}
    (h : ∀ s, P s → Q s.ngen.curr { s with ngen := s.ngen.next }) :
    MWF env P (mkFreshId : M Name) Q := by
  intro s a s' hs hb; rw [mkFreshId_eq] at hb; cases hb; exact h _ hs

theorem MWF.bind' {x : M α} {f : α → M β} {R : β → State → Prop} (hx : MWF env P x Q)
    (hf : ∀ a, MWF env (Q a) (f a) R) : MWF env P (x >>= f) R := by
  intro s b s' hs h
  obtain ⟨a, s'', h1, h2⟩ := bind_ok h
  exact hf a s'' b s' (hx s a s'' hs h1) h2

theorem MWF.mono {x : M α} {R : α → State → Prop} (hx : MWF env P x Q)
    (h : ∀ a s, Q a s → R a s) : MWF env P x R :=
  fun s a s' hs hr => h _ _ (hx s a s' hs hr)

/-- A pure side fact rides along untouched. -/
theorem MWF.frame {x : M α} {I : State → Prop} {A : Prop} {R : α → State → Prop}
    (hx : MWF env I x R) : MWF env (fun s => A ∧ I s) x (fun a s => A ∧ R a s) :=
  fun s a s' hs hr => ⟨hs.1, hx s a s' hs.2 hr⟩

/-- Weakening the precondition. -/
theorem MWF.weaken {x : M α} {P' : State → Prop} (hx : MWF env P x Q) (h : ∀ s, P' s → P s) :
    MWF env P' x Q := fun s a s' hs hr => hx s a s' (h _ hs) hr

/-- `mapM` preserving a state invariant. -/
theorem MWF.mapM' {f : α → M β} {I : State → Prop}
    (hf : ∀ a, MWF env I (f a) (fun _ => I)) :
    ∀ l : List α, MWF env I (l.mapM f) (fun _ => I)
  | [] => by rw [List.mapM_nil]; exact MWF.pure' fun _ h => h
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind' fun _ => (MWF.mapM' hf l).bind' fun _ => MWF.pure' fun _ h => h

/-- `mapM` preserving a state invariant **and** collecting a per-element value fact.  This is the
form `run.loop` needs: the rebuilt constructor list must be known to carry the *same names*. -/
theorem MWF.mapM_forall₂ {f : α → M β} {I : State → Prop} {p : α → β → Prop}
    (hf : ∀ a, MWF env I (f a) (fun b s' => p a b ∧ I s')) :
    ∀ l : List α, MWF env I (l.mapM f) (fun bs s' => List.Forall₂ p l bs ∧ I s')
  | [] => by rw [List.mapM_nil]; exact MWF.pure' fun _ h => ⟨.nil, h⟩
  | a :: l => by
    rw [List.mapM_cons]
    refine (hf a).bind' fun b => ?_
    refine MWF.bind' (MWF.frame (A := p a b) (MWF.mapM_forall₂ hf l)) fun bs => ?_
    exact MWF.pure' fun _ h => ⟨.cons h.1 h.2.1, h.2.2⟩

/-- `withParams` transports `MWF`, provided the invariant survives a fresh-name allocation —
which every invariant about `newTypes` or `nestedAux` does. -/
theorem MWF.withParams' {k : LocalContext → Expr → Array Expr → M α} {I : State → Prop}
    (hng : ∀ s, I s → I { s with ngen := s.ngen.next })
    (n : Nat) (hk : ∀ lctx t ps, ps.size = n → MWF env I (k lctx t ps) Q) (type : Expr) :
    MWF env I (withParams type n k) Q := by
  have main : ∀ i lctx t ps, ps.size + i = n → MWF env I (withParams.loop k lctx t ps i) Q := by
    intro i
    induction i with
    | zero => intro lctx t ps hps; rw [withParams.loop]; exact hk lctx t ps (by omega)
    | succ i ih =>
      intro lctx t ps hps
      cases t with
      | forallE name dom body bi =>
        rw [withParams.loop]
        exact MWF.bind' (MWF.mkFreshId' fun s hs => hng s hs) fun _ =>
          ih _ _ _ (by simp only [Array.size_push]; omega)
      | _ => rw [withParams.loop] <;> first | exact MWF.throw' _ | nofun
  exact main n {} type #[] (by simp)

/-! ## 2. `EWF` is the degenerate instance

Nothing the existing file proves is lost: `EWF env x Q` *is* `MWF` at the invariant
`s.nestedAux = #[]`.  Read the other way, this is the measurement: the invariant is not a
parameter of `EWF`, it is part of its statement, which is why `EWF.modify'` carries the side
condition that `replaceIfNested`'s push violates. -/

theorem EWF_iff {x : M α} {Q : α → Prop} :
    EWF env x Q ↔
      MWF env (fun s => s.nestedAux = #[]) x (fun a s' => s'.nestedAux = #[] ∧ Q a) :=
  ⟨fun h s a s' hs hr => h s a s' hs hr, fun h s a s' hs hr => h s a s' hs hr⟩

theorem EWF.toMWF {x : M α} {Q : α → Prop} (h : EWF env x Q) :
    MWF env (fun s => s.nestedAux = #[]) x (fun a s' => s'.nestedAux = #[] ∧ Q a) :=
  EWF_iff.1 h

theorem MWF.toEWF {x : M α} {Q : α → Prop}
    (h : MWF env (fun s => s.nestedAux = #[]) x (fun a s' => s'.nestedAux = #[] ∧ Q a)) :
    EWF env x Q := EWF_iff.2 h

/-! ## 3. The residue, named

The four `RestoreData` fields that speak about the *prefix* of `r.types` — `name`, `ctor`,
`ownName`, `ownCtor` (`Verify/Inductive/NestedRestore.lean` §6) — all read off one property of
the run: the name skeleton of `State.newTypes` at the end **extends** the one it started with.
`run.loop`'s own write is `newTypes.set! i { indType with ctors }`, which by construction keeps
the member's name and (since each rebuilt constructor is `{ ctor with type := … }`) every
constructor's name; so the whole content of the property is that `replaceAllNested` — i.e.
`replaceIfNested` under `Expr.replaceNoCacheT` — only ever *appends*. -/

/-- The names a block presents: one member name and its constructor names, per member. -/
def nameSkel (l : List InductiveType) : List (Name × List Name) :=
  l.map fun T => (T.name, T.ctors.map (·.name))

theorem nameSkel_append (l₁ l₂ : List InductiveType) :
    nameSkel (l₁ ++ l₂) = nameSkel l₁ ++ nameSkel l₂ := List.map_append ..

/-- The state invariant: `newTypes`' name skeleton extends `sk`. -/
def SkelExt (sk : List (Name × List Name)) (s : State) : Prop :=
  ∃ tail, nameSkel s.newTypes.toList = sk ++ tail

theorem SkelExt.rfl' (s : State) : SkelExt (nameSkel s.newTypes.toList) s :=
  ⟨[], (List.append_nil _).symm⟩

theorem SkelExt.ngen {sk s} (h : SkelExt sk s) : SkelExt sk { s with ngen := s.ngen.next } := h

/-- `SkelExt` is exactly what a `push` preserves. -/
theorem SkelExt.push {sk s} (h : SkelExt sk s) (T : InductiveType) :
    SkelExt sk { s with newTypes := s.newTypes.push T } := by
  obtain ⟨tail, ht⟩ := h
  refine ⟨tail ++ [(T.name, T.ctors.map (·.name))], ?_⟩
  rw [show ({ s with newTypes := s.newTypes.push T } : State).newTypes.toList
      = s.newTypes.toList ++ [T] from Array.toList_push .., nameSkel_append, ht,
    List.append_assoc]
  rfl

/-- **The residue.**  `replaceAllNested` only appends to `newTypes`.

Everything §3's prose reduces to this, and it is a statement about a `forIn` in `M`: the loop
`for J_name in I_val.all do … modify fun st => { st with newTypes := st.newTypes.push newType }`
at `Lean4Lean/Inductive/Add.lean:836-858`.  Neither calculus has a `forIn` combinator yet, which
is why this is a `def` and not a `theorem`. -/
def ReplaceAppendsOnly (env : Environment) : Prop :=
  ∀ (sk : List (Name × List Name)) (lctx : LocalContext) (params As : Array Expr) (e : Expr),
    MWF env (SkelExt sk) (replaceAllNested lctx params As e) (fun _ => SkelExt sk)

/-- …and it is satisfiable: on the degenerate branch `replaceAllNested` is the identity, so it
appends nothing.  So `ReplaceAppendsOnly` is not an unsatisfiable precondition — it is the
*general* form of `EWF.replaceAllNested'` (`AddInductiveStep.lean:278`), with the same proof at
the same hypothesis. -/
theorem replaceAppendsOnly_of_no_inductInfo {env : Environment}
    (h : ∀ n v, env.find? n ≠ some (.inductInfo v)) : ReplaceAppendsOnly env := by
  intro sk lctx params As e s a s' hs hr
  rw [replaceAllNested_id h] at hr
  cases hr; exact hs

end ElimNestedInductive
end Lean4Lean
