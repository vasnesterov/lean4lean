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

## A second correction: what `assert!` does in this monad

`AddInductiveStep.lean:184-190` (`EWF.withParams'`'s docstring) says that `assert!` elaborates to
`panicWithPosWithDecl`, "which in this monad returns `.ok (default, default)` rather than an
error, and `(default : State).nestedAux = #[]` is *not* the incoming state".  **Both halves are
wrong**, and §4's `panic_eq` is the machine-checked statement of what is actually true:

```
(panicWithPosWithDecl m d l c msg : M α) env s = .ok (default, s)
```

`Inhabited (M α)` does *not* resolve through `Inhabited (Except ε α)` (that instance needs
`[Inhabited ε]`, and `Kernel.Exception` has no `Inhabited` instance — `#synth` fails).  It
resolves through `instInhabitedOfMonad`, i.e. `pure default`.  So a panic returns the value
`default` **with the incoming state untouched** — neither an error nor a reset state.

Two consequences, and the second is the reason this file gets further than expected:

* the `ps.size = n` conclusion of `EWF.withParams'` is *not* load-bearing for the reason given:
  on the panic branch `s' = s`, so `EWF`'s postcondition holds there for free.
* **every `assert!` and `unreachable!` in `ElimNestedInductive` is invariant-preserving.**  So the
  four panic sites in `replaceIfNested` — `assert! I_nparams ≤ args.size`,
  `let .const … | unreachable!`, `let .inductInfo … | unreachable!`, `assert! result.isSome` —
  need no side conditions, and neither does `replaceParams`'s `assert! As.size == params.size`.
  §6 proves `ReplaceAppendsOnly` with no hypothesis at all.

What does transfer is the *shape*: the four `_eq` reduction lemmas, `bind_ok` and `run'_ok`
(`AddInductiveStep.lean:107-136`) are invariant-free and are re-used verbatim below.

## What this file adds

§1 `MWF` — the same Hoare triple with the state invariant made a **parameter** on both sides,
plus the nine combinators re-proved for it, and §2 `EWF_iff`, which exhibits `EWF` as the
instance at `P s := s.nestedAux = #[]`, `Q' a s := s.nestedAux = #[] ∧ Q a`.  So nothing is lost
and the degenerate branch stays available.

§4 is the loop rule the residue needed, §5 the rest of the step lemmas, and §6 closes
`ReplaceAppendsOnly` outright.

§3 names the residue.  Every `r`-side field of `RestoreData`/`OccData` that talks about the
*prefix* of `r.types` — `name`, `ctor`, `ownName`, `ownCtor` — follows from a single statement
about `replaceIfNested`: **it only appends to `newTypes`, never rewrites an existing entry's
names.**  `ReplaceAppendsOnly` is that statement as one `def`, and `MWF` is the vehicle in which
it composes.  §6 proves it, with the loop rule of §4.
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


/-! ## 4. The loop rule

`replaceIfNested` runs `for J_name in I_val.all do … modify …` — a `forIn` in `M`, with a mutable
`result` threaded through it as the accumulator.  `MWF.forIn'` is the Hoare loop rule for that:
the invariant is indexed by the **remaining** list and the accumulator, so the body's
postcondition feeds the next iteration's precondition, and `.done` exits straight into the
conclusion.  `MWF.forIn_inv` is the state-invariant special case, which is what §6 uses. -/

/-- **The `MWF` loop rule.**  General in the list, the accumulator and the body. -/
theorem MWF.forIn' {f : α → β → M (ForInStep β)}
    {P : List α → β → State → Prop} {Q : β → State → Prop}
    (hstep : ∀ a l b, MWF env (P (a :: l) b) (f a b)
      (fun r s => match r with | .yield b' => P l b' s | .done b' => Q b' s))
    (hdone : ∀ b s, P [] b s → Q b s) :
    ∀ (l : List α) (b : β), MWF env (P l b) (forIn l b f) Q
  | [], b => by rw [List.forIn_nil]; exact MWF.pure' fun s hs => hdone b s hs
  | a :: l, b => by
    rw [List.forIn_cons]
    refine MWF.bind' (hstep a l b) fun r => ?_
    cases r with
    | done b' => exact MWF.pure' fun _ h => h
    | yield b' => exact MWF.forIn' hstep hdone l b'

/-- …and the state-invariant case: a loop whose every iteration preserves `I` preserves `I`. -/
theorem MWF.forIn_inv {I : State → Prop} {f : α → β → M (ForInStep β)}
    (hstep : ∀ a b, MWF env I (f a b) (fun _ => I)) (l : List α) (b : β) :
    MWF env I (forIn l b f) (fun _ => I) :=
  MWF.forIn' (P := fun _ _ => I) (Q := fun _ => I)
    (fun a _ b => (hstep a b).mono fun r s h => by cases r <;> exact h) (fun _ _ h => h) l b

/-! ## 5. The remaining step lemmas

Nine of them, one per kind of `M`-operation `replaceIfNested` performs.  `panic_eq` is the
measurement §0 announced. -/

variable {I : State → Prop}

/-- **What `assert!`/`unreachable!` really do in `M`.**  `Inhabited (M α)` is
`instInhabitedOfMonad`, i.e. `pure default`: the value is `default`, **the state is the incoming
one**, and nothing is thrown.  Contrast `AddInductiveStep.lean:184-190`. -/
theorem panic_eq {α} [Inhabited α] (m d : String) (l c : Nat) (msg : String) (s : State) :
    (panicWithPosWithDecl m d l c msg : M α) env s = .ok (default, s) := by
  with_unfolding_all rfl

theorem MWF.panic' {α} [Inhabited α] (m d : String) (l c : Nat) (msg : String) :
    MWF env I (panicWithPosWithDecl m d l c msg : M α) (fun _ => I) := by
  intro s a s' hs h; rw [panic_eq] at h; cases h; exact hs

/-- `bind` at a fixed invariant.  Unlike `MWF.bind'` the intermediate postcondition is determined
by the goal, which is what lets a `repeat`-style automation use it. -/
theorem MWF.bind_inv {x : M α} {f : α → M β} {R : β → State → Prop}
    (hx : MWF env I x (fun _ => I)) (hf : ∀ a, MWF env I (f a) R) : MWF env I (x >>= f) R :=
  MWF.bind' hx hf

theorem MWF.get_inv : MWF env I (get : M State) (fun _ => I) := by
  intro s a s' hs h; rw [get_eq] at h; cases h; exact hs

theorem read_eq (s : State) : (read : M Environment) env s = .ok (env, s) := by
  with_unfolding_all rfl

theorem MWF.read_inv : MWF env I (read : M Environment) (fun _ => I) := by
  intro s a s' hs h; rw [read_eq] at h; cases h; exact hs

/-- `Environment.get` and `instantiateForallParams` reach `M` through `liftM` from
`Except Exception`, which is state-transparent. -/
theorem MWF.liftExcept' {α} (x : Except Exception α) :
    MWF env I (liftM x : M α) (fun _ => I) := by
  intro s a s' hs h
  cases x with
  | error e =>
    rw [show (liftM (Except.error e) : M α) env s = .error e from by with_unfolding_all rfl] at h
    exact absurd h nofun
  | ok b =>
    rw [show (liftM (Except.ok b) : M α) env s = .ok (b, s) from by with_unfolding_all rfl] at h
    cases h; exact hs

/-- `mkUniqueName` advances `nextIdx` and touches nothing else — in particular not `newTypes`. -/
theorem mkUniqueName_state {n : Name} {s a s'} (h : mkUniqueName n env s = .ok (a, s')) :
    s' = { s with nextIdx := s'.nextIdx } := by
  have main : ∀ fuel i, mkUniqueName.loop env n s i fuel = .ok (a, s') →
      s' = { s with nextIdx := s'.nextIdx } := by
    intro fuel
    induction fuel with
    | zero => intro i hi; rw [mkUniqueName.loop] at hi; exact absurd hi nofun
    | succ fuel ih =>
      intro i hi
      rw [mkUniqueName.loop] at hi
      split at hi
      · exact ih _ hi
      · cases hi; rfl
  exact main _ _ h

/-- **`mkUniqueName`'s freshness, stated correctly: it is against the `Environment`.**  The loop
tests `env.contains r` and returns the first index that fails it (`Add.lean:766-773`).

Read this together with `Verify/Inductive/NestedOccData.lean` §10: the block being declared is
**not** in `env` — that is what `Environment.addInductive`'s own collision checks are for — so this
gives no separation at all between `mkUniqueName`'s output and the input block's names, and §10
exhibits a block where they collide. -/
theorem mkUniqueName_fresh {n : Name} {s a s'} (h : mkUniqueName n env s = .ok (a, s')) :
    env.contains a = false := by
  have main : ∀ fuel i, mkUniqueName.loop env n s i fuel = .ok (a, s') →
      env.contains a = false := by
    intro fuel
    induction fuel with
    | zero => intro i hi; rw [mkUniqueName.loop] at hi; exact absurd hi nofun
    | succ fuel ih =>
      intro i hi
      rw [mkUniqueName.loop] at hi
      split at hi
      · exact ih _ hi
      · rename_i hc; cases hi; simpa using hc
  exact main _ _ h

theorem MWF.mkUniqueName_skel {sk} (n : Name) :
    MWF env (SkelExt sk) (mkUniqueName n) (fun _ => SkelExt sk) := by
  intro s a s' hs h; rw [mkUniqueName_state h]; exact hs

/-- `replaceParams` — **unconditionally**, both branches of its `assert!`. -/
theorem MWF.replaceParams' {sk} (params As : Array Expr) (e : Expr) :
    MWF env (SkelExt sk) (replaceParams params e As) (fun _ => SkelExt sk) := by
  intro s a s' hs h
  unfold replaceParams at h
  split at h
  · rw [pure_eq] at h; cases h; exact hs
  · rw [panic_eq] at h; cases h; exact hs

/-- The traversal `replaceAllNested` runs: `Expr.replaceNoCacheT` transports any invariant its
replacement function transports. -/
theorem MWF.replaceNoCacheT {f? : Expr → M (Option Expr)}
    (hf : ∀ e, MWF env I (f? e) (fun _ => I)) (e : Expr) :
    MWF env I (Expr.replaceNoCacheT f? e) (fun _ => I) := by
  induction e with
  | _ =>
    rw [Lean.Expr.replaceNoCacheT]
    · refine MWF.bind' (hf _) fun o => ?_
      cases o with
      | some eNew => exact MWF.pure' fun _ h => h
      | none =>
        first
        | exact MWF.pure' fun _ h => h
        | (refine MWF.bind' (by assumption) fun _ => ?_
           first
           | exact MWF.pure' fun _ h => h
           | (refine MWF.bind' (by assumption) fun _ => ?_
              first
              | exact MWF.pure' fun _ h => h
              | (refine MWF.bind' (by assumption) fun _ => ?_
                 exact MWF.pure' fun _ h => h)))
    all_goals nofun

set_option maxHeartbeats 2000000 in
/-- **`isNestedInductiveApp?` preserves every state invariant.**  It only `read`s and `get`s; its
`for i in [0:ci.numParams]` loop is a `Std.Legacy.Range` `forIn`, which core's
`forIn_eq_forIn_range'` turns into a `List` one, so §4's rule applies. -/
theorem MWF.isNestedApp' (e : Expr) : MWF env I (isNestedInductiveApp? e) (fun _ => I) := by
  unfold isNestedInductiveApp?
  repeat (first
    | exact MWF.pure' fun _ h => h
    | exact MWF.throw' _
    | exact MWF.get_inv
    | exact MWF.read_inv
    | rw [Std.Legacy.Range.forIn_eq_forIn_range']
    | dsimp only
    | refine MWF.bind_inv ?_ fun _ => ?_
    | refine MWF.forIn_inv (fun _ _ => ?_) _ _
    | split)

/-! ## 6. `ReplaceAppendsOnly`, proved

The automation below is the whole content: *every* `M`-operation `replaceIfNested` performs is one
of §5's nine, and each preserves `SkelExt`.  In particular

* the `modify` that pushes to `nestedAux` (`Add.lean:845`) does not touch `newTypes`, so
  `SkelExt` is preserved *definitionally* — `fun _ h => h`;
* the `modify` that pushes to `newTypes` (`Add.lean:858`) is `SkelExt.push`;
* **no iteration's `modify` rewrites an existing entry**, and no panic resets the state.

So `replaceIfNested` appends and nothing else. -/

syntax "mwf_skel" : tactic
macro_rules
  | `(tactic| mwf_skel) => `(tactic|
      repeat (first
        | exact MWF.pure' fun _ h => h
        | exact MWF.throw' _
        | exact MWF.panic' _ _ _ _ _
        | exact MWF.liftExcept' _
        | exact MWF.replaceParams' _ _ _
        | exact MWF.mkUniqueName_skel _
        | exact MWF.get_inv
        | exact MWF.read_inv
        | exact MWF.modify' fun _ h => h
        | exact MWF.modify' fun _ h => SkelExt.push h _
        | rw [Lean.Expr.withApp_eq]
        | dsimp only
        | refine MWF.bind_inv ?_ fun _ => ?_
        | refine MWF.forIn_inv (fun _ _ => ?_) _ _
        | refine MWF.mapM' (fun _ => ?_) _
        | split))

set_option maxHeartbeats 4000000 in
/-- **`replaceIfNested` only appends to `newTypes`.** -/
theorem MWF.replaceIfNested' {sk} (lctx : LocalContext) (params As : Array Expr) (e : Expr) :
    MWF env (SkelExt sk) (replaceIfNested lctx params As e) (fun _ => SkelExt sk) := by
  unfold replaceIfNested
  refine MWF.bind' (MWF.isNestedApp' e) fun o => ?_
  cases o with
  | none => exact MWF.pure' fun _ h => h
  | some I_val => mwf_skel

/-- **The residue of §3, discharged.**  No hypothesis on the environment, and none on the
`assert!`s. -/
theorem replaceAppendsOnly (env : Environment) : ReplaceAppendsOnly env :=
  fun _ lctx params As e => MWF.replaceNoCacheT (fun _ => MWF.replaceIfNested' lctx params As _) e


/-! ## 7. From `ReplaceAppendsOnly` to `run`

`run.loop`'s own write is

```
modify fun s => { s with newTypes := s.newTypes.set! i { indType with ctors } }
```

with `indType` read off an *earlier* `get` in the same iteration and `ctors` from a `mapM` whose
every element is `{ ctor with type := … }`.  Three facts make it skeleton-preserving:

1. **overwriting an entry by one with the same name skeleton is a no-op on `nameSkel`** —
   `nameSkel_set`, and `SkelExt.set`, which also covers `i` past the pinned prefix (there the
   write cannot touch it at all);
2. the `mapM` keeps each constructor's *name* — `MWF.mapM_forall₂` at
   `p c c' := c'.name = c.name`.  Its panic branch would return `default`, whose name is
   `.anonymous`; this is the one place where `withParams`' `ps.size = n` conclusion is genuinely
   needed, and it is needed **by the caller**, exactly as the corrected
   `AddInductiveStep.lean:184-190` now says;
3. the cross-state step: `indType` comes from `s₀`, and `replaceAllNested` may have appended
   since.  `SkelExt sk` pins the whole prefix in *every* state, so `SkelExt.getElem` reads the
   `i`-th skeleton entry off `s₀` and `MWF.frame` carries that pure fact across the `mapM`.

So `RunSkelExtends` closes, and `run_prefix` is the entrywise form the `RestoreData` fields
consume.  Which of them actually follow is settled in
`Verify/Inductive/NestedOccData.lean` §8 — field by field, and not all of them do. -/

theorem List.set_eq_self_of_getElem? {α : Type _} : ∀ {l : List α} {i : Nat} {a : α},
    l[i]? = some a → l.set i a = l
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by simp at h; rw [List.set_cons_zero, h]
  | b :: l, i+1, a, h => by
    rw [List.set_cons_succ, List.set_eq_self_of_getElem? (l := l) (by simpa using h)]

/-- **Overwriting an entry by one with the same name skeleton leaves `nameSkel` alone.** -/
theorem nameSkel_set {l : List InductiveType} {i : Nat} {T : InductiveType}
    (h : (nameSkel l)[i]? = some (T.name, T.ctors.map (·.name))) :
    nameSkel (l.set i T) = nameSkel l := by
  rw [nameSkel, List.map_set]
  exact List.set_eq_self_of_getElem? h

/-- …and `SkelExt` survives such a write at *any* index: inside the pinned prefix by
`nameSkel_set`, past it because the write cannot reach the prefix. -/
theorem SkelExt.set {sk} {s : State} {i : Nat} {T : InductiveType} (h : SkelExt sk s)
    (hT : ∀ p, sk[i]? = some p → p = (T.name, T.ctors.map (·.name))) :
    SkelExt sk { s with newTypes := s.newTypes.set! i T } := by
  obtain ⟨tail, ht⟩ := h
  have hL : ({ s with newTypes := s.newTypes.set! i T } : State).newTypes.toList
      = s.newTypes.toList.set i T := Array.toList_set!
  rw [SkelExt, hL, nameSkel, List.map_set,
    show List.map (fun T => (T.name, T.ctors.map (·.name))) s.newTypes.toList
      = sk ++ tail from ht]
  by_cases hi : i < sk.length
  · refine ⟨tail, ?_⟩
    rw [List.set_append_left _ _ hi]
    congr 1
    refine List.set_eq_self_of_getElem? ?_
    have hp : sk[i]? = some sk[i] := List.getElem?_eq_getElem hi
    rw [hp, ← hT _ hp]
  · exact ⟨tail.set (i - sk.length) _, List.set_append_right _ _ (Nat.le_of_not_lt hi)⟩

/-- The `i`-th pinned skeleton entry, read off the array. -/
theorem SkelExt.getElem {sk} {s : State} {i : Nat} (h : SkelExt sk s)
    (hi : i < s.newTypes.size) :
    ∀ p, sk[i]? = some p → p = (s.newTypes[i].name, s.newTypes[i].ctors.map (·.name)) := by
  obtain ⟨tail, ht⟩ := h
  intro p hp
  have hlt : i < sk.length := by
    rcases Nat.lt_or_ge i sk.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hp; exact absurd hp nofun
  have h1 : (nameSkel s.newTypes.toList)[i]?
      = some (s.newTypes[i].name, s.newTypes[i].ctors.map (·.name)) := by
    rw [nameSkel, List.getElem?_map,
      show s.newTypes.toList[i]? = some s.newTypes[i] from by
        simp [List.getElem?_eq_getElem (l := s.newTypes.toList)
          (show i < s.newTypes.toList.length by simpa using hi)]]
    rfl
  rw [ht, List.getElem?_append_left hlt, hp] at h1
  exact Option.some.injEq .. ▸ h1

theorem map_name_of_forall₂ : ∀ {l bs : List Constructor},
    List.Forall₂ (fun c c' => c'.name = c.name) l bs → bs.map (·.name) = l.map (·.name)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by rw [List.map_cons, List.map_cons, h, map_name_of_forall₂ hs]

set_option maxHeartbeats 1000000 in
/-- **`run.loop` extends the name skeleton and never rewrites it.** -/
theorem run_loop_skel {sk} (nparams : Nat) (lctx : LocalContext) (params : Array Expr) :
    ∀ (fuel i : Nat), MWF env (SkelExt sk) (run.loop nparams lctx params i fuel)
      (fun r s => SkelExt sk s ∧ ∃ tail, nameSkel r.types = sk ++ tail) := by
  intro fuel
  induction fuel with
  | zero => intro i; rw [run.loop]; exact MWF.throw' _
  | succ fuel ih =>
    intro i
    rw [run.loop]
    refine MWF.bind' MWF.get' fun s0 => ?_
    split
    · rename_i hi
      dsimp only
      refine MWF.weaken (P := fun s' =>
        (∀ p, sk[i]? = some p
            → p = (s0.newTypes[i].name, s0.newTypes[i].ctors.map (·.name))) ∧ SkelExt sk s')
        ?_ (fun s' h => ⟨SkelExt.getElem (by rw [h.2]; exact h.1) hi, h.1⟩)
      refine MWF.bind' (MWF.frame (MWF.mapM_forall₂
        (p := fun c c' => Constructor.name c' = Constructor.name c) (fun ctor => ?_) _))
        fun ctors => ?_
      · refine MWF.withParams' (fun _ h => h) nparams (fun lctx' t As hAs => ?_) _
        rw [hAs]
        simp only [beq_self_eq_true, if_true]
        exact MWF.bind' (replaceAppendsOnly env sk lctx' params As t) fun _ =>
          MWF.pure' fun _ h => ⟨rfl, h⟩
      · refine MWF.bind' (MWF.modify' (Q := fun _ => SkelExt sk) fun s h => ?_)
          fun _ => ih (i+1)
        refine SkelExt.set h.2.2 fun p hp => ?_
        rw [h.1 p hp, map_name_of_forall₂ h.2.1]
    · exact MWF.pure' fun s' h => ⟨h.1, by rw [h.2]; exact h.1⟩

theorem run_skel {sk} (fuel np : Nat) (types : List InductiveType) :
    MWF env (SkelExt sk) (run fuel np types)
      (fun r s => SkelExt sk s ∧ ∃ tail, nameSkel r.types = sk ++ tail) := by
  unfold run
  split
  · refine MWF.bind' (MWF.modify' (Q := fun _ => SkelExt sk) fun s h => h) fun _ => ?_
    exact MWF.withParams' (fun _ h => h) np
      (fun lctx t ps _ => run_loop_skel np lctx ps fuel 0) _
  · exact MWF.throw' _

/-- The `run`-level conclusion the four prefix fields of `RestoreData` read off: `run` only ever
*extends* the name skeleton of the block it was handed. -/
def RunSkelExtends (env : Environment) : Prop :=
  ∀ (fuel np : Nat) (types : List InductiveType) (s : State) (r : Result) (s' : State),
    run fuel np types env s = .ok (r, s') →
      ∃ tail, nameSkel r.types = nameSkel s.newTypes.toList ++ tail

/-- **Proved.** -/
theorem runSkelExtends (env : Environment) : RunSkelExtends env := fun fuel np types s r s' h =>
  (run_skel (sk := nameSkel s.newTypes.toList) fuel np types s r s' (SkelExt.rfl' s) h).2

/-- **The entrywise form.**  On the prefix, `run`'s output member has the input member's name and
its constructors' names, in order. -/
theorem run_prefix {fuel np : Nat} {types : List InductiveType} {s : State} {r : Result}
    {s' : State} (hs : s.newTypes.toList = types)
    (h : run fuel np types env s = .ok (r, s')) :
    ∀ (j : Nat) (t : InductiveType), r.types[j]? = some t → j < types.length →
      ∃ u, types[j]? = some u ∧ t.name = u.name ∧
        t.ctors.map (·.name) = u.ctors.map (·.name) := by
  obtain ⟨tail, ht⟩ := runSkelExtends env fuel np types s r s' h
  rw [hs] at ht
  intro j t hjt hj
  have h1 : (nameSkel r.types)[j]? = some (t.name, t.ctors.map (·.name)) := by
    rw [nameSkel, List.getElem?_map, hjt]; rfl
  rw [ht, List.getElem?_append_left (by rwa [nameSkel, List.length_map])] at h1
  rw [nameSkel, List.getElem?_map] at h1
  cases hu : types[j]? with
  | none => rw [hu] at h1; exact absurd h1 nofun
  | some u =>
    rw [hu] at h1
    have h2 := Option.some.injEq .. ▸ h1
    refine ⟨u, rfl, ?_, ?_⟩
    · exact ((Prod.mk.injEq .. ▸ h2).1 : u.name = t.name).symm
    · exact ((Prod.mk.injEq .. ▸ h2).2 :
        List.map (·.name) u.ctors = List.map (·.name) t.ctors).symm

end ElimNestedInductive
end Lean4Lean
