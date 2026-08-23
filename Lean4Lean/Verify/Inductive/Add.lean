import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.TypeChecker

/-!
# A `WF` framework for the inductive adder

`Verify/TypeChecker/` refines the type checker; **nothing refines `Lean4Lean/Inductive/Add.lean`**,
and `TrEnv'.induct` demands `decl.WF env` — which only the adder's own run can supply.  This
file is that framework (R0).

## Why it is not the type checker's framework

`Verify/TypeChecker/Basic.lean` builds `M.WF` over
`ReaderT Context (StateT State (Except Exception))`, so its postconditions are
`α → VState → Prop` and every `bind` threads state monotonicity: `VState.LE`, `.rfl`, `.trans`,
`.reserves`, `.next`, `getNGen`, `InferCache.WF` and the `M.WF.le` combinator all exist to serve
that.

`AddInductive.M` is `ReaderT Context (Except Exception)` — **no state**.  So `M.WF` is
`∀ a, x c = .ok a → Q a`, postconditions are `α → Prop`, and the entire monotonicity apparatus
disappears.  That is why this framework is a fraction of the analogue's size rather than
comparable to it.

## What the postcondition is stated over

`M.WF` takes the *raw* `Context`, not an abstract one.  The abstract data — the `VEnv`, the
`VLCtx` mirroring `Context.lctx`, and the invariants tying them — belongs in the *statements*
of the individual phase lemmas, not in the combinators.  Keeping it out here makes this section
independent of that one, which matters because the two have different risk profiles: these are
mechanical, and the context is where the reuse question lives.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! # Part 0: the occurrence check, specified

`checkPositivity`'s only evidence is `hasIndOcc stats.indConsts (← whnf dom) = false`, and until
recently that could not be read at all: `hasIndOcc` went through `Lean.Expr.find?`, i.e.
`Lean.Expr.findImpl?`, an `@[extern] opaque` with **no Lean-side body**.  Nothing inside a proof
can say what a body-less constant computes, so R7 needed a new interface axiom and was blocked
on a policy question rather than a proof difficulty.

**That dependency is gone.**  `Lean4Lean.anySubterm` (`Lean4Lean/Inductive/Add.lean`) replaces
all three `find?` call sites; it delegates to `Lean.Expr.replaceNoCacheT` (`Lean4Lean/Expr.lean`),
ordinary total Lean whose body unfolds in a proof.

**Measured, not assumed, and measured structurally rather than by grep.**  A transitive-closure
scan of `Lean4Lean.addDecl`'s cone — `getUsedConstantsAsSet`, following `@[implemented_by]`
targets and `_unsafe_rec` companions, i.e. `Guard.lean`'s check-3 traversal — reports
`Lean.Expr.find?`, `Lean.Expr.findImpl?`, `Lean.Expr.findExtImpl?` and `Lean.Expr.occurs` all
**absent**, and `Lean.Expr.replaceNoCacheT`, `Lean4Lean.anySubterm`,
`Lean4Lean.AddInductive.hasIndOcc` all **reachable**.  A textual check of
`Lean4Lean/Inductive/Add.lean` would not have settled this, since the call could have arrived
through any of the cone's other 1000-odd constants.

This section is the specification: a pure structural predicate `anySub`, and
`anySubterm_eq : anySubterm p e = anySub p e`.  It costs **no axiom** — the whole section is
`propext`-only, which is already on `Guard.lean`'s whitelist as a standard axiom. -/

/-- The pure structural reading of `anySubterm p e`: does `p` hold of `e` or of any of its
descendants?  "Descendant" is the node set `Expr.replaceNoCacheT` visits — an application's
`f` and `a`, a binder's domain and body, a `mdata`/`proj` payload, a `letE`'s three
components — which is also the node set the C traversal `for_each_fn<true>` visits. -/
def anySub (p : Expr → Bool) (e : Expr) : Bool :=
  p e || match e with
    | .forallE _ d b _ => anySub p d || anySub p b
    | .lam _ d b _ => anySub p d || anySub p b
    | .mdata _ b => anySub p b
    | .letE _ t v b _ => anySub p t || anySub p v || anySub p b
    | .app f a => anySub p f || anySub p a
    | .proj _ _ b => anySub p b
    | _ => false

/-- `anySub`'s defining equation, in the uniform form.  The generated equation lemmas split on
the constructor and so cannot rewrite under a variable `e`; `eq_def` can. -/
theorem anySub_eq (p : Expr → Bool) (e : Expr) : anySub p e = (p e || match e with
    | .forallE _ d b _ => anySub p d || anySub p b
    | .lam _ d b _ => anySub p d || anySub p b
    | .mdata _ b => anySub p b
    | .letE _ t v b _ => anySub p t || anySub p v || anySub p b
    | .app f a => anySub p f || anySub p a
    | .proj _ _ b => anySub p b
    | _ => false) := by rw [anySub.eq_def]

namespace anySubterm

variable {α β : Type}

/-- `StateM Bool`'s `bind`, projected to the state.  `rfl` by structure eta on the pair. -/
theorem sbind (x : StateM Bool α) (f : α → StateM Bool β) (b : Bool) :
    ((x >>= f) b).2 = ((f (x b).1) (x b).2).2 := rfl

theorem spure (a : α) (b : Bool) : ((pure a : StateM Bool α) b).2 = b := rfl

/-- The callback, run.  It never rewrites: on a hit (or once a hit is recorded) it returns the
node unchanged, purely to prune; otherwise it declines and `replaceNoCacheT` descends. -/
theorem visit_run (p : Expr → Bool) (e : Expr) (b : Bool) :
    (anySubterm.visit p e b) = (if b || p e then (some e, true) else (none, false)) := by
  cases b <;> [skip; simp [anySubterm.visit, StateT.bind, bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure]]
  by_cases hp : p e = true <;>
    simp [anySubterm.visit, StateT.bind, bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, set, MonadStateOf.set, StateT.set, hp]

/-- **The traversal computes `anySub`, from any starting state.**  The generalisation over the
incoming state `b` is what makes the induction go through: a node's two children are run in
sequence, the second starting from whatever the first left. -/
theorem run_visit (p : Expr → Bool) : ∀ (e : Expr) (b : Bool),
    (Lean.Expr.replaceNoCacheT (m := StateM Bool) (anySubterm.visit p) e b).2
      = (b || anySub p e) := by
  have key : ∀ (e : Expr) (b : Bool), (b || p e) = true →
      (Lean.Expr.replaceNoCacheT (m := StateM Bool) (anySubterm.visit p) e b).2
        = (b || anySub p e) := by
    intro e b h
    rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run, if_pos h]
    simp only [spure]
    rw [anySub_eq, ← Bool.or_assoc, h, Bool.true_or]
  intro e
  induction e with
  | app f a ihf iha =>
    intro b
    by_cases h : (b || p (.app f a)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false]
      rw [sbind, sbind, spure, iha, ihf, anySub_eq (e := .app f a)]
      simp [hp]
  | lam n d bd bi ihd ihb =>
    intro b
    by_cases h : (b || p (.lam n d bd bi)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false]
      rw [sbind, sbind, spure, ihb, ihd, anySub_eq (e := .lam n d bd bi)]
      simp [hp]
  | forallE n d bd bi ihd ihb =>
    intro b
    by_cases h : (b || p (.forallE n d bd bi)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false]
      rw [sbind, sbind, spure, ihb, ihd, anySub_eq (e := .forallE n d bd bi)]
      simp [hp]
  | letE n t v bd nd iht ihv ihb =>
    intro b
    by_cases h : (b || p (.letE n t v bd nd)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false]
      rw [sbind, sbind, sbind, spure, ihb, ihv, iht, anySub_eq (e := .letE n t v bd nd)]
      simp [hp, Bool.or_assoc]
  | mdata dt bd ihb =>
    intro b
    by_cases h : (b || p (.mdata dt bd)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false]
      rw [sbind, spure, ihb, anySub_eq (e := .mdata dt bd)]
      simp [hp]
  | proj s i bd ihb =>
    intro b
    by_cases h : (b || p (.proj s i bd)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false]
      rw [sbind, spure, ihb, anySub_eq (e := .proj s i bd)]
      simp [hp]
  | bvar i =>
    intro b
    by_cases h : (b || p (.bvar i)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false, spure]
      rw [anySub_eq (e := .bvar i)]
      simp [hp]
  | fvar i =>
    intro b
    by_cases h : (b || p (.fvar i)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false, spure]
      rw [anySub_eq (e := .fvar i)]
      simp [hp]
  | mvar i =>
    intro b
    by_cases h : (b || p (.mvar i)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false, spure]
      rw [anySub_eq (e := .mvar i)]
      simp [hp]
  | sort u =>
    intro b
    by_cases h : (b || p (.sort u)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false, spure]
      rw [anySub_eq (e := .sort u)]
      simp [hp]
  | const c us =>
    intro b
    by_cases h : (b || p (.const c us)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false, spure]
      rw [anySub_eq (e := .const c us)]
      simp [hp]
  | lit l =>
    intro b
    by_cases h : (b || p (.lit l)) = true
    · exact key _ _ h
    · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      obtain ⟨hb, hp⟩ := h
      subst hb
      rw [Lean.Expr.replaceNoCacheT.eq_def, sbind, visit_run]
      simp only [Bool.false_or, hp, Bool.false_eq_true, if_false, spure]
      rw [anySub_eq (e := .lit l)]
      simp [hp]

end anySubterm

/-- **The checker's occurrence test, specified.**  No axiom, no `opaque`: the right-hand side
is a total structural function of `p` and `e`. -/
theorem anySubterm_eq (p : Expr → Bool) (e : Expr) : anySubterm p e = anySub p e := by
  rw [anySubterm]; exact (anySubterm.run_visit p e false).trans (Bool.false_or _)

/-- `hasIndOcc`, specified.  Note the C++ kernel's `has_ind_occ` asks the same existential
question, so this is a specification of the mirrored check, not of a divergence. -/
theorem hasIndOcc_eq (indConsts : Array Expr) (t : Expr) :
    AddInductive.hasIndOcc indConsts t
      = anySub (fun | .const e _ => indConsts.any fun I => I.constName! == e | _ => false) t :=
  anySubterm_eq ..

/-! ## Destructors

`anySub p e = false` is the hypothesis `checkPositivity`'s success hands over; these are the
projections a consumer needs.  All are `simp`-driven from `anySub_eq`. -/

theorem anySub_self {p : Expr → Bool} {e : Expr} (h : anySub p e = false) : p e = false := by
  rw [anySub_eq] at h; simpa using (Bool.or_eq_false_iff.1 h).1

theorem anySub_app {p : Expr → Bool} {f a : Expr} (h : anySub p (.app f a) = false) :
    anySub p f = false ∧ anySub p a = false := by
  rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h; exact ⟨h.2.1, h.2.2⟩

theorem anySub_forallE {p : Expr → Bool} {n d b bi} (h : anySub p (.forallE n d b bi) = false) :
    anySub p d = false ∧ anySub p b = false := by
  rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h; exact ⟨h.2.1, h.2.2⟩

theorem anySub_lam {p : Expr → Bool} {n d b bi} (h : anySub p (.lam n d b bi) = false) :
    anySub p d = false ∧ anySub p b = false := by
  rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h; exact ⟨h.2.1, h.2.2⟩

theorem anySub_letE {p : Expr → Bool} {n t v b nd} (h : anySub p (.letE n t v b nd) = false) :
    anySub p t = false ∧ anySub p v = false ∧ anySub p b = false := by
  rw [anySub_eq] at h; simp only [Bool.or_eq_false_iff] at h; exact ⟨h.2.1.1, h.2.1.2, h.2.2⟩

theorem anySub_mdata {p : Expr → Bool} {d b} (h : anySub p (.mdata d b) = false) :
    anySub p b = false := by
  rw [anySub_eq] at h; simpa using (Bool.or_eq_false_iff.1 h).2

theorem anySub_proj {p : Expr → Bool} {s i b} (h : anySub p (.proj s i b) = false) :
    anySub p b = false := by
  rw [anySub_eq] at h; simpa using (Bool.or_eq_false_iff.1 h).2

/-! ## From the syntactic check to `VExpr.NoConsts`

`VIndField.WF.pos`'s `none` branch is `∃ A, D.NoBlock A ∧ …`, and `NoBlock` is
`VExpr.NoConsts D.blockNames` — a statement about the **translated** term.  The checker's
evidence is about the **source** term.  The bridge below is the transfer, by induction on
`TrExprS`.

### Three side conditions — investigated, and all three are closed

`TrExprS` is not constant-preserving: two of its rules put constants into the `VExpr` that are
not in the `Expr` at all, and one reads a `VExpr` out of the context rather than out of the
term.  So the transfer needs three hypotheses.  Each was a candidate blindness of `hasIndOcc`
— an occurrence of the block that the syntactic check cannot see, which in a positivity check
is the shape of a real defect.  **All three were investigated and none is reachable.**  What
follows is the reason in each case, because until now none of them was anyone's stated
invariant.

* `hctx` — a `.bvar`/`.fvar` translates to whatever the `VLCtx` maps it to: `.bvar _` for a
  `vlam` entry, but the *value* for a `vlet` entry, which the source variable does not
  display.  **Closed outright** (`VLCtx.noConsts_of_allVLam`): `AddInductive` never calls
  `withLetDecl` — its only binder is `withLocalDecl` — so the context the positivity check
  runs in is all-`vlam`, and `VLCtx.mkFVars` (R1/R2's dictionary) builds exactly such a
  context.  Any `letE` met *inside* the term re-establishes the invariant from the induction
  hypothesis, because `anySub` scans a `letE`'s value (`anySub_letE`).

* `hlit` — `TrExprS.lit` translates `.lit l` through `l.toConstructor`, so a numeral
  introduces `Nat.zero`/`Nat.succ` and a string literal `String.ofList`, `List.nil`,
  `List.cons`, `Char.ofNat`.  `hasIndOcc` sees a `.lit` node and no `.const` node at all, and
  block-name freshness in the *pre-block* environment does not obviously help, because the
  literal is translated at the *staged* environment.  **Closed for numerals**
  (`VInductDecl'.natPrimitives_not_block`) by an invariant that already exists and had not
  been connected to this: `VEnv.HasPrimitives.nat` says `Nat ∈ env → Nat.zero, Nat.succ ∈ env`,
  and `TrExprS.lit`'s own `ContainsLits` premise demands `Nat ∈ env`.  So both constructor
  names are in the pre-block environment, and `VEnv.addConstList_fresh` then forbids the block
  from declaring either.  `VContext.hasPrimitives` is exactly the field that carries this.
  For string literals the same argument runs through `HasPrimitives.charOfNat` /
  `.stringOfList`, which pin those constants' types, and closes except in an environment where
  a primitive's type is *definitionally a sort* — see the note on `anySub_natLit`.

* `hproj` — `TrProj` expands `.proj s i e` into `VInductDecl'.projTerm`, which splices in the
  structure's recursor name, its stored field types, **and the parameter/index arguments `ps`,
  `ιs` read off the type of `e`**.  Those are not syntactically present in `.proj s i e` at
  all, so this was the sharpest candidate: the arguments are *derived* rather than merely
  elided.  **Unreachable**, for the reason recorded under "the positivity scope invariant"
  below, which was checked against both kernels rather than argued on paper.

The residual is proof-side, not kernel-side: `TrProj`'s `ps`/`ιs` are pinned only by
`HasType e ((const S us).mkApp (ps ++ ιs))`, which is closed under conversion, so the
*relation* admits a derivation whose `ps` mentions the block (`[(fun _ => Nat) I]` in place of
`[Nat]`) even though `inferProj` never produces one.  Discharging `hproj` therefore needs
either a canonical-spine strengthening of `TrProj` (a `Theory/` change, not this stream's) or
the observation that `pos` only asks for *some* defeq block-free `A`, so one may re-derive at
the whnf'd spine.

## The positivity scope invariant

Nowhere stated in either kernel, and it is what makes the projection route dead:

> At the point `checkConstructors` checks field `i` of a constructor, **every free variable in
> scope has a type that is either definitionally free of the block's constants, or of the form
> `∀ ξ, I_j p args`.**

`checkPositivity`'s two `throw`s are what maintain it — the `.forallE` branch rejects a block
occurrence in a binder domain, and the final `isValidIndApp?` branch rejects a type whose
head-normal form mentions the block but is not headed by a block constant.  The second
alternative is a **pi**, and a pi is never the type of a projectable term, so a projection
subject always has a definitionally block-free type.  Two supporting facts do the rest:

* **Block-name freshness.**  `addConst` fails on a duplicate, so no constant already in the
  environment mentions a block name.  Hence δ-unfolding during `whnf` can never *introduce* a
  block constant: every block constant in `whnf t` came from `t`.
* **`whnf` is head-only.**  So a block occurrence either survives into an argument of the
  head-normal form — where `hasIndOcc` sees it — or is erased by the reduction, in which case
  it is gone from the type altogether and cannot reach `ps`/`ιs` either.  That dichotomy is
  what makes "visible or absent" exhaustive.

**Checked, not argued.**  Hand-built declarations were fed to `Lean4Lean.addDecl` and to the
C++ kernel (`Lean.Kernel.Environment.addDeclCore` — *not* `Lean.addDecl`, whose checking is
asynchronous and silently defers rejections).  Every route agreed between the two kernels:

| probe | shape | both kernels |
|---|---|---|
| `K0` | `(b : KBox Nat) → b.0 → K0` | **accept** — a projection out of a genuinely *indexed* one-constructor type is legal (`nindices = 0` is never required: `kernel/type_checker.cpp:263`), so the `ιs` route is live in principle |
| `K1` | `(b : KBox (K1 → Nat)) → b.0 → K1` | reject — "non valid occurrence", at the *earlier field* `b` |
| `K3` | β-redex hiding the occurrence *inside* the index | reject — `whnf` is head-only, the occurrence survives |
| `K4` | β-redex over the *whole* field type | **accept** — the occurrence is erased, and the index is then `Nat` |
| `K5` | subject is `f 0` for an earlier `f : Nat → KBox (K5 → Nat)` | reject |
| `K6` | subject is `let`-bound | reject |
| `K7` | occurrence only under a `ξ` binder of a recursive field | reject — "non positive occurrence" |
| `P1`/`P3` | the same via a *parameter* of a structure | reject — the parameter route is taken by nested-inductive elimination first (`isNestedInductiveApp?` scans only `[0:numParams]`, which is why the index route had to be probed separately) |

`K1` versus `K4` is the dichotomy: the occurrence is either seen or absent, never hidden.

One cosmetic divergence, recorded and not a bug: on the `isValidIndApp?` branch lean4lean says
"has a non valid occurrence" where the C++ kernel says "contains a non valid occurrence".
Accept/reject agrees on every probe. -/

theorem VExpr.NoConsts.liftN {S : List Name} {n : Nat} :
    ∀ {e : VExpr} {k : Nat}, e.NoConsts S → (e.liftN n k).NoConsts S
  | .bvar _, _, h | .sort _, _, h | .const .., _, h => h
  | .app .., _, h | .lam .., _, h | .forallE .., _, h => ⟨h.1.liftN, h.2.liftN⟩

/-- Extending the `VLCtx` preserves the "every looked-up value is block-free" invariant, given
that the new entry's own value is.  For a `vlam` that value is `.bvar 0`; for a `vlet` it is the
translated let-value, which the induction supplies. -/
theorem VLCtx.noConsts_cons {S : List Name} {Δ : VLCtx} {ofv} {d : VLocalDecl}
    (hd : VExpr.NoConsts S d.value)
    (h : ∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts S x) :
    ∀ v x A, VLCtx.find? ((ofv, d) :: Δ) v = some (x, A) → VExpr.NoConsts S x := by
  intro v x A hv
  rw [VLCtx.find?] at hv
  split at hv
  · cases hv; exact hd
  · rename_i v' _
    cases hf : Δ.find? v' with
    | none => rw [hf] at hv; exact absurd hv nofun
    | some q => rw [hf] at hv; cases hv; exact (h _ _ _ hf).liftN

/-! ### `hctx`, discharged

`AddInductive` binds with `withLocalDecl` and never with `withLetDecl`, so every context the
positivity check runs in is all-`vlam`, and a `vlam` entry's value is `.bvar 0`. -/

/-- Every declaration in the context is a `vlam` — no let-bindings. -/
def VLCtx.AllVLam : VLCtx → Prop
  | [] => True
  | (_, .vlam _) :: Δ => VLCtx.AllVLam Δ
  | (_, .vlet ..) :: _ => False

/-- **`hctx`, discharged.**  In an all-`vlam` context every looked-up value is a `.bvar`, which
is block-free for any `S` whatsoever. -/
theorem VLCtx.noConsts_of_allVLam {S : List Name} :
    ∀ {Δ : VLCtx}, Δ.AllVLam → ∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts S x
  | [], _ => by intro _ _ _ h; exact absurd h nofun
  | (_, .vlam _) :: Δ, hΔ => VLCtx.noConsts_cons trivial (VLCtx.noConsts_of_allVLam hΔ)

/-- The only case that consumes `hpS`: a source constant translates to the same constant, so
the syntactic miss is the abstract miss. -/
theorem noConsts_const {S : List Name} {p : Expr → Bool} {c : Name} {us : List Lean.Level}
    {us' : List VLevel} (hpS : ∀ c us, c ∈ S → p (.const c us) = true)
    (h : anySub p (.const c us) = false) : VExpr.NoConsts S (.const c us') := by
  show c ∉ S
  intro hc
  have h2 := anySub_self h
  rw [hpS c us hc] at h2
  exact absurd h2 nofun

/-- **The transfer.**  Sorry-free and axiom-clean; every gap is an explicit hypothesis.
See the section note for what each hypothesis records. -/
theorem TrExprS.noConsts {env : VEnv} {Us : List Name} {S : List Name} {p : Expr → Bool}
    (hpS : ∀ c us, c ∈ S → p (.const c us) = true)
    (hlit : ∀ l : Lean.Literal, anySub p l.toConstructor = false)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConsts S x → VExpr.NoConsts S y) :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, TrExprS env Us Δ e e' →
      (∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConsts S x) →
      anySub p e = false → VExpr.NoConsts S e' := by
  intro Δ e e' H
  induction H with
  | bvar h => exact fun hctx _ => hctx _ _ _ h
  | fvar h => exact fun hctx _ => hctx _ _ _ h
  | sort => exact fun _ _ => trivial
  | const _ _ _ => exact fun _ h => noConsts_const hpS h
  | app _ _ _ _ ihf iha =>
    intro hctx h
    exact ⟨ihf hctx (anySub_app h).1, iha hctx (anySub_app h).2⟩
  | lam _ _ _ ihd ihb =>
    intro hctx h
    refine ⟨ihd hctx (anySub_lam h).1, ihb ?_ (anySub_lam h).2⟩
    exact VLCtx.noConsts_cons trivial hctx
  | forallE _ _ _ _ ihd ihb =>
    intro hctx h
    refine ⟨ihd hctx (anySub_forallE h).1, ihb ?_ (anySub_forallE h).2⟩
    exact VLCtx.noConsts_cons trivial hctx
  | letE _ _ _ _ iht ihv ihb =>
    intro hctx h
    obtain ⟨_, hv, hb⟩ := anySub_letE h
    exact ihb (VLCtx.noConsts_cons (ihv hctx hv) hctx) hb
  | lit _ _ ih => exact fun hctx _ => ih hctx (hlit _)
  | mdata _ ih => exact fun hctx h => ih hctx (anySub_mdata h)
  | proj _ hp ih => exact fun hctx h => hproj _ _ _ _ _ hp (ih hctx (anySub_proj h))

/-! ### `hlit`, discharged for numerals

The route nobody had connected: `TrExprS.lit`'s own `ContainsLits` premise demands `Nat` be
declared, `VEnv.HasPrimitives.nat` then forces `Nat.zero` and `Nat.succ` to be declared **in
the same environment**, and `VEnv.addConstList_fresh` forbids the block from declaring a name
that is already there.  So the two constants a numeral expands into can never be block names,
and `anySub_natLit` applies.  `VContext.hasPrimitives` is the field that carries the premise. -/

/-- A name already in the environment is not one the block declares — `addIndTypes` succeeding
means every block name was fresh. -/
theorem VInductDecl'.not_mem_blockNames {env env₁ : VEnv} {D : VInductDecl'} {n : Name}
    (h : env.addIndTypes D = some env₁) (hn : env.contains n) : n ∉ D.blockNames := by
  intro hmem
  have hfresh := (VEnv.addConstList_fresh h).1 n (D.typeConsts_names ▸ hmem)
  obtain ⟨_, hci⟩ := hn
  rw [hci] at hfresh; exact absurd hfresh nofun

/-- **`hlit`'s premise, discharged for numerals.**  Neither `Nat.zero` nor `Nat.succ` can be a
block name in any environment where a numeral literal can be translated at all. -/
theorem VInductDecl'.natPrimitives_not_block {env env₁ : VEnv} {D : VInductDecl'}
    (hp : env.HasPrimitives) (h : env.addIndTypes D = some env₁) (hnat : env.contains ``Nat) :
    ``Nat.zero ∉ D.blockNames ∧ ``Nat.succ ∉ D.blockNames :=
  let ⟨h0, h1⟩ := hp.nat hnat
  ⟨VInductDecl'.not_mem_blockNames h h0, VInductDecl'.not_mem_blockNames h h1⟩

/-! ### The hypotheses bite, and are satisfiable

Two positive checks.  The first is not merely a check — it is the connector the caller needs,
since `hasIndOcc`'s predicate is phrased over an `Array Expr` of `.const` nodes while
`NoConsts` is phrased over a `List Name`.  The second exhibits `hlit` holding non-vacuously
for numerals, and shows exactly which two names a block may not steal. -/

/-- `hpS`, discharged for the checker's own predicate: if every name of `S` is the head of one
of `stats.indConsts`, the predicate fires on it. -/
theorem hasIndOcc_hpS {indConsts : Array Expr} {S : List Name}
    (hS : ∀ c ∈ S, ∃ I ∈ indConsts, I.constName! = c) (c : Name) (us : List Lean.Level)
    (hc : c ∈ S) :
    (fun e => match e with
      | .const e _ => indConsts.any fun I => I.constName! == e
      | _ => false) (Lean.Expr.const c us) = true := by
  obtain ⟨I, hI, hIc⟩ := hS c hc
  show (indConsts.any fun I => I.constName! == c) = true
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hI
  exact Array.any_eq_true.2 ⟨i, hi, by simp [hIc]⟩

/-- `hlit` holds for numerals as soon as the block steals neither `Nat.zero` nor `Nat.succ`.
`Literal.toConstructor` is *not* fully expanded — `natLitToConstructor (n+1)` is
`.app (.const Nat.succ []) (.lit (.natVal n))` — so this is a finite check, with no induction
on `n` and no dependence on how deep the numeral is. -/
theorem anySub_natLit {p : Expr → Bool}
    (hp : ∀ e : Lean.Expr, p e = true → ∃ c us, e = .const c us)
    (h0 : p (.const ``Nat.zero []) = false) (h1 : p (.const ``Nat.succ []) = false) (n : Nat) :
    anySub p (Lean.Literal.toConstructor (.natVal n)) = false := by
  have hne : ∀ e : Lean.Expr, (∀ c us, e ≠ .const c us) → p e = false := by
    intro e he
    cases hh : p e with
    | false => rfl
    | true => obtain ⟨c, us, rfl⟩ := hp e hh; exact absurd rfl (he c us)
  cases n with
  | zero =>
    show anySub p (.const ``Nat.zero []) = false
    rw [anySub_eq]; simpa using h0
  | succ n =>
    have hc : anySub p (Lean.Expr.const ``Nat.succ []) = false := by
      rw [anySub_eq]; simpa using h1
    have hlp : p (Lean.Expr.lit (.natVal n)) = false := hne _ (by simp)
    have hl : anySub p (Lean.Expr.lit (.natVal n)) = false := by
      rw [anySub_eq]; simpa using hlp
    have happ : p ((Lean.Expr.const ``Nat.succ []).app (.lit (.natVal n))) = false :=
      hne _ (by simp)
    show anySub p (.app (.const ``Nat.succ []) (.lit (.natVal n))) = false
    rw [anySub_eq]; simp [happ, hc, hl]

namespace AddInductive
open Kernel

variable {α β : Type}

/-- `x` succeeds only with results satisfying `Q`.  Failure is unconstrained: the kernel
rejecting a declaration is always sound, so a refinement statement never has to say anything
about the error branch. -/
def M.WF (c : Context) (x : M α) (Q : α → Prop) : Prop := ∀ a, x c = .ok a → Q a

theorem M.WF.pure {c : Context} {Q : α → Prop} (H : Q a) : (pure a : M α).WF c Q := by
  rintro _ ⟨⟩; exact H

theorem M.WF.throw {c : Context} {Q : α → Prop} {e} : (throw e : M α).WF c Q := nofun

theorem M.WF.bind {c : Context} {x : M α} {f : α → M β} {Q R}
    (h1 : x.WF c Q) (h2 : ∀ a, Q a → (f a).WF c R) : (x >>= f).WF c R := by
  intro b eq
  replace eq : (x c >>= fun a => f a c) = .ok b := eq
  cases hx : x c with
  | error => rw [hx] at eq; exact absurd eq nofun
  | ok a => rw [hx] at eq; exact h2 a (h1 a hx) b eq

theorem M.WF.mono {c : Context} {x : M α} {Q R}
    (h1 : x.WF c Q) (h2 : ∀ a, Q a → R a) : x.WF c R := fun a e => h2 a (h1 a e)

theorem M.WF.map {c : Context} {x : M α} {f : α → β} {Q R}
    (h1 : x.WF c Q) (h2 : ∀ a, Q a → R (f a)) : (f <$> x).WF c R := by
  rw [map_eq_pure_bind]; exact h1.bind fun _ h => .pure (h2 _ h)

/-- `read`, as a `WF` rule: the context is the one the statement is about. -/
theorem M.WF.read {c : Context} {Q : Context → Prop} (H : Q c) : (read : M Context).WF c Q := by
  rintro _ ⟨⟩; exact H

theorem M.WF.getLCtx {c : Context} {Q : LocalContext → Prop} (H : Q c.lctx) :
    (getLCtx : M LocalContext).WF c Q := by rintro _ ⟨⟩; exact H

/-- `withReader`, as a `WF` rule: the body is verified against the modified context. -/
theorem M.WF.withReader {c : Context} {f : Context → Context} {x : M α} {Q}
    (h : x.WF (f c) Q) : (withReader f x : M α).WF c Q := h

/-- A pure `Except` computation lifts with its own postcondition. -/
theorem M.WF.liftExcept {c : Context} {x : Except Exception α} {Q}
    (h : ∀ a, x = .ok a → Q a) : (liftM x : M α).WF c Q := by
  intro a eq; exact h a eq

/-! ## The `for` rule

`checkConstructors` and `declareConstructors` are `for` loops over the block's types and
constructors, so the framework needs the same loop-invariant rule the type checker's does.
Indexed by the list still to be processed, so `Inv []` records that every element was handled. -/

theorem M.WF.forIn {c : Context} {f : α → β → M (ForInStep β)} {Inv : List α → β → Prop}
    (H : ∀ a as b, Inv (a :: as) b →
      (f a b).WF c fun r => ∃ b', r = .yield b' ∧ Inv as b') :
    ∀ {xs : List α} {b : β}, Inv xs b → (forIn xs b f).WF c fun b' => Inv [] b'
  | [], _, h => .pure h
  | a :: as, b, h => by
    rw [List.forIn_cons]
    refine (H a as b h).bind fun r hr => ?_
    obtain ⟨b', rfl, hinv⟩ := hr
    exact M.WF.forIn H hinv

/-! ## A1: the abstract context

`AddInductive.Context` carries the kernel environment, a `LocalContext`, the level parameters
and a `NameGenerator`.  Its abstract counterpart carries the `VEnv`, the `VLCtx`, and the
invariants tying them.

**It does not use `MLCtx`.**  The type checker's `VContext` stores an `MLCtx` and *derives*
`trlctx` from `MLCtx.WF`; `MLCtx` is that framework's plumbing for `withMLC`, not the context's
content.  Carrying `TrLCtx` directly gives the same context — and `TrLCtx` lives in
`Verify/LocalContext.lean`, so this section never needed `MLCtx` at all.

**The `reserves` field is the invariant that did *not* disappear with the state.**  See its
docstring: the type checker keeps its `NameGenerator` in state, so freshness lives in
`VState.WF`; `AddInductive.M` keeps it in the reader, so the obligation moves into the context.
Deleting a mechanism does not delete what it was maintaining. -/

/-- The abstract counterpart of `AddInductive.Context`. -/
structure VContext extends Context where
  venv : VEnv
  /-- Carried because `TypeChecker.VContext` requires them, and A5 must build one. -/
  hasPrimitives : VEnv.HasPrimitives venv
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  trenv : TrEnv safety env venv
  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv lparams
  lctx_eq : mlctx.lctx = lctx
  /-- **The relocated freshness invariant.**  The type checker keeps its `NameGenerator` in
  *state*, so freshness lives in `VState.WF`.  `AddInductive.M` keeps it in the *reader*
  (`withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }`), so the obligation does
  not disappear with the state — it moves here.

  Stated over `vlctx.fvars` rather than `lctx.find?`: `TrLCtx` ties the two
  (`TrLCtx.find?_eq_none`), and the `VLCtx` side has the `cons` simp lemmas that make the
  push case one line. -/
  reserves : ∀ fv ∈ mlctx.vlctx.fvars, ngen.Reserves fv
  /-- **Created by composition, not relocated.**  The bridge to the type checker (A5) runs it
  at a *fresh* state, whose generator reserves nothing.  So the type checker's `ngen_wf`
  obligation can only be met by knowing our fvars are not *its* fvars — a fact neither
  framework ever needed, because the two generators had never met.  `fvars_mint` says every
  fvar here was minted by our generator; `prefix_ne` says our generator is not the kernel's. -/
  fvars_mint : ∀ fv ∈ mlctx.vlctx.fvars, ∃ i, fv = ⟨.num ngen.namePrefix i⟩
  prefix_ne : ngen.namePrefix ≠ `_kernel_fresh

@[simp] abbrev VContext.vlctx (c : VContext) := c.mlctx.vlctx

/-- `TrLCtx` is *derived*, not stored — it is the content, and `MLCtx.WF` implies it. -/
theorem VContext.trlctx (c : VContext) : TrLCtx c.venv c.lparams c.lctx c.vlctx :=
  c.lctx_eq ▸ c.mlctx_wf.tr

nonrec abbrev VContext.TrExprS (c : VContext) : Expr → VExpr → Prop :=
  TrExprS c.venv c.lparams c.vlctx
nonrec abbrev VContext.TrExpr (c : VContext) : Expr → VExpr → Prop :=
  TrExpr c.venv c.lparams c.vlctx
nonrec abbrev VContext.IsType (c : VContext) : VExpr → Prop :=
  c.venv.IsType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.HasType (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.HasType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.IsDefEqU (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx

/-- The local context is well-formed, from the translation. -/
theorem VContext.lctx_wf (c : VContext) : c.lctx.WF := c.trlctx.1

/-- The fresh id is not already declared — the analogue of `VState.WF.find?_eq_none`, derived
from the relocated invariant instead of from the state. -/
theorem VContext.fresh (c : VContext) : c.lctx.find? ⟨c.ngen.curr⟩ = none :=
  c.trlctx.find?_eq_none.2 fun h => c.ngen.not_reserves_self (c.reserves _ h)

/-- **Extending the context with a fresh binder.**  The shape all 13 `withLocalDecl` uses have.
`ngen` advances, so `reserves` is re-established by `Reserves.mono` on the tail and
`next_reserves_self` on the new id. -/
def VContext.push (c : VContext) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo)
    (htr : c.TrExprS ty ty') (hty : c.IsType ty') : VContext :=
  { c with
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
    ngen := c.ngen.next
    mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi c.mlctx
    mlctx_wf := ⟨c.mlctx_wf, c.lctx_eq ▸ c.fresh, htr, hty⟩
    lctx_eq := by rw [TypeChecker.MLCtx.lctx, c.lctx_eq]
    reserves := by
      intro fv hfv
      rw [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons] at hfv
      rcases hfv with rfl | hfv
      · exact NameGenerator.next_reserves_self
      · exact (c.reserves fv hfv).mono NameGenerator.LE.next
    fvars_mint := by
      intro fv hfv
      rw [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons] at hfv
      rcases hfv with rfl | hfv
      · exact ⟨c.ngen.idx, rfl⟩
      · exact c.fvars_mint fv hfv
    prefix_ne := c.prefix_ne }

@[simp] theorem VContext.push_lctx (c : VContext) {name ty ty' bi htr hty} :
    (c.push name ty ty' bi htr hty).lctx = c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi := rfl

@[simp] theorem VContext.push_ngen (c : VContext) {name ty ty' bi htr hty} :
    (c.push name ty ty' bi htr hty).ngen = c.ngen.next := rfl

@[simp] theorem VContext.push_venv (c : VContext) {name ty ty' bi htr hty} :
    (c.push name ty ty' bi htr hty).venv = c.venv := rfl

@[simp] theorem VContext.push_lparams (c : VContext) {name ty ty' bi htr hty} :
    (c.push name ty ty' bi htr hty).lparams = c.lparams := rfl

/-- The pushed context's `VLCtx`, spelled out.  Used by the loop invariant to re-establish the
`VLCtx.mkFVars` shape one binder at a time. -/
@[simp] theorem VContext.push_vlctx' (c : VContext) {name ty ty' bi htr hty} :
    (c.push name ty ty' bi htr hty).vlctx
      = (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') :: c.vlctx := rfl

/-- The environment is well formed; `AddInductive.VContext`'s analogue of
`TypeChecker.VContext.Ewf`. -/
theorem VContext.Ewf (c : VContext) : VEnv.WF c.venv := c.trenv.wf

/-- The fresh id is genuinely fresh among the abstract context's fvars — the `VLCtx`-side form
of `VContext.fresh`, which is what maintains the loop invariant's `Nodup`. -/
theorem VContext.curr_not_mem (c : VContext) : (⟨c.ngen.curr⟩ : FVarId) ∉ c.vlctx.fvars :=
  fun h => c.ngen.not_reserves_self (c.reserves _ h)

/-! ## A3′: the annotation-stripping rule

`AddInductive.consumeAnnotations` replaced the body-less `Lean.Expr.consumeTypeAnnotations` in
`Lean4Lean/Inductive/Add.lean`, so for the first time this step **has a body to unfold**.  The
rule below is the payoff: the `isAnnotation e = false` branch returns the input *verbatim*, so
the `hcta` obligation collapses on every binder that carries no annotation — measured at ~98%
of the constructor binder domains of a real environment.  What is left is exactly the
annotated case, where `optParam α d` really is only *definitionally* `α`. -/

theorem M.WF.consumeAnnotations {c : Context} {e : Expr} {Q : Expr → Prop}
    (hid : isAnnotation e = false → Q e)
    (hann : isAnnotation e = true →
      Q (Nat.repeat stripAnnotation c.fuel.inductiveFuel e)) :
    M.WF c (AddInductive.consumeAnnotations e) Q := by
  intro a ha
  rw [AddInductive.consumeAnnotations] at ha
  by_cases h : isAnnotation e = true
  · rw [if_pos h] at ha
    split at ha
    · exact absurd ha nofun
    · cases ha; exact hann h
  · simp only [Bool.not_eq_true] at h
    rw [if_neg (by simp [h])] at ha
    cases ha; exact hid h

/-- The un-annotated case in isolation: `consumeAnnotations` is the identity.  Stated
separately because it is what makes the residual obligation *narrow* rather than merely
*stated* — a hypothesis that is false but vacuous almost everywhere reads very differently
from one that is false and always in play. -/
theorem M.WF.consumeAnnotations_id {c : Context} {e : Expr} (h : isAnnotation e = false) :
    M.WF c (AddInductive.consumeAnnotations e) (· = e) :=
  M.WF.consumeAnnotations (fun _ => rfl) (fun h' => absurd (h ▸ h') nofun)

/-! ## A3: the binder rule

`withLocalDecl` (`Lean4Lean/LocalContext.lean`) is
`withFreshId fun id => withReader (·.mkLocalDecl ⟨id⟩ name ty bi) (k (.fvar ⟨id⟩))`, and
`AddInductive`'s two instances make that run the body at exactly `VContext.push`'s context:
`withFreshId` supplies `c.ngen.curr` and advances the generator, `withReader` extends the local
context.  So the rule is `rfl` on the context and the content is `push`'s obligations. -/

theorem M.WF.withLocalDecl {c : VContext} {name : Name} {bi : BinderInfo} {ty : Expr}
    {ty' : VExpr} {k : Expr → M α} {Q : α → Prop}
    (htr : c.TrExprS ty ty') (hty : c.IsType ty')
    (H : (k (.fvar ⟨c.ngen.curr⟩)).WF (c.push name ty ty' bi htr hty).toContext Q) :
    (withLocalDecl name bi ty k).WF c.toContext Q := H

/-! ## A5: the bridge to the verified type checker

`AddInductive.M` reaches `checkType`, `whnf`, `isDefEq`, `ensureSort` and `ensureType` through

    instance : MonadLift TypeChecker.M M where
      monadLift x c := x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel)

The lift **runs a fresh type-checker state and discards it**.  So the existing `.WF` lemmas —
whose postconditions are `α → VState → Prop` — transfer with the state existentially dropped,
rather than needing a state-compatible restatement.  That is what makes the bridge one lemma.

**What the bridge does not launder.**  `inferType.WF` and `isDefEq.WF` close their
`.inductInfo` cases with `TrEnv.not_inductInfo` (`InferType.lean:472`, `IsDefEq.lean:514`),
which holds *only while* `AddInduct` has no constructors.  Both files say so in their own
docstrings.  So the lemmas are true and their statements have content, but part of their
current proof is vacuous **for exactly the declarations `AddInductive` adds** — the bridge is
sound, and what it delivers is conditional on that debt being paid.  A clean `#print axioms`
does not see this; only reading the proof does. -/

/-- The type checker's abstract context, built from ours.  Everything it needs we now carry;
`ngen` and `allowPrimitive` are ours alone and it does not use them. -/
def VContext.toTC (c : VContext) : TypeChecker.VContext where
  toContext :=
    { env := c.env, safety := c.safety, lctx := c.lctx, lparams := c.lparams, fuel := c.fuel }
  venv := c.venv
  hasPrimitives := c.hasPrimitives
  safePrimitives := c.safePrimitives
  trenv := c.trenv
  mlctx := c.mlctx
  mlctx_wf := c.mlctx_wf
  lctx_eq := c.lctx_eq

/-- Our fvars are reserved by the type checker's *fresh* generator — vacuously, because they
carry a different prefix.  This is the obligation composition manufactured. -/
theorem VContext.reserves_kernel (c : VContext) {fv : FVarId}
    (h : fv ∈ c.vlctx.fvars) : ({} : TypeChecker.VState).ngen.Reserves fv := by
  intro i hi
  obtain ⟨j, hj⟩ := c.fvars_mint fv h
  rw [hj] at hi
  simp only [FVarId.mk.injEq, Name.num.injEq] at hi
  exact absurd hi.1 c.prefix_ne

/-- The type checker's state invariant at the fresh state.  Every cache is empty; the context
invariant is ours; the generator condition is `reserves_kernel`. -/
theorem VContext.toTC_state_wf (c : VContext) :
    TypeChecker.VState.WF c.toTC {} where
  trctx := c.mlctx_wf.tr
  ngen_wf _ h := c.reserves_kernel h
  ectx := ⟨_, _, c.mlctx_wf.tr.wf, .refl, .empty, fun _ h => c.reserves_kernel h⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

/-- **A5, at the `Except` level.**  Running the type checker from our context, at a fresh
state, and discarding it.  Mirrors `TypeChecker.M.WF.run1`, which pins `lctx := {}`; ours
runs at the local context we have actually built. -/
theorem VContext.run_WF {c : VContext} {x : TypeChecker.M α} {Q : α → Prop}
    (h : TypeChecker.M.WF c.toTC {} x fun a _ => Q a) :
    ∀ a, TypeChecker.M.run c.env c.safety c.lctx c.lparams (fuel := c.fuel) x = .ok a → Q a := by
  intro a eq
  simp [TypeChecker.M.run, Functor.map, Except.map] at eq
  split at eq <;> cases eq; rename_i eq
  let ⟨_, _, _, _, H⟩ := h c.toTC_state_wf _ _ eq
  exact H

/-- **A5.**  A verified type-checker computation, lifted into `AddInductive.M`.  The
postcondition transfers with the type checker's state existentially dropped, because the lift
runs a fresh state and discards it — which is why this is one lemma rather than a
state-compatible restatement of every phase. -/
theorem M.WF.liftTC {c : VContext} {x : TypeChecker.M α} {Q : α → Prop}
    (h : TypeChecker.M.WF c.toTC {} x fun a _ => Q a) :
    M.WF c.toContext (liftM x) Q := VContext.run_WF h

/-! ## A4: the environment-change rule

`withEnv env x = withReader (fun c => { c with env }) x`, so the *combinator* half is
`M.WF.withReader` and costs nothing.  All the content is in rebuilding the `VContext` at the
new environment.

**Row zero, run against the prediction "is there an invariant that neither side maintains once
they are composed?".  Answer: yes — `mlctx_wf`.**

- The **type checker** never changes its environment.  `Lean4Lean/TypeChecker.lean` has no
  `withEnv`; its only `env :=` is inside a commented-out line (994) and `M.run`'s initial
  record.  So `MLCtx.WF`'s behaviour under a growing `VEnv` is a question that framework never
  had to ask, and `MLCtx.WF.mono` does not exist in the tree.
- The **adder** changes its environment twice (`Inductive/Add.lean:469, 471`) but has no
  local-context invariant to maintain: `LocalContext` does not mention `env`.

Composed, `checkInductiveTypes` binds `stats` — whose `params`, `indConsts` and `lctx` are
fvars checked at the *old* environment — and `run` then carries them under two `withEnv`s.  So
a context built and verified at `venv` is used at `venv'`, and that is precisely the obligation
neither framework owned.  `TrExprS.mono` (`Verify/Typing/Lemmas.lean:723`) exists, but only for
single expressions; the context-level lifting below is new.

`hasPrimitives`, `safePrimitives` and `trenv` are *hypotheses* here rather than derived:
`HasPrimitives.extend` (`Verify/Primitive.lean:728`) transfers across an extension with exactly
one new constant, and the adder adds a whole block.  The caller (R12) holds these from the
`TrEnv` extension lemmas. -/

/-- **Environment-monotonicity of the type checker's context invariant.**  Absent upstream
because the type checker never changes environments; see the A4 note. -/
theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.mono {env env' : VEnv} {Us : List Name}
    (henv : env ≤ env') :
    ∀ {c : TypeChecker.MLCtx}, c.WF env Us → c.WF env' Us
  | .nil, h => h
  | .vlam .., ⟨h1, h2, h3, h4⟩ => ⟨h1.mono henv, h2, h3.mono henv, h4.mono henv⟩
  | .vlet .., ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1.mono henv, h2, h3.mono henv, h4.mono henv, h5.mono henv⟩

/-- **The abstract context, moved to a larger environment.**  Only `mlctx_wf` needs work; the
freshness fields are environment-free, and the three environment facts are supplied by the
caller because the adder's extension adds many constants at once. -/
def VContext.withEnv (c : VContext) (env' : Environment) (venv' : VEnv)
    (hle : c.venv ≤ venv') (hprim : VEnv.HasPrimitives venv')
    (hsafe : ∀ {n ci}, env'.find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (htr : TrEnv c.safety env' venv') : VContext :=
  { c with
    env := env'
    venv := venv'
    hasPrimitives := hprim
    safePrimitives := hsafe
    trenv := htr
    mlctx_wf := c.mlctx_wf.mono hle }

@[simp] theorem VContext.withEnv_lctx (c : VContext) {env' venv' hle hprim hsafe htr} :
    (c.withEnv env' venv' hle hprim hsafe htr).lctx = c.lctx := rfl

@[simp] theorem VContext.withEnv_ngen (c : VContext) {env' venv' hle hprim hsafe htr} :
    (c.withEnv env' venv' hle hprim hsafe htr).ngen = c.ngen := rfl

@[simp] theorem VContext.withEnv_vlctx (c : VContext) {env' venv' hle hprim hsafe htr} :
    (c.withEnv env' venv' hle hprim hsafe htr).vlctx = c.vlctx := rfl

/-- **A4.**  `withEnv` runs its body in the context moved to the new environment. -/
theorem M.WF.withEnv {c : VContext} {x : M α} {Q : α → Prop} {env' venv' hle hprim hsafe htr}
    (h : x.WF (c.withEnv env' venv' hle hprim hsafe htr).toContext Q) :
    (AddInductive.withEnv env' x).WF c.toContext Q := h

/-! ## A6: `getEnv`, and the `StateT Nat` layer

**Row zero.**  `getEnv` is not a rule of `AddInductive.M` at all: `Inductive/Add.lean` opens
`TypeChecker`, so the `getEnv` at lines 203 and 483 is `TypeChecker.getEnv` reaching `M`
through the `MonadLift` instance.  It could therefore go through `M.WF.liftTC`, but that
would drag in the whole `VState.WF` bridge to read a reader field, so it gets its own
one-line rule.

The `StateT Nat` layer (`Inductive/Add.lean:482`, wrapping the recursor loop; the state is
`mkRecRules`' `minorIdx`) is a second monad and would ordinarily need a second combinator
family with its own state discipline.  It does not, because **no postcondition in this
development mentions the counter**: `minorIdx` only picks which minor premise a recursor rule
refers to, and that is checked structurally, not through the counter's value.  So `SM.WF`
quantifies over the incoming state and discards the outgoing one, and every rule below is the
`M.WF` rule with an extra `intro n`.  `run'` is then definitional. -/

/-- `getEnv`, as a `WF` rule.  The environment is the reader's. -/
theorem M.WF.getEnv {c : Context} {Q : Environment → Prop} (H : Q c.env) :
    (liftM TypeChecker.getEnv : M Environment).WF c Q := by rintro _ ⟨⟩; exact H

/-- Positive check that the rule fires on the term the source actually writes: at
`Inductive/Add.lean:203` and `:483`, `getEnv` is `TypeChecker.getEnv` reaching `M` through the
`MonadLift` instance, and this `example` elaborates it in exactly that way. -/
example (c : Context) : M.WF c (TypeChecker.getEnv : M Environment) (· = c.env) :=
  M.WF.getEnv rfl

/-- Positive check that A4's rule fires on `Inductive/Add.lean`'s own combinator (line 54),
at the two call sites' shape (lines 469, 471). -/
example (c : VContext) (env' : Environment) (venv' : VEnv) (hle : c.venv ≤ venv')
    (hprim : VEnv.HasPrimitives venv')
    (hsafe : ∀ {n ci}, env'.find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (htr : TrEnv c.safety env' venv') :
    M.WF c.toContext (AddInductive.withEnv env' (TypeChecker.getEnv : M Environment))
      (· = env') :=
  M.WF.withEnv (hle := hle) (hprim := hprim) (hsafe := hsafe) (htr := htr) (M.WF.getEnv rfl)

/-- The `StateT Nat` analogue of `M.WF`.  Universally quantified over the incoming counter and
silent about the outgoing one — see the A6 note for why that is enough. -/
def SM.WF (c : Context) (x : StateT Nat M α) (Q : α → Prop) : Prop :=
  ∀ n a n', x n c = .ok (a, n') → Q a

theorem SM.WF.pure {c : Context} {Q : α → Prop} (H : Q a) :
    SM.WF c (pure a : StateT Nat M α) Q := by
  rintro _ _ _ ⟨⟩; exact H

theorem SM.WF.throw {c : Context} {Q : α → Prop} {e} :
    SM.WF c (throw e : StateT Nat M α) Q := nofun

theorem SM.WF.bind {c : Context} {x : StateT Nat M α} {f : α → StateT Nat M β} {Q R}
    (h1 : SM.WF c x Q) (h2 : ∀ a, Q a → SM.WF c (f a) R) : SM.WF c (x >>= f) R := by
  intro n b n' eq
  replace eq : (x n c >>= fun p => f p.1 p.2 c) = .ok (b, n') := eq
  cases hx : x n c with
  | error => rw [hx] at eq; exact absurd eq nofun
  | ok p => rw [hx] at eq; exact h2 p.1 (h1 n p.1 p.2 hx) _ _ _ eq

theorem SM.WF.mono {c : Context} {x : StateT Nat M α} {Q R}
    (h1 : SM.WF c x Q) (h2 : ∀ a, Q a → R a) : SM.WF c x R :=
  fun n a n' e => h2 a (h1 n a n' e)

theorem SM.WF.map {c : Context} {x : StateT Nat M α} {f : α → β} {Q R}
    (h1 : SM.WF c x Q) (h2 : ∀ a, Q a → R (f a)) : SM.WF c (f <$> x) R := by
  rw [map_eq_pure_bind]; exact h1.bind fun _ h => .pure (h2 _ h)

/-- An `M` computation lifted into the counter layer keeps its postcondition. -/
theorem SM.WF.lift {c : Context} {x : M α} {Q} (h : x.WF c Q) :
    SM.WF c (liftM x : StateT Nat M α) Q := by
  intro n a n' eq
  replace eq : (x c >>= fun a => .ok (a, n)) = .ok (a, n') := eq
  cases hx : x c with
  | error => rw [hx] at eq; exact absurd eq nofun
  | ok b => rw [hx] at eq; cases eq; exact h _ hx

theorem SM.WF.forIn {c : Context} {f : α → β → StateT Nat M (ForInStep β)}
    {Inv : List α → β → Prop}
    (H : ∀ a as b, Inv (a :: as) b →
      SM.WF c (f a b) fun r => ∃ b', r = .yield b' ∧ Inv as b') :
    ∀ {xs : List α} {b : β}, Inv xs b → SM.WF c (forIn xs b f) fun b' => Inv [] b'
  | [], _, h => .pure h
  | a :: as, b, h => by
    rw [List.forIn_cons]
    refine (H a as b h).bind fun r hr => ?_
    obtain ⟨b', rfl, hinv⟩ := hr
    exact SM.WF.forIn H hinv

/-- **A6.**  Running the counter layer and discarding the counter.  Definitional, because
`SM.WF` was already stated with the outgoing state discarded. -/
theorem M.WF.stateT_run' {c : Context} {x : StateT Nat M α} {Q} {n : Nat}
    (h : SM.WF c x Q) : (StateT.run' x n : M α).WF c Q := by
  intro a eq
  replace eq : (x n c >>= fun p => .ok p.1) = .ok a := eq
  cases hx : x n c with
  | error => rw [hx] at eq; exact absurd eq nofun
  | ok p => rw [hx] at eq; cases eq; exact h n p.1 p.2 hx

/-! # Part II: the checker's phases against `VInductDecl'.WF`

The framework above exists to state, for each phase of `Lean4Lean/Inductive/Add.lean`, which
clause of `VInductDecl'.WF` its success establishes.  Three phases are covered here.

**Inherited debt, stated once.**  Every one of these calls into the type checker, and
`TypeChecker.ensureType.WF`, `checkType.WF`, `isDefEq.WF`, `whnf.WF` are all `sorryAx`-tainted
through the five declared `sorry`s in `Verify/TypeChecker/{InferType,IsDefEq,WHNF}.lean`
(PLAN.md's projection / ι-reduction / structure-eta gaps).  The taint is *real*, not error
recovery: `Verify/TypeChecker*` builds with zero errors.  So the rows below are **complete but
not clean**; they become unconditional exactly when those five close, and nobody should read
"R6–R8 done" as unconditional.  The framework itself (Part I) is `sorryAx`-free.

## R6: the field's recorded level and level bound

`checkConstructors` (`Add.lean:225–227`) does, for each non-parameter argument:

```
let s ← ensureType dom
unless stats.resultLevel.isAlwaysZero || stats.resultLevel.geq' s.sortLevel! do throw …
```

Success gives exactly the two clauses of `VIndField.WF` that **do not mention `recArg`** —
`hasType` and `level` — so R6 is independent of R7, and neither has to wait for the other. -/

/-- `ensureType`, lifted into `AddInductive.M`.  The existential is `ensureType.WF`'s own: it
re-derives a translation of `e` rather than reusing the one handed in, and pinning the two
together needs `TrExprS.uniq`, which yields an `IsDefEqU` rather than an equality.  Leaving it
existential costs nothing here, because R1/R2 pin the recorded field type anyway. -/
theorem M.WF.ensureType {c : VContext} {e : Expr} {e' : VExpr} (he : c.TrExprS e e') :
    M.WF c.toContext (liftM (TypeChecker.ensureType e)) fun s =>
      ∃ e'' u u', c.TrExprS e e'' ∧ s = .sort u ∧
        VLevel.ofLevel c.lparams u = some u' ∧ c.HasType e'' (.sort u') :=
  M.WF.liftTC ((TypeChecker.ensureType.WF (c := c.toTC) (s := {}) he).mono
    fun _ _ _ ⟨e'', h1, u, u', h2, h3, h4⟩ => ⟨e'', u, u', h1, h2, h3, h4⟩)

/-- **The pure half of R6.**  The kernel's F6 guard is *strictly stronger* than Carneiro's
`imax ℓ ℓ' ≤ ℓ'` (see `Theory/Inductive/Decl.lean`, `VIndField.WF.level`), and both of its
disjuncts imply it outright — neither needs the other's negation.  `imax a b ≤ b` because
`Nat.imax a b` is `0` when `b` is `0` and `max a b` otherwise. -/
theorem VIndField.level_of_geq {lvl dlvl : VLevel} (h : lvl ≤ dlvl ∨ dlvl ≈ VLevel.zero) :
    VLevel.imax lvl dlvl ≤ dlvl := by
  intro ls
  simp only [VLevel.eval, Lean.Nat.imax]
  cases h with
  | inl h => split <;> simp_all [h ls]
  | inr h =>
    have := VLevel.equiv_def.1 h ls
    simp only [VLevel.eval] at this
    simp [this]

/-- **R6.**  The checker's field step, as it appears in `checkConstructors`.  Success produces
a field level with both `VIndField.WF.hasType` and `VIndField.WF.level`, for *any* choice of
`recArg` — which is why R7 is a separate row rather than a precondition of this one. -/
theorem M.WF.field_step {c : VContext} {D : VInductDecl'} {dom : Expr} {e' : VExpr}
    {resultLevel : Lean.Level} (hU : c.lparams.length = D.uvars)
    (hlvl : VLevel.ofLevel c.lparams resultLevel = some D.lvl) (he : c.TrExprS dom e') :
    M.WF c.toContext
      (do
        let s ← liftM (TypeChecker.ensureType dom)
        unless resultLevel.isAlwaysZero || resultLevel.geq' s.sortLevel! do
          MonadExcept.throw (Exception.other "level too big")
        Pure.pure s)
      fun s => ∃ (ty : VExpr) (lvl : VLevel) (u : Lean.Level),
        c.TrExprS dom ty ∧ s = Lean.Expr.sort u ∧ VLevel.ofLevel c.lparams u = some lvl ∧
        c.venv.HasType D.uvars c.vlctx.toCtx ty (.sort lvl) ∧
        VLevel.imax lvl D.lvl ≤ D.lvl := by
  refine (M.WF.ensureType he).bind fun s hs => ?_
  obtain ⟨ty, u, lvl, h1, rfl, h2, h3⟩ := hs
  simp only [Lean.Expr.sortLevel!]
  by_cases hg : (resultLevel.isAlwaysZero || resultLevel.geq' u) = true
  case neg =>
    simp only [Bool.not_eq_true] at hg
    simp only [hg, Bool.false_eq_true, if_false]
    exact M.WF.bind (M.WF.throw (Q := fun _ => False)) fun _ h => h.elim
  case pos =>
    simp only [hg, if_true]
    simp only [Bool.or_eq_true] at hg
    refine M.WF.pure ⟨ty, lvl, u, h1, rfl, h2, hU ▸ h3, VIndField.level_of_geq ?_⟩
    rcases hg with hz | hge
    · exact .inr (Lean4Lean.ofLevel_isAlwaysZero hlvl hz)
    · exact .inl (Lean.Level.geq'_wf hlvl h2 hge)


/-! ## R7: strict positivity — **unblocked; the occurrence check is now specified**

`checkPositivity` (`Add.lean:224`) rejects on `hasIndOcc stats.indConsts …`; its *success*
is what establishes `VIndField.WF.pos`, whose `none` branch is the positive statement
`∃ A, D.NoBlock A ∧ env.IsDefEqType D.uvars Γ F.type A`.  The only evidence for it is
`hasIndOcc (← whnf dom) = false`, so R7 must read `hasIndOcc`.

**The blocker was removed and this row was re-measured against the tree rather than against
the old note.**  `hasIndOcc` no longer goes through `Lean.Expr.find?` / the body-less
`@[extern] opaque findImpl?`; it goes through `Lean4Lean.anySubterm`, whose traversal is
`Lean.Expr.replaceNoCacheT` — total Lean that unfolds in a proof.  Part 0 of this file is the
specification: `anySubterm_eq` and `hasIndOcc_eq`, proved with **no new axiom** (`propext`
and `Quot.sound` only, both already standard).  The previous note's recommendation — "replace
it with a structural walk rather than assert an axiom" — is what happened, and this row is the
confirmation that it was sufficient.

### What R7 still needs, precisely

1. **The syntactic→abstract transfer.**  `TrExprS.noConsts` (Part 0), sorry-free, modulo three
   named hypotheses that are *findings*, not bookkeeping: `hasIndOcc` is blind to constants a
   `vlet` binding hides, to constants a literal expands into, and — the sharpest — to the
   parameter/index arguments `TrProj` reads off the *type* of a projected term.  See that
   section's note.  The C++ `has_ind_occ` is blind in exactly the same three ways, so this is a
   question about `VIndField.WF.pos` versus both kernels, not a divergence between them.

2. **The sort upgrade.**  `whnf.WF` delivers `c.TrExpr e₁ e'`, i.e. an `IsDefEqU`.
   `VIndField.WF.pos` wants `VEnv.IsDefEqType` — an `IsDefEq` *at a sort*.  There is no lemma
   in the tree taking `IsDefEqU A B` plus `HasType A (.sort u)` to `IsDefEqType A B`; the route
   is type uniqueness (`IsDefEq.uniq`, `Theory/Typing/UniqueTyping.lean`), which the type
   checker's own proofs already use, so it adds no taint beyond Part II's inherited debt — but
   it is a step, not a rewrite, and it is not done here.

3. **The context correspondence — which is R1/R2.**  `checkPositivity.loop` recurses under
   `withLocalDecl`, so its evidence lands in an *fvar* context, while `pos` is stated at
   `((C.fields.take i).map (·.type)).reverse ++ D.params.reverse`.  Relating the two is the
   same telescope pinning R8's scan branch needs.  So R7 and R8 share a gate, and it is R1/R2.

## R8: the large-elimination flag

`isLargeEliminator` (`Add.lean:258`) has two branches, and they separate cleanly.

**The `isNotZero` branch closes here** — `stats.isNotZero` is `resultLevel.isNeverZero`
(`Add.lean:101`), and `ofLevel_isNeverZero` carries it to `D.lvl.IsNeverZero`, which is
`LECond`'s first disjunct verbatim.

**The scan branch was gated on R1/R2**, and this is worth stating precisely because the
*direction* of the gate is the opposite of what the row's price assumed.  The scan itself is
sound in exactly the direction `LECond` needs: `isAlwaysZero` is a sound-but-incomplete
syntactic test, and a field is pushed onto `toCheck` when it *fails*, so a field **absent**
from `toCheck` really does have `F.lvl ≈ .zero` (`ofLevel_isAlwaysZero`), and a field
**present** in it is covered by the final `toCheck.all type.getAppArgs.contains`.  No
completeness is needed anywhere.  What was missing is the correspondence between the loop's
accumulated fvars and the spec's field indices — `arg_i ↦ .bvar (nf-1-i)` and
`type.getAppArgs ↦ C.args`.

**That correspondence is now the R1/R2 section at the end of this file**, and both halves are
proved: `VLCtx.find?_mkFVars_rev` is `arg_k ↦ .bvar (nf-1-k)` and
`VIndCtor.mem_args_of_mem_getAppArgs` takes `arg_k ∈ type.getAppArgs` to
`.bvar (nf-1-k) ∈ C.args` — `of_scan`'s right disjunct, on the nose.  What remains between
that and `of_scan` firing is the *loop invariant itself*: that a successful run of
`isLargeEliminator.loop` leaves the accumulated binder list equal to `C.fields` (with the
`Nodup` the `NameGenerator` supplies) and stops at a `type` translating to
`C.canonResult D j`.  That is an `M.WF` induction over the loop, using R1's
`TrExprS.forallE_inst_fvar` at each step and `VIndCtor.canonResult_ne_forallE` to pin where it
stops; it is stated here as the remaining obligation rather than assumed.  The per-field step
below never depended on it. -/

/-- **R8, the `isNotZero` branch.**  `stats.isNotZero` is `resultLevel.isNeverZero`, so a
large eliminator justified by it lands on `LECond`'s first disjunct. -/
theorem VInductDecl'.LECond.of_isNotZero {D : VInductDecl'} {Us : List Name}
    {resultLevel : Lean.Level} (hlvl : VLevel.ofLevel Us resultLevel = some D.lvl)
    (h : resultLevel.isNeverZero) : D.LECond :=
  .inl (Lean4Lean.ofLevel_isNeverZero hlvl h)

/-- Positive check that the `isNotZero` branch is not vacuous: a `Type`-valued block really
does reach `LECond` through it, with no hypothesis discharged by accident. -/
example : (VInductDecl'.mk 0 [] (.succ .zero) [] false).LECond :=
  VInductDecl'.LECond.of_isNotZero (Us := []) (resultLevel := .succ .zero) rfl rfl

/-- **R8, the scan's per-field step.**  A field the scan does *not* push onto `toCheck` has
`isAlwaysZero` on its inferred sort, hence `F.lvl ≈ .zero` — `LECond`'s left disjunct for that
field.  `isAlwaysZero` is incomplete, but the implication runs in the sound direction, so
nothing here is hostage to that. -/
theorem M.WF.elim_field_step {c : VContext} {dom : Expr} {e' : VExpr}
    (he : c.TrExprS dom e') :
    M.WF c.toContext (liftM (TypeChecker.ensureType dom)) fun s =>
      ∃ (ty : VExpr) (lvl : VLevel) (u : Lean.Level),
        c.TrExprS dom ty ∧ s = Lean.Expr.sort u ∧
        c.venv.HasType c.lparams.length c.vlctx.toCtx ty (.sort lvl) ∧
        (u.isAlwaysZero → lvl ≈ VLevel.zero) := by
  refine (M.WF.ensureType he).mono fun _ h => ?_
  obtain ⟨ty, u, lvl, h1, rfl, h2, h3⟩ := h
  exact ⟨ty, lvl, u, h1, rfl, h3, fun hz => Lean4Lean.ofLevel_isAlwaysZero h2 hz⟩

/-- **R8's remaining obligation, stated.**  Everything the scan branch still needs is this
one implication, and its hypothesis is exactly R1/R2's telescope pinning: that the loop's
`i`-th binder is the spec's `i`-th field and that the result's spine arguments are `C.args`.
Kept as a theorem rather than a comment so that R1/R2 landing makes it fire. -/
theorem VInductDecl'.LECond.of_scan {D : VInductDecl'} {T : VIndType} {C : VIndCtor}
    (hT : D.types = [T]) (hC : T.ctors = [C])
    (h : ∀ i (F : VIndField), C.fields[i]? = some F →
      F.lvl ≈ VLevel.zero ∨ VExpr.bvar (C.fields.length - 1 - i) ∈ C.args) :
    D.LECond := .inr ⟨T, hT, .inr ⟨C, hC, h⟩⟩

/-- The empty-constructor case, which `isLargeEliminator` returns `true` for outright. -/
theorem VInductDecl'.LECond.of_no_ctors {D : VInductDecl'} {T : VIndType}
    (hT : D.types = [T]) (hC : T.ctors = []) : D.LECond := .inr ⟨T, hT, .inl hC⟩

end AddInductive

/-! # R1/R2: the telescope, pinned

Both R7 and R8's scan branch need the same thing, and it is neither a level fact nor a
positivity fact: **the checker walks a constructor's pi-spine binding fvars, while the spec
indexes the same spine by de Bruijn level.**  Every clause of `VIndCtor.WF` — `fields`, `pos`,
`args_ty`, `result` — is stated in the context
`((C.fields.take i).map (·.type)).reverse ++ D.params.reverse`, and every fact the checker
produces is stated about an fvar.  This section is the dictionary.

Two halves, and they are independent:

* **R1, the binder step.**  Destructuring `.forallE name dom body bi` and running the body
  under `withLocalDecl` corresponds to peeling one `VExpr.forallE` and pushing one `vlam`.
  This is `TrExprS.forallE_inst_fvar` below; it is `TrExprS`'s own inversion composed with
  the existing `TrExprS.inst_fvar`, so it costs nothing new.

* **R2, the index arithmetic.**  A fvar bound `i` binders from the *innermost* end looks up to
  `.bvar i`.  In declaration order that is `arg_k ↦ .bvar (n - 1 - k)` — the shape
  `VInductDecl'.LECond` is stated with, and the shape `VIndCtor.WF.fields` needs.

`VLCtx.mkFVars` below is stored **innermost-first**, matching `VLCtx` itself rather than the
declaration order the spec's telescopes use; `find?_mkFVars_rev` is the one place the two
orders meet, and stating both makes the `n - 1 - k` appear exactly once. -/

/-- The local context the checker's binder walk builds: one `vlam` fvar entry per binder,
**innermost first**, on top of `Δ`. -/
def VLCtx.mkFVars : List (FVarId × List FVarId × VExpr) → VLCtx → VLCtx
  | [], Δ => Δ
  | (fv, deps, A) :: l, Δ => (some (fv, deps), .vlam A) :: VLCtx.mkFVars l Δ

@[simp] theorem VLCtx.mkFVars_nil {Δ : VLCtx} : VLCtx.mkFVars [] Δ = Δ := rfl

@[simp] theorem VLCtx.mkFVars_cons {fv deps A l} {Δ : VLCtx} :
    VLCtx.mkFVars ((fv, deps, A) :: l) Δ = (some (fv, deps), .vlam A) :: VLCtx.mkFVars l Δ := rfl

theorem VLCtx.mkFVars_append : ∀ (l₁ l₂ : List (FVarId × List FVarId × VExpr)) (Δ : VLCtx),
    VLCtx.mkFVars (l₁ ++ l₂) Δ = VLCtx.mkFVars l₁ (VLCtx.mkFVars l₂ Δ)
  | [], _, _ => rfl
  | _ :: l₁, l₂, Δ => congrArg _ (VLCtx.mkFVars_append l₁ l₂ Δ)

@[simp] theorem VLCtx.fvars_mkFVars : ∀ (l : List (FVarId × List FVarId × VExpr)) (Δ : VLCtx),
    (VLCtx.mkFVars l Δ).fvars = l.map (·.1) ++ Δ.fvars
  | [], _ => rfl
  | _ :: l, Δ => congrArg _ (VLCtx.fvars_mkFVars l Δ)

/-- **The fvar context *is* the spec's `Γ`.**  `VIndCtor.WF`'s clauses are all stated over
`(telescope.map (·.type)).reverse ++ D.params.reverse`; this says the abstract context of the
checker's fvar walk is that list, so no transport is needed between the two — which is the
whole point of R1/R2. -/
@[simp] theorem VLCtx.toCtx_mkFVars : ∀ (l : List (FVarId × List FVarId × VExpr)) (Δ : VLCtx),
    (VLCtx.mkFVars l Δ).toCtx = l.map (·.2.2) ++ Δ.toCtx
  | [], _ => rfl
  | _ :: l, Δ => congrArg _ (VLCtx.toCtx_mkFVars l Δ)

/-- The checker's binder walk only ever pushes `vlam`s, which is what discharges the `hctx`
hypothesis of `TrExprS.noConsts` — see the note there. -/
theorem VLCtx.allVLam_mkFVars {Δ : VLCtx} (h : Δ.AllVLam) :
    ∀ (l : List (FVarId × List FVarId × VExpr)), (VLCtx.mkFVars l Δ).AllVLam
  | [] => h
  | _ :: l => VLCtx.allVLam_mkFVars h l

/-- **The transfer, with `hctx` gone.**  In the context the positivity check actually runs in
— all-`vlam`, because `AddInductive` has no `withLetDecl` — a source term free of the block's
names translates to a block-free `VExpr`, modulo only the literal and projection hypotheses. -/
theorem TrExprS.noConsts_mkFVars {env : VEnv} {Us : List Name} {S : List Name}
    {p : Expr → Bool} {l : List (FVarId × List FVarId × VExpr)} {Δ₀ : VLCtx}
    {e : Expr} {e' : VExpr}
    (hpS : ∀ c us, c ∈ S → p (.const c us) = true)
    (hlit : ∀ lit : Lean.Literal, anySub p lit.toConstructor = false)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConsts S x → VExpr.NoConsts S y)
    (hΔ₀ : Δ₀.AllVLam)
    (H : TrExprS env Us (VLCtx.mkFVars l Δ₀) e e') (h : anySub p e = false) :
    VExpr.NoConsts S e' :=
  H.noConsts hpS hlit hproj (VLCtx.noConsts_of_allVLam (VLCtx.allVLam_mkFVars hΔ₀ l)) h

/-- **R2, innermost-first.**  The fvar `i` binders in from the innermost end is `.bvar i`.
The `Nodup` hypothesis is what stops a shadowed fvar from resolving to the wrong binder; the
checker supplies it from its `NameGenerator` (`VContext.reserves`/`fvars_mint`). -/
theorem VLCtx.find?_mkFVars {Δ : VLCtx} :
    ∀ {l : List (FVarId × List FVarId × VExpr)} {i fv deps A},
      (l.map (·.1)).Nodup → l[i]? = some (fv, deps, A) →
      ∃ B, (VLCtx.mkFVars l Δ).find? (.inr fv) = some (.bvar i, B)
  | (fv₀, deps₀, A₀) :: l, 0, fv, deps, A, _, hi => by
    cases hi
    refine ⟨A₀.lift, ?_⟩
    simp [VLCtx.mkFVars, VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
  | (fv₀, deps₀, A₀) :: l, i+1, fv, deps, A, hnd, hi => by
    simp only [List.getElem?_cons_succ] at hi
    have hmem : (fv, deps, A) ∈ l := List.mem_of_getElem? hi
    have hnd' : (l.map (·.1)).Nodup := by
      simpa using (List.nodup_cons.1 (by simpa using hnd)).2
    have hne : ¬ (fv₀ = fv) := by
      simp only [List.map_cons, List.nodup_cons] at hnd
      intro h; subst h
      exact hnd.1 (List.mem_map.2 ⟨_, hmem, rfl⟩)
    obtain ⟨B, hB⟩ := VLCtx.find?_mkFVars (Δ := Δ) hnd' hi
    refine ⟨B.liftN 1, ?_⟩
    simp only [VLCtx.mkFVars, VLCtx.find?, VLCtx.next, beq_iff_eq, hne, if_false, hB,
      VLocalDecl.depth]
    simp [VExpr.liftN]

/-- **R2, in declaration order** — the form `VInductDecl'.LECond` and `VIndCtor.WF.fields` are
stated in.  `l` here is the telescope as the checker pushes it, outermost first, so entry `k`
is field `k` and resolves to `.bvar (l.length - 1 - k)`. -/
theorem VLCtx.find?_mkFVars_rev {Δ : VLCtx} {l : List (FVarId × List FVarId × VExpr)}
    {k fv deps A} (hnd : (l.map (·.1)).Nodup) (hk : l[k]? = some (fv, deps, A)) :
    ∃ B, (VLCtx.mkFVars l.reverse Δ).find? (.inr fv) = some (.bvar (l.length - 1 - k), B) := by
  have hlt : k < l.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hk; exact absurd hk nofun
  refine VLCtx.find?_mkFVars (deps := deps) (A := A)
    (by simpa [List.map_reverse] using List.nodup_reverse.2 hnd) ?_
  rw [List.getElem?_reverse (by omega)]
  have : l.length - 1 - (l.length - 1 - k) = k := by omega
  rw [this]; exact hk

/-- **`mkFVars` is the shape the checker actually builds** — checked against A3's own binder
rule rather than asserted.  One `AddInductive.VContext.push` (which is what `withLocalDecl`
runs the body at, by `M.WF.withLocalDecl`) prepends exactly one `mkFVars` entry, with the
`deps` field `MLCtx.vlctx` supplies.  `rfl`, which is the point: no coercion sits between the
dictionary and the framework. -/
theorem AddInductive.VContext.push_vlctx (c : AddInductive.VContext)
    {name : Name} {ty : Expr} {ty' : VExpr} {bi : BinderInfo} {htr hty} :
    (c.push name ty ty' bi htr hty).vlctx
      = VLCtx.mkFVars [(⟨c.ngen.curr⟩, ty.fvarsList, ty')] c.vlctx := rfl

/-- Positive check that the index arithmetic is the one `VInductDecl'.LECond` asks for, and
that the statement is not vacuous: with two binders, the **first** declared resolves to
`.bvar 1` and the second to `.bvar 0` — i.e. `arg_k ↦ .bvar (n - 1 - k)`, `n = 2`. -/
example (fv₀ fv₁ : FVarId) (A₀ A₁ : VExpr) (h : fv₀ ≠ fv₁) :
    (∃ B, (VLCtx.mkFVars [(fv₀, [], A₀), (fv₁, [], A₁)].reverse []).find? (.inr fv₀)
        = some (.bvar 1, B)) ∧
    (∃ B, (VLCtx.mkFVars [(fv₀, [], A₀), (fv₁, [], A₁)].reverse []).find? (.inr fv₁)
        = some (.bvar 0, B)) :=
  ⟨VLCtx.find?_mkFVars_rev (by simp [h]) (k := 0) rfl,
   VLCtx.find?_mkFVars_rev (by simp [h]) (k := 1) rfl⟩

/-! ## R1: the binder step -/

/-- **R1.**  One step of the checker's spine walk, refined.  The `Expr` side destructures a
`.forallE` and instantiates the body with a fresh fvar (`withLocalDecl` + `instantiate1`); the
`VExpr` side peels one `VExpr.forallE` and pushes one `vlam`.  Both halves come out of
`TrExprS`'s own inversion — the target is *given* as `.forallE A B`, so constructor injectivity
pins the domain and codomain rather than leaving them existential. -/
theorem TrExprS.forallE_inst_fvar {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {name : Name} {dom body : Expr} {bi : BinderInfo} {A B : VExpr} {fv deps}
    (henv : VEnv.Ordered env)
    (hΔ : VLCtx.WF env Us.length ((some (fv, deps), .vlam A) :: Δ))
    (H : TrExprS env Us Δ (.forallE name dom body bi) (.forallE A B)) :
    TrExprS env Us Δ dom A ∧
      TrExprS env Us ((some (fv, deps), .vlam A) :: Δ) (body.instantiate1' (.fvar fv)) B := by
  cases H with
  | forallE _ _ hdom hbody => exact ⟨hdom, hbody.inst_fvar henv hΔ⟩

/-- The spine at the end of the walk is **not** a `forallE`, so the checker's loop cannot stop
early and cannot run long: a constructor's stored type is `mkPi (params ++ fields) result` and
`result` is an application.  This is what makes "the loop ran exactly `np + nf` times" a
consequence of success rather than an assumption. -/
theorem VExpr.mkApp_ne_forallE : ∀ {as : List VExpr} {f : VExpr},
    (∀ A B, f ≠ .forallE A B) → ∀ A B, VExpr.mkApp f as ≠ .forallE A B
  | [], _, hf => hf
  | _ :: as, f, _ => VExpr.mkApp_ne_forallE (as := as) (f := f.app _) (by rintro _ _ ⟨⟩)

theorem VIndCtor.canonResult_ne_forallE (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    ∀ A B, C.canonResult D j ≠ .forallE A B :=
  VExpr.mkApp_ne_forallE (by rintro _ _ ⟨⟩)

/-- Inverting the `VExpr` telescope at a `forallE`: the checker seeing a `.forallE` forces the
remaining telescope to be non-empty, because a constructor's result is an application.  This is
what makes "the loop ran exactly `np + nf` times" a *consequence* of success. -/
theorem VExpr.mkPi_eq_forallE {Bs : List VExpr} {R A B : VExpr}
    (hR : ∀ A B, R ≠ .forallE A B) (h : VExpr.mkPi Bs R = .forallE A B) :
    ∃ Bs', Bs = A :: Bs' ∧ B = VExpr.mkPi Bs' R := by
  cases Bs with
  | nil => exact absurd h (hR _ _)
  | cons B₀ Bs' => cases h; exact ⟨Bs', rfl, rfl⟩


/-! ## R2, assembled: `type.getAppArgs ↦ C.args`

The second half of the dictionary.  `isLargeEliminator` finishes with
`toCheck.all type.getAppArgs.contains`, and `VInductDecl'.LECond` asks for
`.bvar (nf - 1 - k) ∈ C.args`.  Four steps, each one lemma:

1. an argument of the checker's spine translates to a member of the target's `spineArgs`
   (`TrExprS.mem_spineArgs`);
2. an fvar's translation is *determined* by the context, so the member is exactly
   `.bvar (nf - 1 - k)` (`TrExprS.fvar_det` with R2's `find?_mkFVars_rev`);
3. the target's `spineArgs` at a constructor result is `bvars nf np ++ C.args`;
4. `bvars nf np` holds only indices `≥ nf`, so a field index lands in `C.args`.

Step 4 is the argument `VInductDecl'.LECond`'s own docstring makes informally ("a field
variable can never be one of the `nparams` leading parameter arguments"); it is discharged
here rather than assumed. -/

/-- An fvar's translation is pinned by the context — `TrExprS` on a `.fvar` has exactly one
rule and it reads `find?`.  This is what turns "some translation of `arg` is in the spine"
into "`.bvar (nf-1-k)` is in the spine". -/
theorem TrExprS.fvar_det {env : VEnv} {Us : List Name} {Δ : VLCtx} {fv : FVarId} {x y A : VExpr}
    (H : TrExprS env Us Δ (.fvar fv) x) (h : Δ.find? (.inr fv) = some (y, A)) : x = y := by
  cases H with | fvar h' => rw [h] at h'; exact (congrArg Prod.fst (Option.some.inj h')).symm

/-- Step 1.  Stated over `getAppArgsRevList` (`Verify/Expr.lean`), the structural reading of
`Expr.getAppArgs`; `getAppArgs_eq_rev` converts. -/
theorem TrExprS.mem_spineArgs {env : VEnv} {Us : List Name} {Δ : VLCtx} :
    ∀ {e : Expr} {e' : VExpr}, TrExprS env Us Δ e e' →
      ∀ a ∈ e.getAppArgsRevList, ∃ a', TrExprS env Us Δ a a' ∧ a' ∈ e'.spineArgs := by
  intro e
  induction e with
  | app f b ihf _ =>
    intro e' H a ha
    cases H with
    | app _ _ hf hb =>
      rw [Lean.Expr.getAppArgsRevList, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨_, hb, by rw [VExpr.spineArgs]; simp⟩
      · obtain ⟨a', ha', hmem⟩ := ihf hf a ha
        exact ⟨a', ha', by rw [VExpr.spineArgs]; exact List.mem_append_left _ hmem⟩
  | _ => intro e' H a ha; simp [Lean.Expr.getAppArgsRevList] at ha

/-- Step 4.  A de Bruijn index below the telescope's floor is not one of its variables. -/
theorem VExpr.not_mem_bvars_of_lt {m lo n : Nat} (h : m < lo) :
    VExpr.bvar m ∉ VExpr.bvars lo n := by
  intro hm
  obtain ⟨i, _, hi⟩ := VExpr.mem_bvars.1 hm
  simp only [VExpr.bvar.injEq] at hi
  omega

/-- **R2, assembled.**  If the checker's `k`-th field fvar appears among the spine arguments of
the constructor's result, then the spec's `.bvar (n - 1 - k)` is a member of `C.args` — which
is `VInductDecl'.LECond`'s right disjunct verbatim.

`hres` is where R1's telescope walk lands: the result the loop stops at translates to the
constructor's canonical result. -/
theorem VIndCtor.mem_args_of_mem_getAppArgs {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {D : VInductDecl'} {C : VIndCtor} {j : Nat} {type : Lean.Expr}
    {l : List (FVarId × List FVarId × VExpr)} {np k fv deps A} {Δ₀ : VLCtx}
    (hΔ : Δ = VLCtx.mkFVars l.reverse Δ₀)
    (hnd : (l.map (·.1)).Nodup) (hk : l[np + k]? = some (fv, deps, A))
    (hlen : l.length = np + C.fields.length)
    (hres : TrExprS env Us Δ type (C.canonResult D j))
    (hmem : Lean.Expr.fvar fv ∈ type.getAppArgsRevList) :
    VExpr.bvar (C.fields.length - 1 - k) ∈ C.args := by
  subst hΔ
  have hlt : np + k < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hk; exact absurd hk nofun
  obtain ⟨B, hfind⟩ := VLCtx.find?_mkFVars_rev (Δ := Δ₀) hnd hk
  obtain ⟨a', ha', hmem'⟩ := hres.mem_spineArgs _ hmem
  rw [ha'.fvar_det hfind, show l.length - 1 - (np + k) = C.fields.length - 1 - k by omega]
    at hmem'
  rw [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.spineArgs_mkApp, VExpr.spineArgs_const,
    List.nil_append, List.mem_append] at hmem'
  exact hmem'.resolve_left (VExpr.not_mem_bvars_of_lt (by omega))

namespace AddInductive
open Kernel

/-! ## The loop invariant of `isLargeEliminator.loop`

R7 and R8's scan branch share one gate, and this is it: **a successful run of
`isLargeEliminator.loop` walked exactly the constructor's telescope.**  The dictionary above
supplies the two halves of the correspondence; this is the induction that installs it.

The loop is unusual among the checker's walks in that it binds *every* binder with
`withLocalDecl`, parameters included — `checkConstructors.loop` substitutes `stats.params[i]!`
instead — so after `m` steps the context is exactly `VLCtx.mkFVars` of the first `m` entries of
`C.params ++ C.fields.map (·.type)`, and `VLCtx.toCtx_mkFVars` makes that *syntactically* the
spec's `Γ`.

### The one obligation this cannot discharge: `consumeTypeAnnotations`

`withLocalDecl name bi dom.consumeTypeAnnotations` pushes the **annotation-stripped** domain,
while `ensureType dom` and the target telescope use the raw one.  `Expr.consumeTypeAnnotations`
removes `optParam`/`autoParam`/`outParam`/`semiOutParam` applications, and `optParam α d` is
only *definitionally* `α` — `TrExprS` is syntactic, so the two translate to different `VExpr`s.

That matters here and not merely cosmetically: `TrExprS.inst_fvar` requires the pushed
`VLocalDecl` to be the very `.vlam B` the target's `forallE` supplies, so the pushed type's
translation **must** be `B`.  It is therefore taken as the hypothesis `hcta` rather than
absorbed, and `hcta` is **not** universally true.

**It is false in practice, not only in principle — measured, not argued.**  Over a full `Lean`
environment, `Expr.consumeTypeAnnotations` is *not* the identity on **263 of 13408**
constructor binder domains (4716 constructors), i.e. ~2%.  Real instances:

    Lean.Compiler.LCNF.LetValue.proj   autoParam (Purity = .pure) …   ↦  Purity = .pure
    Std.Roc.Sliceable.mk               outParam.{v+2} Type.{v}        ↦  Type.{v}
    Lean.Grind.ToInt.Div.mk            outParam IntInterval           ↦  IntInterval

So on ~2% of real constructors the kernel's local context records a binder type that is not
the constructor's stored domain, and `VLCtx.toCtx_mkFVars`'s claim that the fvar walk's context
*is* the spec's `Γ` is wrong for those declarations.  This is **not** a divergence: the C++
kernel calls `consume_type_annotations` at exactly the two `mk_local_decl` sites
(`~/lean4/src/kernel/inductive.cpp:222,227`), so both kernels do the same thing.

### Why the `IsDefEqCtx` weakening cannot be built yet

The shape is right — `outParam α` and `autoParam α t` δ-reduce to `α`, so the true relation is
definitional equality, and `VIndCtor.WF.params_eq` already absorbs exactly this slack for the
parameter telescope.  But two facts have to hold before it can be written, and the first is
fatal today:

1. **`Lean.Expr.consumeTypeAnnotations` is `partial`, hence an `opaque` with no Lean body.**
   Verified structurally, not by reading: it is reachable from `Lean4Lean.addDecl`, and a
   cone scan finds **48** body-less opaques there of which **28** are not mentioned by any
   axiom of `Verify/Axioms.lean` — this one among them (there is no `consumeTypeAnnotations'`
   model anywhere in the tree).  Nothing can be proved about its result, so no translation of
   `dom.consumeTypeAnnotations` can be exhibited *at all* — weakened or not.  This is the
   `Lean.Expr.findImpl?` blocker again, in a place nobody had looked, and `Guard.lean`'s
   check 3 is blind to it for the same reason: it filters to constants defined in
   `Lean4Lean.*` modules.  It reaches **eleven** distinct binder-introducing loops —
   `checkInductiveTypes.loopInd.loop`, `checkConstructors.loop`, `checkPositivity.loop`,
   `isRecArg.loop`, `isLargeEliminator.loop`, and all six of `mkRecInfos.*` — i.e. every
   `withLocalDecl` site in the inductive adder.

   **The fix is the `anySubterm` fix, and it was checked rather than proposed.**  Written by
   pattern-matching on the application shape instead of through the partial `appFn!`/`appArg!`,
   it is structurally recursive — each call descends to a strict subterm — so it needs no fuel
   and has a body:

       def consumeTypeAnnotations' : Expr → Expr
         | e@(.app (.app (.const n _) α) _) =>
             if n == ``optParam || n == ``autoParam then consumeTypeAnnotations' α else e
         | e@(.app (.const n _) α) =>
             if n == ``outParam || n == ``semiOutParam then consumeTypeAnnotations' α else e
         | e => e

   Differentially checked against the opaque over every binder domain of every constructor and
   inductive type in a full `Lean` environment: **15799 compared, 15799 agree, 0
   disagreements**.  The arity conditions match `isOptParam`/`isOutParam`'s `isAppOfArity`,
   including the over- and under-applied cases, which fall through to `e` on both sides.
   Dropping the call is *not* an option: the C++ kernel makes it too, so removing it would be
   a genuine divergence.  `Lean4Lean/Inductive/Add.lean` is a file this stream does not own, so
   this is a recommendation with its measurement attached, not a change.

2. **A target-preserving context-defeq transport for `TrExprS` is missing.**  `defeqDFC` and
   `defeqDFC'` (`Verify/Typing/Lemmas.lean:1423,1481`) both let the *target* move
   (`∃ e₂, …` and `TrExpr`), and re-inverting a moved target at a `forallE` needs pi
   injectivity.  What is needed instead is

       TrExprS.defeqDFC_target :
         VEnv.WF env → (Δ₁ and Δ₂ agree on every `ofv` and every `vlet` *value*, and their
           `vlam` types are pairwise `IsDefEq`) → TrExprS env Us Δ₁ e e' → TrExprS env Us Δ₂ e e'

   **This is provable and is *not* injectivity-blocked** — all eleven cases were checked.
   `bvar`/`fvar` preserve the target because `find?`'s value is determined by position and by
   the `vlet` values, both of which the relation fixes; `app`/`lam`/`forallE`/`letE` transport
   their `HasType`/`IsType` premises by `defeqDFC` and reuse the IH's target; and the `proj`
   case — the one that looks blocked — is fine because a target-*preserving* statement may
   **reuse** the same `us`/`ps`/`ιs` rather than re-deriving them, so it never needs
   `TrProj.uniq`.  `defeqDFC` reads as blocked only because it re-derives them existentially.
   Anyone pricing this as part of the injectivity family should not.

Until (1) is fixed, `hcta` stays a stated hypothesis, false as written, and labelled so at its
own definition — a hypothesis discharged at every real call site is exactly the kind that
erodes into a technicality, and the next person to reuse this lemma would inherit a false
claim with no warning.  The live measurement in `Lean4Lean/Tests/KernelHardening.lean` exists
so the "2%" cannot quietly become "never". -/

/-- The number of leading `forallE` binders — the *syntactic* pi-arity.  `TrExprS` does not
determine it (`.mdata`/`.letE` translate through), so the loop invariant tracks it. -/
def _root_.Lean.Expr.piArity : Expr → Nat
  | .forallE _ _ b _ => b.piArity + 1
  | _ => 0

/-- Instantiating an **fvar** preserves the head constructor, hence the pi-arity.  The
restriction to fvars is not cosmetic: substituting a *pi* for a bound variable raises the
arity, so the general statement is false.  The loop only ever substitutes `withLocalDecl`'s
fvar. -/
theorem _root_.Lean.Expr.piArity_instantiate1'_fvar :
    ∀ (e : Expr) (v : FVarId) (k : Nat),
      (Lean.Expr.instantiate1' e (.fvar v) k).piArity = e.piArity
  | .forallE _ _ b _, v, k => by
    rw [Lean.Expr.instantiate1', Lean.Expr.piArity, Lean.Expr.piArity,
      Lean.Expr.piArity_instantiate1'_fvar b v (k+1)]
  | .bvar _, _, _ => by
    rw [Lean.Expr.instantiate1']
    split
    · rfl
    · split
      · rw [Lean.Expr.liftLooseBVars']; rfl
      · rfl
  | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const _ _, _, _
  | .app _ _, _, _ | .lam .., _, _ | .letE .., _, _ | .lit _, _, _
  | .mdata _ _, _, _ | .proj _ _ _, _, _ => by
    rw [Lean.Expr.instantiate1'] <;> rfl

/-- The `.fvar` companion of `Lean.Expr.eqv_sort`/`eqv_const` (`Verify/Expr.lean`), which is
what turns `Array.contains` back into membership at the loop's final check. -/
theorem _root_.Lean.Expr.eqv_fvar {e : Expr} {v : FVarId} :
    (e == Lean.Expr.fvar v) = true ↔ e = Lean.Expr.fvar v := by
  conv => lhs; simp [(· == ·)]
  cases e <;> simp [Lean.Expr.eqv']

/-- The state of `isLargeEliminator.loop`, refined.  `l` is the telescope walked so far in
declaration order, `Bs` the telescope still to come. -/
structure ElimLoopInv (c₀ : VContext) (D : VInductDecl') (C : VIndCtor) (j np : Nat)
    (Small : Nat → Prop) (c : VContext)
    (l : List (FVarId × List FVarId × VExpr)) (Bs : List VExpr)
    (type : Expr) (toCheck : Array Expr) : Prop where
  /-- The environment and level parameters do not move; only the local context grows. -/
  venv : c.venv = c₀.venv
  lparams : c.lparams = c₀.lparams
  /-- **R1/R2's dictionary, as a loop invariant.** -/
  vlctx : c.vlctx = VLCtx.mkFVars l.reverse c₀.vlctx
  nodup : (l.map (·.1)).Nodup
  /-- Walked plus remaining is the constructor's whole telescope. -/
  tele : l.map (·.2.2) ++ Bs = C.params ++ C.fields.map (·.type)
  /-- The `Expr` the loop holds translates to the `VExpr` telescope still to come. -/
  tr : c.TrExprS type (VExpr.mkPi Bs (C.canonResult D j))
  /-- **The loop cannot stop early.**  Not derivable from `tr`: a `.mdata`- or `.letE`-wrapped
  domain translates to a `forallE` *target* without being a `forallE` itself, so the syntactic
  spine has to be tracked separately.  `Expr.piArity` is preserved by `instantiate1`, which is
  what makes this maintainable in one line.  The caller has the fact for free —
  `checkConstructors` has already run and `isValidIndAppIdx` rejects any constructor whose
  stored spine is not a literal `forallE` chain. -/
  spine : Bs.length ≤ type.piArity
  /-- Every field already walked is either recorded small or queued in `toCheck`. -/
  done : ∀ k x, np ≤ k → l[k]? = some x → Small (k - np) ∨ Lean.Expr.fvar x.1 ∈ toCheck

/-- Inverting `TrExprS` at a source `forallE`: the target is a `forallE` too.  Only
`TrExprS.forallE` can derive it, which is what pins the telescope. -/
theorem _root_.Lean4Lean.TrExprS.forallE_target {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {n : Name} {d b : Expr} {bi : BinderInfo} {X : VExpr}
    (H : TrExprS env Us Δ (.forallE n d b bi) X) : ∃ A B, X = .forallE A B := by
  cases H; exact ⟨_, _, rfl⟩

/-- The walked prefix reaches the field telescope: at position `l.length ≥ np` the next entry
of `C.params ++ C.fields.map (·.type)` is field `l.length - np`'s stored type.  Pure list
arithmetic, but it is what turns "the loop is at binder `i`" into "the loop is at field
`i - np`". -/
theorem ElimLoopInv.field_at {C : VIndCtor} {np : Nat}
    {l : List (FVarId × List FVarId × VExpr)} {A : VExpr} {Bs : List VExpr}
    (htele : l.map (·.2.2) ++ (A :: Bs) = C.params ++ C.fields.map (·.type))
    (hnp : np = C.params.length) (hge : np ≤ l.length) :
    ∃ F, C.fields[l.length - np]? = some F ∧ F.type = A := by
  subst hnp
  have hlen : (l.map (·.2.2)).length = l.length := List.length_map ..
  have h1 : (l.map (·.2.2) ++ (A :: Bs))[l.length]? = some A := by
    rw [List.getElem?_append_right (by omega), hlen]; simp
  rw [htele, List.getElem?_append_right (by omega), List.getElem?_map] at h1
  cases hF : C.fields[l.length - C.params.length]? with
  | none => rw [hF] at h1; exact absurd h1 nofun
  | some F => rw [hF] at h1; exact ⟨F, rfl, Option.some.inj h1⟩

/-- **The entry condition, from `TrIndCtor`.**  A relation with no instance proves nothing, so
the invariant is exhibited at the state the loop actually starts in: nothing walked, the whole
telescope ahead, an empty `toCheck`.  `tr` is `rfl` here — `VIndCtor.type` *is*
`mkPi (params ++ fields) canonResult`, which is why the loop's target never has to be guessed.

`spine` is the one field the caller must supply, and it is exactly the fact
`checkConstructors` has already established; see the `spine` field's own docstring. -/
theorem ElimLoopInv.start {c₀ : VContext} {D : VInductDecl'} {C : VIndCtor} {j : Nat}
    {stats : InductiveStats} {Small : Nat → Prop} {ctorType : Expr}
    (htr : c₀.TrExprS ctorType (C.type D j))
    (hspine : (C.params ++ C.fields.map (·.type)).length ≤ ctorType.piArity) :
    ElimLoopInv c₀ D C j stats.params.size Small c₀ []
      (C.params ++ C.fields.map (·.type)) ctorType #[] where
  venv := rfl
  lparams := rfl
  vlctx := rfl
  nodup := by simp
  tele := by simp
  tr := htr
  spine := hspine
  done := by intro k x _ h; exact absurd h nofun

/-- **The terminal case**, and the payoff of the whole R1/R2 section: when the loop stops, its
`spine` field forces the remaining telescope to be empty, so `tr` says the `Expr` it stopped at
translates to `C.canonResult D j` — and `VIndCtor.mem_args_of_mem_getAppArgs` turns
`toCheck.all type.getAppArgs.contains` into `LECond`'s right disjunct. -/
theorem ElimLoopInv.terminal {c₀ : VContext} {D : VInductDecl'} {C : VIndCtor} {j : Nat}
    {stats : InductiveStats} {Small : Nat → Prop} {c : VContext}
    {l : List (FVarId × List FVarId × VExpr)} {Bs : List VExpr} {type : Expr}
    {toCheck : Array Expr}
    (inv : ElimLoopInv c₀ D C j stats.params.size Small c l Bs type toCheck)
    (hnp : stats.params.size = C.params.length) (hz : type.piArity = 0) :
    M.WF c.toContext (Pure.pure (toCheck.all type.getAppArgs.contains) : M Bool)
      (fun b => b = true → ∀ k F, C.fields[k]? = some F →
        Small k ∨ VExpr.bvar (C.fields.length - 1 - k) ∈ C.args) := by
  have hBs : Bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (hz ▸ inv.spine))
  subst hBs
  have htele := inv.tele
  rw [List.append_nil] at htele
  have hlen : l.length = stats.params.size + C.fields.length := by
    have := congrArg List.length htele
    simp only [List.length_map, List.length_append] at this
    omega
  refine M.WF.pure ?_
  intro hb k F hF
  have hklt : k < C.fields.length := by
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hF; exact absurd hF nofun
  have hlt : stats.params.size + k < l.length := by omega
  obtain ⟨x, hx⟩ : ∃ x, l[stats.params.size + k]? = some x :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  rcases inv.done _ x (Nat.le_add_right ..) hx with hs | hmem
  · exact .inl (by simpa using hs)
  refine .inr ?_
  have hcontains : type.getAppArgs.contains (Lean.Expr.fvar x.1) = true := by
    rw [Array.all_eq_true] at hb
    obtain ⟨i, hi, hgi⟩ := Array.getElem_of_mem hmem
    exact hgi ▸ hb i hi
  have hall : (Lean.Expr.fvar x.1) ∈ type.getAppArgsRevList := by
    rw [Array.contains_iff_exists_mem_beq] at hcontains
    obtain ⟨y, hy, hyeq⟩ := hcontains
    rw [Lean.Expr.getAppArgs_eq_rev] at hy
    have hy' : y ∈ type.getAppArgsRevList := by simpa using hy
    rw [← Lean.Expr.eqv_fvar.1 (Lean.Expr.eqv_euc hyeq (Lean.Expr.eqv_refl _))]
    exact hy'
  exact VIndCtor.mem_args_of_mem_getAppArgs inv.vlctx inv.nodup (np := stats.params.size) hx
    hlen (by simpa using inv.tr) hall

/-- **The loop invariant.**  A successful `isLargeEliminator.loop` walked exactly the
constructor's telescope, and every field it did not record as small has its de Bruijn variable
in `C.args` — which is `VInductDecl'.LECond`'s per-field disjunction verbatim, so
`VInductDecl'.LECond.of_scan` fires on it.

Two hypotheses, both real and both stated rather than absorbed:

* `hcta` is the annotation-stripping obligation of the section note, **now narrowed to the
  annotated case**: `Lean4Lean.consumeAnnotations` replaced the body-less opaque, so
  `M.WF.consumeAnnotations`'s identity branch discharges every binder with
  `isAnnotation dom = false` — ~98% of a real environment's constructor binder domains.  What
  is left is genuinely false and genuinely there: on an `optParam`/`autoParam`/`outParam`
  binder the stripped type is only *definitionally* the stored one.  Do not read the remainder
  as a technicality; closing it needs the `IsDefEqCtx` weakening and `defeqDFC_target`, both
  named in the section note.
* `hSmall` is the level side, handed the *pre-push* translation and asked about the
  *post-push* run, because `ensureType dom` executes inside `withLocalDecl`.  The weakening
  between the two is the caller's, which is where the choice of `VIndField.lvl` lives anyway. -/
theorem M.WF.elim_loop {c₀ : VContext} {D : VInductDecl'} {C : VIndCtor} {j : Nat}
    {stats : InductiveStats} {Small : Nat → Prop}
    (hnp : stats.params.size = C.params.length)
    (hcta : ∀ (c : VContext) (dom : Expr) (B : VExpr), isAnnotation dom = true →
      c.TrExprS dom B →
      c.TrExprS (Nat.repeat stripAnnotation c.fuel.inductiveFuel dom) B)
    (hSmall : ∀ (c c' : VContext) (l : List (FVarId × List FVarId × VExpr))
        (x : FVarId × List FVarId × VExpr) (dom : Expr) (k : Nat) (F : VIndField),
      c.vlctx = VLCtx.mkFVars l.reverse c₀.vlctx →
      c'.vlctx = VLCtx.mkFVars (l ++ [x]).reverse c₀.vlctx →
      l.length = stats.params.size + k →
      C.fields[k]? = some F →
      c.TrExprS dom F.type →
      M.WF c'.toContext (liftM (TypeChecker.ensureType dom))
        (fun s => s.sortLevel!.isAlwaysZero → Small k)) :
    ∀ (fuel : Nat) (c : VContext) (l : List (FVarId × List FVarId × VExpr)) (Bs : List VExpr)
      (type : Expr) (toCheck : Array Expr),
      ElimLoopInv c₀ D C j stats.params.size Small c l Bs type toCheck →
      M.WF c.toContext (isLargeEliminator.loop stats type l.length toCheck fuel)
        (fun b => b = true → ∀ k F, C.fields[k]? = some F →
          Small k ∨ VExpr.bvar (C.fields.length - 1 - k) ∈ C.args) := by
  intro fuel
  induction fuel with
  | zero =>
    intro c l Bs type toCheck _
    rw [isLargeEliminator.loop]
    exact M.WF.throw
  | succ fuel ih =>
    intro c l Bs type toCheck inv
    cases type with
    | forallE name dom body bi =>
      rw [isLargeEliminator.loop]
      -- The target must be a `forallE` too, so the remaining telescope is non-empty.
      obtain ⟨A, B, hAB⟩ := inv.tr.forallE_target
      obtain ⟨Bs', rfl, rfl⟩ := VExpr.mkPi_eq_forallE (C.canonResult_ne_forallE D j) hAB
      -- Invert once: the domain's translation is the telescope head, and the body's is the tail.
      obtain ⟨hty, -, hdom, hbody⟩ :
          c.IsType A ∧ True ∧ c.TrExprS dom A ∧
            TrExprS c.venv c.lparams ((none, .vlam A) :: c.vlctx) body
              (VExpr.mkPi Bs' (C.canonResult D j)) := by
        cases h : inv.tr with | forallE h1 _ h3 h4 => exact ⟨h1, trivial, h3, h4⟩
      -- The annotation step, which now has a body: on an un-annotated domain it is the
      -- identity, so `hcta` is only consulted on the ~2% that carry one.
      refine (M.WF.consumeAnnotations (Q := fun d => c.TrExprS d A)
        (fun _ => hdom) (fun h => hcta c dom A h hdom)).bind fun dom' hdom' => ?_
      refine M.WF.withLocalDecl hdom' hty ?_
      let fv : FVarId := ⟨c.ngen.curr⟩
      let x : FVarId × List FVarId × VExpr := (fv, dom'.fvarsList, A)
      let c' : VContext := c.push name dom' A bi hdom' hty
      show M.WF c'.toContext _ _
      -- The four invariant fields that do not depend on which branch is taken.
      have hvl : c'.vlctx = VLCtx.mkFVars (l ++ [x]).reverse c₀.vlctx := by
        show ((some (fv, _), VLocalDecl.vlam A) :: c.vlctx) = _
        rw [inv.vlctx, List.reverse_append]
        rfl
      have hnodup : ((l ++ [x]).map (·.1)).Nodup := by
        rw [List.map_append, List.nodup_append]
        refine ⟨inv.nodup, by simp, ?_⟩
        intro a ha b hb hab
        have hb' : b = fv := by simpa using hb
        subst hb'; subst hab
        refine c.curr_not_mem ?_
        rw [inv.vlctx]
        simp only [VLCtx.fvars_mkFVars, List.mem_append, List.map_reverse, List.mem_reverse]
        exact .inl ha
      have htele : (l ++ [x]).map (·.2.2) ++ Bs' = C.params ++ C.fields.map (·.type) := by
        rw [List.map_append]; simpa using inv.tele
      have htr : c'.TrExprS (body.instantiate1 (.fvar fv)) (VExpr.mkPi Bs' (C.canonResult D j)) := by
        rw [Lean.Expr.instantiate1_eq]
        exact hbody.inst_fvar c.Ewf.ordered c'.mlctx_wf.tr.wf
      have hspine : Bs'.length ≤ (body.instantiate1 (.fvar fv)).piArity := by
        rw [Lean.Expr.instantiate1_eq, Lean.Expr.piArity_instantiate1'_fvar]
        have := inv.spine
        simp only [Lean.Expr.piArity, List.length_cons] at this
        omega
      have hlen' : (l ++ [x]).length = l.length + 1 := by simp
      -- The `done` field, given the branch's `toCheck`.
      have hdone : ∀ (tc : Array Expr), (∀ e, e ∈ toCheck → e ∈ tc) →
          (stats.params.size ≤ l.length →
            Small (l.length - stats.params.size) ∨ Lean.Expr.fvar fv ∈ tc) →
          ∀ k y, stats.params.size ≤ k → (l ++ [x])[k]? = some y →
            Small (k - stats.params.size) ∨ Lean.Expr.fvar y.1 ∈ tc := by
        intro tc hsub hnew k y hk hy
        by_cases hlt : k < l.length
        · rw [List.getElem?_append_left hlt] at hy
          exact (inv.done k y hk hy).imp id (fun h => hsub _ h)
        · have hkeq : k = l.length := by
            have : k < (l ++ [x]).length := by
              by_contra hc
              rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hy; exact absurd hy nofun
            rw [hlen'] at this; omega
          subst hkeq
          have : y = x := by
            rw [List.getElem?_append_right (Nat.le_refl _)] at hy; simpa using hy.symm
          subst this
          exact hnew hk
      by_cases hge : l.length ≥ stats.params.size
      · -- Past the parameters: `ensureType` decides whether the field is queued.
        simp only [hge, if_true]
        obtain ⟨F, hF, rfl⟩ := ElimLoopInv.field_at inv.tele hnp hge
        refine (hSmall c c' l x dom (l.length - stats.params.size) F inv.vlctx hvl
          (by omega) hF hdom).bind fun s hs => ?_
        by_cases hz : (!s.sortLevel!.isAlwaysZero) = true
        · simp only [hz, if_true]
          refine hlen' ▸ ih c' (l ++ [x]) Bs' _ _ ?_
          exact { venv := inv.venv, lparams := inv.lparams, vlctx := hvl, nodup := hnodup, tele := htele
                  tr := htr, spine := hspine
                  done := hdone _ (fun _ h => Array.mem_push_of_mem _ h)
                    fun _ => .inr (Array.mem_push_self ..) }
        · simp only [hz, Bool.false_eq_true, if_false]
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hz
          refine hlen' ▸ ih c' (l ++ [x]) Bs' _ _ ?_
          exact { venv := inv.venv, lparams := inv.lparams, vlctx := hvl, nodup := hnodup, tele := htele
                  tr := htr, spine := hspine
                  done := hdone _ (fun _ h => h) fun _ => .inl (hs hz) }
      · -- Still in the parameters: nothing queued, and no field index is in range.
        simp only [hge, if_false]
        refine hlen' ▸ ih c' (l ++ [x]) Bs' _ _ ?_
        exact { venv := inv.venv, lparams := inv.lparams, vlctx := hvl, nodup := hnodup, tele := htele
                tr := htr, spine := hspine
                done := hdone _ (fun _ h => h) fun h => absurd h hge }
    | _ =>
      rw [isLargeEliminator.loop]
      · exact inv.terminal hnp rfl
      · intro _ _ _ _ h; exact absurd h (by simp)

/-- **The gate closes.**  `M.WF.elim_loop`'s postcondition is `VInductDecl'.LECond.of_scan`'s
hypothesis modulo the `Small` predicate, so choosing `Small k := (C.fields.getD k default).lvl ≈
VLevel.zero` makes `of_scan` fire on a successful run directly.  Kept live so that the two ends
of R8's scan branch cannot drift apart. -/
theorem VInductDecl'.LECond.of_elimLoop {D : VInductDecl'} {T : VIndType} {C : VIndCtor}
    {Small : Nat → Prop} (hT : D.types = [T]) (hC : T.ctors = [C])
    (hlvl : ∀ k F, C.fields[k]? = some F → Small k → F.lvl ≈ VLevel.zero)
    (h : ∀ k F, C.fields[k]? = some F →
      Small k ∨ VExpr.bvar (C.fields.length - 1 - k) ∈ C.args) :
    D.LECond :=
  VInductDecl'.LECond.of_scan hT hC fun k F hF =>
    (h k F hF).imp (hlvl k F hF) id

end AddInductive
end Lean4Lean
