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

### Three side conditions, and why each is a finding rather than bookkeeping

`TrExprS` is not constant-preserving: two of its rules put constants into the `VExpr` that
are not in the `Expr` at all, and one reads a `VExpr` out of the context rather than out of
the term.  So the transfer needs exactly three hypotheses, and each records a place where
`hasIndOcc` is *blind* — a genuine incompleteness of the syntactic check relative to the
abstract predicate, not an artifact of this proof.

* `hctx` — a `.bvar`/`.fvar` translates to whatever the `VLCtx` maps it to.  For a `vlam`
  entry that is `.bvar _`, which is block-free outright; for a `vlet` entry it is the *value*,
  an arbitrary term the source variable does not display.  Threaded through the induction,
  so the binder cases have to re-establish it — which is why `NoConsts.liftN` is needed.

* `hlit` — `TrExprS.lit` translates `.lit l` through `l.toConstructor`, so a numeral
  introduces `Nat.zero`/`Nat.succ` and a string literal `String.ofList`, `List.nil`,
  `List.cons`, `Char.ofNat`.  `hasIndOcc` sees a `.lit` node and no `.const` node at all.
  A block declaring an inductive *type* under one of those six names would therefore pass
  the positivity check while its translation mentions the block — the freshness of the block
  names in the pre-block environment does not rule this out, because the literal is
  translated at the *staged* environment where the block's types are already declared.

* `hproj` — `TrProj` expands `.proj s i e` into `VInductDecl'.projTerm`, which splices in the
  structure's recursor name, its stored field types, **and the parameter/index arguments `ps`,
  `ιs` read off the type of `e`**.  Those arguments are not syntactically present in
  `.proj s i e`, so a block occurrence carried only by them is invisible to `hasIndOcc`.
  This is the sharper of the two: the field types and recursor name come from a declaration
  that predates the block, but `ps` is an arbitrary term of the local context.

None of the three is discharged here, and none should be quietly assumed: they are the exact
statement of what `hasIndOcc` does not see.  The C++ kernel's `has_ind_occ` is equally blind,
so this is a question about the *specification* `VIndField.WF.pos` versus both kernels, not a
divergence between them. -/

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
    {l : List (FVarId × List FVarId × VExpr)} {k fv deps A} {Δ₀ : VLCtx}
    (hΔ : Δ = VLCtx.mkFVars l.reverse Δ₀)
    (hnd : (l.map (·.1)).Nodup) (hk : l[k]? = some (fv, deps, A))
    (hlen : l.length = C.fields.length)
    (hres : TrExprS env Us Δ type (C.canonResult D j))
    (hmem : Lean.Expr.fvar fv ∈ type.getAppArgsRevList) :
    VExpr.bvar (C.fields.length - 1 - k) ∈ C.args := by
  subst hΔ
  obtain ⟨B, hfind⟩ := VLCtx.find?_mkFVars_rev (Δ := Δ₀) hnd hk
  obtain ⟨a', ha', hmem'⟩ := hres.mem_spineArgs _ hmem
  rw [ha'.fvar_det hfind, hlen] at hmem'
  rw [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.spineArgs_mkApp, VExpr.spineArgs_const,
    List.nil_append, List.mem_append] at hmem'
  refine hmem'.resolve_left (VExpr.not_mem_bvars_of_lt ?_)
  have hlt : k < l.length := by
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hk; exact absurd hk nofun
  omega

end Lean4Lean
