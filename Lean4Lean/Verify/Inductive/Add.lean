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
namespace AddInductive
open Lean hiding Environment Exception
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


/-! ## R7: strict positivity — **blocked on an unmodelled `@[extern] opaque`**

`checkPositivity` (`Add.lean:184`) rejects on `hasIndOcc stats.indConsts …`; its *success*
is what would establish `VIndField.WF.pos`, whose `none` branch is the positive statement
`∃ A, D.NoBlock A ∧ env.IsDefEqType D.uvars Γ F.type A`.  The only evidence for it is
`hasIndOcc (← whnf dom) = false`.  So R7 must read `hasIndOcc`.

```
def hasIndOcc (indConsts : Array Expr) (t : Expr) : Bool :=
  (t.find? fun | .const e _ => indConsts.any fun I => I.constName! == e | _ => false).isSome
```

and `Lean.Expr.find? p e = findImpl? p e` where (`~/lean4/src/Lean/Util/FindExpr.lean:16`)

```
@[extern "lean_find_expr"] opaque findImpl? (p : @& (Expr → Bool)) (e : @& Expr) : Option Expr
```

**`findImpl?` is `opaque`: it has no body at all.**  Not `partial`, not
`@[implemented_by]` — there is nothing in Lean to unfold, so no amount of work inside this
file can say what `hasIndOcc` computes.  Giving it a meaning requires a new interface axiom in
`Lean4Lean/Verify/Axioms.lean`, alongside `Lean.Expr.replace_eq`, `Lean.Expr.abstract_eq` and
the rest.  That file is frozen, and the change would move its count in the wrong direction.
**So R7 is blocked, and it is blocked on a policy question rather than a proof difficulty.**

Note this is *not* a `Guard.lean` check-3 violation: check 3 filters to constants defined in
`Lean4Lean.*` modules (`unless (`Lean4Lean).isPrefixOf modName do continue`), and `findImpl?`
is upstream.  It is a **trusted-base** fact, not a guard-list fact — the strict-positivity
check, one of the two places where an inductive declaration can be unsound, currently rests on
a C function with no Lean-side model, and nothing in the tree records that.

**The recommended fix is not an axiom.**  `hasIndOcc` uses `find?` only through `.isSome`, so
it is asking "does any subterm match?", and the traversal order and the extern cache are both
invisible to the answer.  Replacing it with a structurally recursive `Expr` walk in
`Lean4Lean/Inductive/Add.lean` removes the dependency outright — shrinking the trusted base
rather than growing the axiom list, and faithful to the C++ kernel, whose `has_ind_occ` is the
same existential question.  That is an edit to a file this stream does not own, so it is a
recommendation, not a change.

## R8: the large-elimination flag

`isLargeEliminator` (`Add.lean:258`) has two branches, and they separate cleanly.

**The `isNotZero` branch closes here** — `stats.isNotZero` is `resultLevel.isNeverZero`
(`Add.lean:101`), and `ofLevel_isNeverZero` carries it to `D.lvl.IsNeverZero`, which is
`LECond`'s first disjunct verbatim.

**The scan branch is gated on R1/R2**, and this is worth stating precisely because the
*direction* of the gate is the opposite of what the row's price assumed.  The scan itself is
sound in exactly the direction `LECond` needs: `isAlwaysZero` is a sound-but-incomplete
syntactic test, and a field is pushed onto `toCheck` when it *fails*, so a field **absent**
from `toCheck` really does have `F.lvl ≈ .zero` (`ofLevel_isAlwaysZero`), and a field
**present** in it is covered by the final `toCheck.all type.getAppArgs.contains`.  No
completeness is needed anywhere.  What is missing is the correspondence between the loop's
accumulated fvars and the spec's field indices — `arg_i ↦ .bvar (nf-1-i)` and
`type.getAppArgs ↦ C.args` — which is `TrIndCtor`'s telescope pinning, i.e. **R1/R2**, not a
row I hold as done.  The per-field step below is the part that does not depend on it. -/

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
end Lean4Lean
