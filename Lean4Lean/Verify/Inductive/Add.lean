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
  trenv : TrEnv safety env venv
  vlctx : VLCtx
  trlctx : TrLCtx venv lparams lctx vlctx
  /-- **The relocated freshness invariant.**  The type checker keeps its `NameGenerator` in
  *state*, so freshness lives in `VState.WF`.  `AddInductive.M` keeps it in the *reader*
  (`withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }`), so the obligation does
  not disappear with the state — it moves here.

  Stated over `vlctx.fvars` rather than `lctx.find?`: `TrLCtx` ties the two
  (`TrLCtx.find?_eq_none`), and the `VLCtx` side has the `cons` simp lemmas that make the
  push case one line. -/
  reserves : ∀ fv ∈ vlctx.fvars, ngen.Reserves fv

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
    vlctx := (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') :: c.vlctx
    trlctx := c.trlctx.mkLocalDecl c.fresh htr hty
    reserves := by
      intro fv hfv
      rw [VLCtx.fvars_cons_some, List.mem_cons] at hfv
      rcases hfv with rfl | hfv
      · exact NameGenerator.next_reserves_self
      · exact (c.reserves fv hfv).mono NameGenerator.LE.next }

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

end AddInductive
end Lean4Lean
