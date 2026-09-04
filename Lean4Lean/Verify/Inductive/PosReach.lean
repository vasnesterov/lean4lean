import Lean4Lean.Verify.Inductive.PosScan

/-!
# Is `PosIndex` §3.2's counterexample **reachable**?  No — and the repair it forces

`Verify/Inductive/PosIndex.lean` §3.2 (`binders_noBlock_not_transferable`) exhibits a field type
whose `Expr`-side positivity telescope is empty — so `PosScan`'s `checkPositivity_binderDoms` is
*vacuous* on it — while its `TrExprS` translation has a pi binder carrying a block constant.  That
witness is what makes §4.2's `hlen` hypothesis indispensable.  The question this file answers is
whether such a field type can reach `VIndField.WF.pos`'s consumers at all, i.e. whether
`checkPositivity` **accepts** it.

**It does not**, and the mechanism is one arm of `whnf'`.  `checkPositivity.loop`'s first act is
`whnf`, and `whnf'`'s second match arm (`Lean4Lean/TypeChecker.lean`:531) is
`| .mdata _ e => return ← whnf' e`.  So the loop descends *past* the annotation the witness hides its
pi behind, reaches the `.forallE` arm, tests `hasIndOcc stats.indConsts dom` on the block-carrying
domain, and **throws**.  The information §3.2 says is missing on the `Expr` side is missing from
`checkPositivity_binderDoms`' **statement**, not from `checkPositivity`'s **behaviour**.

So this is not a soundness bug — `bugs-found.md` is untouched — and it is not a licence to keep
`hlen` as it stood either, because §3.2 remains a true theorem about `posBinderDoms`.  The repair is
to weaken the hypothesis to the arity **`TrExprS` actually sees**, which is
`(Lean.Expr.consumeMData t).piArity`: `TrExprS.mdata` passes straight through, so stripping head
annotations changes neither side of the translation, and §4's `checkPositivity` invariance says the
checker's answer is unchanged too.  `PosIndex` §4.2 now carries that form.

## Contents

* **§1 `whnf` at a `.mdata`** — `whnf_mdata`, the `.mdata` twin of `PosScan`'s `whnf_forallE`, and
  the reason it is an *equality* of `M Expr` values where `whnf_forallE` is an implication.
* **§2 the same for `checkPositivity`** — `checkPositivity.loop` is invariant under a head `.mdata`
  at the *same* fuel, hence under `Lean.Expr.consumeMData`; and `TrExprS` is too.
* **§3 the rejection** — any field type whose `consumeMData` is a pi with a block-carrying domain is
  thrown out, at every fuel.  §3.2's witness is an instance (`PosIndex` §3.3 fires it).
* **§4 the arity gap is real anyway** — an `#eval` tripwire: `Lean4Lean.addDecl` **accepts** an
  `.mdata`-wrapped *positive* field, and rejects the non-positive one.  So the `Expr`/`VExpr` arity
  mismatch §3.2 exploits is reachable; only its *non-positive* instance is not.
* **§5 the limits**, including the one general theorem this round did not attempt and why.
-/

set_option autoImplicit false

namespace Lean4Lean

/-! ## §1 `whnf` at a `.mdata`

`PosScan` §3.2's `whnf_forallE` is the only `whnf`-behaviour lemma in `Verify/Inductive/`, and
`PosScan` §5(b)(2) states the `.mdata` fact as *prose about the source*.  Here it is as a theorem.

Two things make it stronger than its `.forallE` sibling, and both come from the same reading of
`whnf'`:

* it is an **equality of `M Expr` values**, not an implication from success, because the `.mdata` arm
  returns before the `whnfCache` lookup — so `whnf (.mdata m e)` and `whnf e` are the *same*
  computation, agreeing on failure as well as success (at `recDepth = 0` both throw
  `.deepRecursion`);
* it is general in `e`, with no premise on the annotated term's head.

It is nevertheless **not** `rfl`: `Inner.whnf'` is compiled by structural recursion (`brecOn`), so
the `.mdata` equation has to be brought in as an equation lemma.  Measured — `rfl` is rejected with
"Not a definitional equality". -/

namespace AddInductive
open Lean hiding Environment Exception
open Kernel

/-- **`whnf` descends past a `.mdata`.**  The annotation is stripped before the cache is consulted
and without consuming `Methods.withFuel`'s `recDepth` — `whnf'`'s `.mdata` arm recurses into `whnf'`
at the *same* method dictionary — so this is an equality of computations and needs no induction. -/
theorem whnf_mdata {m : MData} {e : Expr} :
    (liftM (TypeChecker.whnf (.mdata m e)) : M Expr) = (liftM (TypeChecker.whnf e) : M Expr) := by
  funext c
  simp only [liftM, monadLift, MonadLift.monadLift, TypeChecker.whnf, TypeChecker.Inner.whnf,
    TypeChecker.RecM.run, TypeChecker.M.run, readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, bind, StateT.bind, StateT.pure, pure, StateT.run', Except.bind,
    Functor.map, Except.map, Except.pure]
  cases hr : c.fuel.recDepth with
  | zero => simp only [TypeChecker.Methods.withFuel]
  | succ k => simp only [TypeChecker.Methods.withFuel, TypeChecker.Inner.whnf']

/-! ## §2 `checkPositivity` under a head `.mdata`, and `Lean.Expr.consumeMData`

`Lean.Expr.consumeMData` is upstream, and — unlike `Lean.Expr.consumeTypeAnnotations`, which is
`partial` and is why `Inductive/Add.lean` had to hand-write `consumeAnnotations` — it is an ordinary
structural recursion with a usable body.  So no new definition is introduced here, and guard 3's
frozen list is untouched. -/

/-- Head `.mdata` is invisible to `checkPositivity.loop`, at the **same** fuel: the annotation is
consumed by `whnf`, which the loop calls before it matches, and no fuel is spent doing it. -/
theorem checkPositivity_loop_mdata {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {m : MData} {e : Expr} : ∀ (fuel : Nat) (c : Context),
      checkPositivity.loop stats ctor idx (.mdata m e) fuel c
        = checkPositivity.loop stats ctor idx e fuel c
  | 0, _ => by rw [checkPositivity.loop, checkPositivity.loop]
  | _+1, _ => by rw [checkPositivity.loop, checkPositivity.loop, whnf_mdata]

end AddInductive

open Lean in
@[simp] theorem consumeMData_mdata {m : MData} {e : Expr} :
    (Expr.mdata m e).consumeMData = e.consumeMData := rfl

open Lean in
/-- `consumeMData` is the identity on every head but `.mdata`.  Stated as ten `rfl`s rather than a
`match` so that it is usable as a `simp` lemma at an unknown head. -/
theorem consumeMData_eq_self : ∀ {e : Expr}, (∀ m b, e ≠ .mdata m b) → e.consumeMData = e
  | .bvar _, _ | .sort _, _ | .const .., _ | .fvar _, _ | .mvar _, _ | .lit _, _
  | .app .., _ | .lam .., _ | .forallE .., _ | .letE .., _ | .proj .., _ => rfl
  | .mdata m b, h => absurd rfl (h m b)

namespace AddInductive
open Lean hiding Environment Exception
open Kernel

/-- The iterated form of `checkPositivity_loop_mdata`: an arbitrarily deep annotation stack is
invisible to the loop, still at the same fuel.  Structural recursion on the annotation stack — the
only recursive step is the `.mdata` one. -/
theorem checkPositivity_loop_consumeMData {stats : InductiveStats} {ctor : Name} {idx : Nat} :
    ∀ (t : Expr) (fuel : Nat) (c : Context),
      checkPositivity.loop stats ctor idx t.consumeMData fuel c
        = checkPositivity.loop stats ctor idx t fuel c
  | .mdata _ e, fuel, c => by
      rw [consumeMData_mdata, checkPositivity_loop_consumeMData e fuel c,
        checkPositivity_loop_mdata]
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ | .fvar _, _, _ | .mvar _, _, _
  | .lit _, _, _ | .app .., _, _ | .lam .., _, _ | .forallE .., _, _ | .letE .., _, _
  | .proj .., _, _ => rfl

/-- …and at the entry point `checkConstructors` actually calls. -/
theorem checkPositivity_consumeMData {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {t : Expr} {c : Context} :
    checkPositivity stats t.consumeMData ctor idx c = checkPositivity stats t ctor idx c := by
  rw [checkPositivity, checkPositivity]
  simp only [bind, ReaderT.bind, Except.bind, readThe, MonadReaderOf.read, ReaderT.read, pure]
  exact checkPositivity_loop_consumeMData t c.fuel.inductiveFuel c

/-! ### §2.1 the `Expr`-side scan, read off the stripped term

The composition that `PosIndex` §4.2 consumes: `checkPositivity`'s success on the **stored** field
type gives block-freeness of every domain of the **stripped** term's telescope, which is the
telescope `TrExprS` sees. -/

/-- `PosScan.checkPositivity_binderDoms`, transported across the annotation stack. -/
theorem checkPositivity_binderDoms_consumeMData {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {t : Expr} {c : Context} {u : Unit} (h : checkPositivity stats t ctor idx c = .ok u) :
    ∀ B ∈ posBinderDoms t.consumeMData, hasIndOcc stats.indConsts B = false :=
  checkPositivity_binderDoms (checkPositivity_consumeMData.trans h)

/-! ## §3 The rejection

The theorem that kills §3.2's witness, and it kills the whole *shape*: not just an `.mdata` over a
non-positive pi, but any annotation stack over one.

Prior S4 of `docs/handoff-posreach.md` §1 decided in advance that the rejection had to route through
the `hasIndOcc dom` throw and never through `isValidIndApp? = none`, because `isValidIndAppIdx`'s
head test is `Lean.Expr.eqv`, an `@[extern]` `opaque` that no closed input can evaluate.  That is the
route taken: the only fact consumed is `hasIndOcc stats.indConsts dom = true`, and `hasIndOcc` is
`anySub`, pure total Lean. -/

/-- A block occurrence in a domain is a block occurrence in the pi. -/
theorem hasIndOcc_forallE_of_dom (indConsts : Array Expr) (nm : Name) (dom body : Expr)
    (bi : BinderInfo) (h : hasIndOcc indConsts dom = true) :
    hasIndOcc indConsts (.forallE nm dom body bi) = true := by
  rw [hasIndOcc_eq] at h ⊢
  rw [anySub_forallE_eq, h]
  simp

/-- **The loop rejects, at every fuel.**  Three ways in: no fuel at all (`throw .deepRecursion`), or
`checkPositivity_loop_forallE`'s two disjuncts, both of which contradict `hocc`.  The `.mdata` stack
is removed first by §2. -/
theorem checkPositivity_loop_reject {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {t : Expr} {nm : Name} {dom body : Expr} {bi : BinderInfo}
    (ht : t.consumeMData = .forallE nm dom body bi)
    (hocc : hasIndOcc stats.indConsts dom = true) :
    ∀ (fuel : Nat) (c : Context) (u : Unit),
      checkPositivity.loop stats ctor idx t fuel c ≠ .ok u := by
  intro fuel c u h
  rw [← checkPositivity_loop_consumeMData, ht] at h
  cases fuel with
  | zero => rw [checkPositivity.loop] at h; exact absurd h nofun
  | succ k =>
    rcases checkPositivity_loop_forallE h with hnone | ⟨hd, -⟩
    · rw [hasIndOcc_forallE_of_dom _ nm dom body bi hocc] at hnone; exact absurd hnone (by simp)
    · rw [hocc] at hd; exact absurd hd (by simp)

/-- **`checkPositivity` rejects.**  The entry point `checkConstructors` calls on each field. -/
theorem checkPositivity_reject {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {t : Expr} {nm : Name} {dom body : Expr} {bi : BinderInfo} {c : Context} {u : Unit}
    (ht : t.consumeMData = .forallE nm dom body bi)
    (hocc : hasIndOcc stats.indConsts dom = true) :
    checkPositivity stats t ctor idx c ≠ .ok u := by
  intro h
  rw [checkPositivity] at h
  obtain ⟨-, -, h⟩ := M_bind_ok h
  exact checkPositivity_loop_reject ht hocc _ c u h

/-- The witness shape of `PosIndex` §3.2 verbatim: `.mdata m ((_ : I) → I)` at a one-member block
`#[.const I []]`.  The `hasIndOcc` fact is evaluated rather than assumed. -/
theorem checkPositivity_reject_mdata_witness {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {I : Name} (hI : stats.indConsts = #[.const I []])
    {m : MData} {nm : Name} {c : Context} {u : Unit} :
    checkPositivity stats (.mdata m (.forallE nm (.const I []) (.const I []) .default))
      ctor idx c ≠ .ok u :=
  checkPositivity_reject rfl (by rw [hI, hasIndOcc_const]; simp [Lean.Expr.constName!])

end AddInductive

/-! ### §3.1 `TrExprS` does not see the annotation either

The other half of the repair: stripping head annotations changes nothing on the `VExpr` side, because
`TrExprS.mdata` is `TrExprS Δ e e' → TrExprS Δ (.mdata d e) e'` — no side condition, same target. -/

variable {env : VEnv} {Us : List Name}

open Lean in
/-- **`TrExprS` passes straight through an annotation stack.**  So `(consumeMData t).piArity` is the
arity the translation sees, and `TrExprS.piArity_le` sharpens to it. -/
theorem TrExprS.consumeMData :
    ∀ {Δ : VLCtx} {t : Expr} {S : VExpr}, TrExprS env Us Δ t S →
      TrExprS env Us Δ t.consumeMData S
  | _, .mdata _ _, _, H => by
      let .mdata H' := H
      rw [consumeMData_mdata]; exact H'.consumeMData
  | _, .bvar _, _, H | _, .sort _, _, H | _, .const .., _, H | _, .fvar _, _, H
  | _, .mvar _, _, H | _, .lit _, _, H | _, .app .., _, H | _, .lam .., _, H
  | _, .forallE .., _, H | _, .letE .., _, H | _, .proj .., _, H => H


/-! ## §4 The arity gap is real anyway — an executable tripwire

The counterexample is unreachable; the **shape** it exploits is not.  `Lean4Lean.addDecl` accepts an
`.mdata`-wrapped *positive* field, so a field type whose `posBinderDoms` is empty while its
`TrExprS`-visible telescope has a binder does occur in accepted declarations.  That is why weakening
`hlen` to `(consumeMData t).piArity` is the right repair and dropping it altogether is not.

**Why this is a tripwire and not a demonstration.**  `PosIndex` §4.2's weakened `hlen` is
*satisfiable at §3.2's own witness* (`t.consumeMData.piArity = 1 = r.binders.length`), so
`recArgOf_binders_noBlock` is saved from §3.2 by its `hchk` hypothesis **alone** — by the rejection of
§3, and by nothing else.  If `whnf'` ever stopped descending past `.mdata`, or `checkPositivity`
stopped calling `whnf` first, `recArgOf_binders_noBlock` would become **false**.  The build fails here
rather than in prose if any of the three arms flips.  Models: `RestoreFaithful.lean` §5.1 and
`NoNestedAll.lean` §5. -/

namespace PosReachWit
open Lean

/-- `W : Type → Type`. -/
def wTy : Expr := .forallE `α (.sort (.succ .zero)) (.sort (.succ .zero)) .default

/-- `mk : ∀ {α}, FIELD → W α`, with `FIELD` the field type under test. -/
def wCtor (N : Name) (fld : Expr) : Expr :=
  .forallE `α (.sort (.succ .zero))
    (.forallE `f fld (.app (.const N []) (.bvar 1)) .default) .implicit

/-- The plain positive field `(_ : α) → W α`. -/
def fldGood : Expr := .forallE `a (.bvar 0) (.app (.const `WGood []) (.bvar 1)) .default

/-- The same, annotated — the shape whose `posBinderDoms` is empty. -/
def fldGoodM : Expr :=
  .mdata {} (.forallE `a (.bvar 0) (.app (.const `WMD []) (.bvar 1)) .default)

/-- `PosIndex` §3.2's shape at a real block member: `.mdata m ((_ : W α) → W α)`. -/
def fldBadM : Expr :=
  .mdata {} (.forallE `a (.app (.const `WBad []) (.bvar 0))
    (.app (.const `WBad []) (.bvar 1)) .default)

def tryInd (N : Name) (fld : Expr) : Except Kernel.Exception Kernel.Environment :=
  Lean4Lean.addDecl (Kernel.Environment.empty `main)
    (.inductDecl [] 1
      [{ name := N, type := wTy, ctors := [{ name := N ++ `mk, type := wCtor N fld }] }] false)

/-- **The arity gap, at the field the tripwire shows is accepted.**  The `Expr`-side scan sees no
binder at all; `TrExprS` sees one.  Both by `rfl`, no environment and no `decide`. -/
theorem fldGoodM_gap :
    posBinderDoms fldGoodM = [] ∧ fldGoodM.consumeMData.piArity = 1 ∧ fldGoodM.piArity = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- The same gap at `PosIndex` §3.2's non-positive shape — identical arities, and §3 is the only
thing standing between it and `recArgOf_binders_noBlock`'s conclusion. -/
theorem fldBadM_gap :
    posBinderDoms fldBadM = [] ∧ fldBadM.consumeMData.piArity = 1 ∧ fldBadM.piArity = 0 :=
  ⟨rfl, rfl, rfl⟩

/-! ### §4.1 The measurement, self-checking

If the positive annotated field is ever **rejected**, §4's claim that the arity gap occurs in
accepted declarations is void and `hlen`'s weakened form is unmotivated.  If the non-positive
annotated field is ever **accepted**, `whnf` has stopped descending past `.mdata`,
`checkPositivity_reject` is contradicted, and `PosIndex.recArgOf_binders_noBlock` is **false** — that
is the alarm this round stood down, re-armed. -/
#eval show Lean.CoreM Unit from do
  let good := tryInd `WGood fldGood
  let goodM := tryInd `WMD fldGoodM
  let badM := tryInd `WBad fldBadM
  unless good.toOption.isSome do
    throwError "PosReach/§4: `Lean4Lean.addDecl` REJECTS the plain positive field \
      `(_ : α) → W α` -- the baseline is broken, so neither of the other two arms means anything"
  unless goodM.toOption.isSome do
    throwError "PosReach/§4: `Lean4Lean.addDecl` REJECTS the ANNOTATED POSITIVE field \
      `.mdata \{} ((_ : α) → W α)`.  The Expr/VExpr arity gap no longer occurs in an accepted \
      declaration, so §4's motivation for weakening `PosIndex.recArgOf_binders_noBlock`'s `hlen` to \
      `(consumeMData t).piArity` is void -- re-derive it or revert the weakening"
  unless badM.toOption.isNone do
    throwError "PosReach/§4: `Lean4Lean.addDecl` ACCEPTS the ANNOTATED NON-POSITIVE field \
      `.mdata \{} ((_ : W α) → W α)`.  This is `PosIndex` §3.2's counterexample, REACHABLE.  \
      `whnf` has stopped descending past `.mdata` (TypeChecker.lean:531) or `checkPositivity` has \
      stopped calling `whnf` first, so `AddInductive.checkPositivity_reject` is contradicted and \
      `PosIndex.recArgOf_binders_noBlock` is FALSE, not merely unproved.  This is a soundness alarm: \
      stop and re-run `docs/handoff-posreach.md`"
  Lean.logInfo "PosReach/§4: plain positive field ACCEPTED, `.mdata`-wrapped POSITIVE field \
    ACCEPTED (so the Expr/VExpr arity gap is real in an accepted declaration), `.mdata`-wrapped \
    NON-POSITIVE field REJECTED (so `PosIndex` §3.2's counterexample is UNREACHABLE and \
    `recArgOf_binders_noBlock`'s weakened `hlen` is sound) ✓"

end PosReachWit

/-! ## §5 The limits

**(a) What is proved.**  `whnf` descends past `.mdata` (§1, an equality of computations, general in
`e`, no fuel or environment hypothesis); `checkPositivity` inherits that at every fuel and at the entry
point (§2); and any annotation stack over a pi with a block-carrying domain is **rejected** (§3).
`PosIndex` §3.2's counterexample is an instance, so it is not reachable and `bugs-found.md` is not
touched.

**(b) What the rejection does *not* say.**  It is about the `hasIndOcc dom` throw only.  Nothing here
proves anything about the *other* rejection path, `isValidIndApp? = none`, and by prior S4 nothing
here can: `isValidIndAppIdx`'s head test is `Lean.Expr.eqv`, an `@[extern]` `opaque`, so that branch
is not evaluable at any closed input.  A field whose annotation hides an *invalid application* rather
than a non-positive pi is therefore outside this file's reach, and `PosScan` §5(c) is where that limit
is recorded.

**(c) No `decide` was added, and none could have been.**  §1 costed §3 as "`decide` on one
`hasIndOcc`".  `decide` fails twice over: the witness's block name is a bound `Name` (so the goal has
free variables), and `PosScan` §3.5 already records that `Array.any` routes through `Array.anyM.loop`,
which is well-founded and does not reduce in the kernel.  The discharge is `hasIndOcc_const` plus
`simp [Lean.Expr.constName!]` — rewriting.  So `PosScan`'s and `PosIndex`'s deliberate avoidance of
`decide` at the residual clause is not regressed here.

**(d) The general theorem is still not proved, and it is still the right next target.**  "The loop
scans every `VExpr` binder", which would delete the arity hypothesis rather than weaken it, needs a
`whnf`-closed binder-domain collector.  §1 and `PosIndex` §7(d) price it identically and this round
does not attempt it: its `.mdata` clause is now cheap (that is §2), but its `.letE` clause is not —
the whnf-faithful reading is `posBinderDoms (b.instantiate1 v)`, which is not structural, and its
`TrExprS` counterpart is a `vlet` **context** entry rather than a substitution, so it needs the R1/R2
dictionary relating `VLCtx` `vlet` entries to the `LocalContext`'s `ldecl`s.  Deliberately left; this
round weakens the hypothesis to the arity that is *actually* available and shows the weakened form is
tight.

**(e) The weakened `hlen` is tight, and §4 is why that matters.**  At §3.2's witness the weakened
hypothesis is *satisfied* (`fldBadM_gap`: `consumeMData` arity 1, `r.binders.length` 1), so
`PosIndex.recArgOf_binders_noBlock` is saved by `hchk` alone.  Its truth therefore **depends** on §3's
rejection; §4's tripwire is not decoration.

**(f) `VIndRecArg.exists_indep` is untouched and off this path**, for the reason `PosIndex` §7(g)
gives: every statement here is about `NoBlock` of a telescope entry or about `checkPositivity`'s
control flow, and neither mentions an `∃` over independent binders. -/

#print axioms Lean4Lean.AddInductive.whnf_mdata
#print axioms Lean4Lean.AddInductive.checkPositivity_loop_mdata
#print axioms Lean4Lean.consumeMData_mdata
#print axioms Lean4Lean.consumeMData_eq_self
#print axioms Lean4Lean.AddInductive.checkPositivity_loop_consumeMData
#print axioms Lean4Lean.AddInductive.checkPositivity_consumeMData
#print axioms Lean4Lean.AddInductive.checkPositivity_binderDoms_consumeMData
#print axioms Lean4Lean.AddInductive.hasIndOcc_forallE_of_dom
#print axioms Lean4Lean.AddInductive.checkPositivity_loop_reject
#print axioms Lean4Lean.AddInductive.checkPositivity_reject
#print axioms Lean4Lean.AddInductive.checkPositivity_reject_mdata_witness
#print axioms Lean4Lean.TrExprS.consumeMData
#print axioms Lean4Lean.PosReachWit.fldGoodM_gap
#print axioms Lean4Lean.PosReachWit.fldBadM_gap

end Lean4Lean
