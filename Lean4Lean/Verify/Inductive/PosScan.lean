import Lean4Lean.Verify.Inductive.WFPos

/-!
# The two `NoBlock` scans, read off the checker — and the index-arity conjunct, which is not a check

`Verify/Inductive/WFPos.lean` §3.1 reduced `VIndField.WF.pos`'s five *syntactic* conjuncts to
**B6's two-stage reader plus a three-part decidable check**: the index-arity equation, plus the two
`NoBlock` scans that it names as "the abstract form of `checkPositivity`'s `hasIndOcc` calls and
`isValidIndAppIdx`'s residual scan".  Its one-line statement of the gap — measured again here rather
than quoted — is that **`VIndRestore.recogAt` performs no `NoBlock` scan**: its guard
(`Theory/Inductive/NestedBuild.lean`:144) is exactly `b.spineFn = .const (R.tyName k) (R.tyLvls k)`,
`sp.take nA = (R.tyArgs k).map (·.liftN (ξ.length + i))`, and `nA ≤ sp.length`, with no occurrence
test and no arity comparison in it.

This file closes what can be closed of that check, and says exactly which part cannot be.

## Contents

* **§1 the three-part check is a two-part check.**  Part (A), the index-arity equation
  `r.args.length = (D.types.getD r.idx default).indices.length`, **is not an independent check at
  all** — it follows from conjunct 7 (`VIndField.PosTy.indexArgs`) together with the `r.idx < D.nm`
  the reader already supplies, by `VEnv.HasArgs.length_eq` and `VExpr.length_liftTele`.  So
  `posSyn_of_recArgOf`'s `hlen` hypothesis is redundant for any consumer who is also going to prove
  the typing half, which is every consumer there is.  `posSome_of_recArgOf` is the composed
  producer: reader + two scans + `PosTy` ⟹ the whole `some` branch.
* **§2 the residual scan, read off `isValidIndAppIdx`.**  `AddInductive.isValidIndAppIdx` is a pure
  `Bool` with no monad, no `whnf` and no context, so its success can be read outright.  Four
  theorems (`head`, `spine_len`, `params`, `residual_noOcc`) and then the shape the transfer wants,
  `anySub … = false` on every residual argument.  This is part (C) on the implementation side, and
  it is *also* where the checker's counterpart of part (A) lives (`spine_len`), which is why §1's
  finding is a strengthening and not a dodge.
* **§3 the binder scan, read off `checkPositivity`.**  Part (B).  `checkPositivity.loop`'s
  `.forallE` branch is the `throw` that establishes it, and it is reached only through a
  `whnf` in `AddInductive.M`, so unlike §2 this one cannot be a statement about a `Bool`.  §3 gives
  the step lemma about the raw monadic value — deliberately **not** through `TypeChecker.M.WF`, for
  the reason `NoNestedAll.lean` §3 gives and which is re-instantiated in §5 — and names the residue.
* **§4 the firing**, on the checker's own data, with no `decide` at the abstract residual clause.
* **§5 the limits**, each measured or proved.
-/

set_option autoImplicit false

namespace Lean4Lean

/-! ## §1 Part (A) is not a check: the index-arity equation follows from conjunct 7

`VIndField.PosTy.indexArgs` is
`∀ T', D.types[r.idx]? = some T' → env.HasArgs … (liftTele (r.binders.length + i) T'.indices) r.args`.
A `HasArgs` derivation equates the two lengths (`VEnv.HasArgs.length_eq`) and `liftTele` preserves
length (`VExpr.length_liftTele`), so the equation *is* the derivation's own length side condition.
The only thing needed to instantiate it is `r.idx < D.nm`, i.e. conjunct 1 — which
`VInductDecl'.recArgOf_idx_lt` supplies from the reader.

This is worth stating rather than inlining, because `WFPos` §3.1 counted it as one of three
*decidable* obligations to be discharged from the implementation, and it is not one: no
implementation fact enters. -/

namespace VIndField

/-- **The index-arity conjunct, from the typing half.**  `hidx` is conjunct 1, `hty` carries
conjunct 7; nothing else is used, and in particular no `VInductDecl'.WF` and no implementation. -/
theorem args_len_of_posTy {env : VEnv} {D : VInductDecl'} {Γ : List VExpr} {i : Nat}
    {F : VIndField} {r : VIndRecArg} (hidx : r.idx < D.nm)
    (hty : PosTy env D Γ i F r) :
    r.args.length = (D.types.getD r.idx default).indices.length := by
  have hget : D.types[r.idx]? = some (D.types.getD r.idx default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]; rfl
  have h := (hty.indexArgs _ hget).length_eq
  rw [VExpr.length_liftTele] at h
  exact h.symm

end VIndField

/-! ### §1.1 The composed producer: reader + two scans + `PosTy` gives the whole `some` branch

`WFPos`'s `posSyn_of_recArgOf` takes four hypotheses; §1 removes one of them for every consumer who
also has the typing half.  This is the composition stated as `VIndField.WF.mk`'s `pos` argument, so
that a producer never has to mention the arity equation at all. -/

namespace VIndField

/-- **`posSyn` from the reader and the two scans only.**  The arity conjunct is gone: it comes from
`hty`.  Conjunct 1 comes from `VInductDecl'.recArgOf_idx_lt` and conjunct 9 from `WFPos` §2. -/
theorem posSyn_of_recArgOf_posTy {env : VEnv} {D : VInductDecl'} {Γ : List VExpr} {i : Nat}
    {F : VIndField} {r : VIndRecArg}
    (h : D.recArgOf i F.type = some r)
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hargs : ∀ a ∈ r.args, D.NoBlock a)
    (hty : PosTy env D Γ i F r) :
    PosSyn D i F r :=
  posSyn_of_recArgOf h (args_len_of_posTy (Lean4Lean.recArgOf_idx_lt h) hty) hbind hargs

/-- **The whole `some` branch, from the reader, the two `NoBlock` scans, and the typing half.**
Nothing else: no arity equation, no `ResidualClean`, no `decide`. -/
theorem posSome_of_recArgOf {env : VEnv} {D : VInductDecl'} {Γ : List VExpr} {i : Nat}
    {F : VIndField} {r : VIndRecArg} (hr : F.recArg = some r)
    (h : D.recArgOf i F.type = some r)
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hargs : ∀ a ∈ r.args, D.NoBlock a)
    (hty : PosTy env D Γ i F r) :
    match F.recArg with
    | none => ∃ A, D.NoBlock A ∧ env.IsDefEqType D.uvars Γ F.type A
    | some r =>
      r.idx < D.nm ∧
      r.args.length = (D.types.getD r.idx default).indices.length ∧
      (∀ B ∈ r.binders, D.NoBlock B) ∧
      (∀ a ∈ r.args, D.NoBlock a) ∧
      OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars) ∧
      env.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl) ∧
      (∀ T', D.types[r.idx]? = some T' →
        env.HasArgs D.uvars (r.binders.reverse ++ Γ)
          (VExpr.liftTele (r.binders.length + i) T'.indices) r.args) ∧
      env.IsDefEqType D.uvars Γ F.type (r.canonType D i) ∧
      D.ResidualClean (r.binders.length + i) F.type :=
  posSome_of_split hr (posSyn_of_recArgOf_posTy h hbind hargs hty) hty

end VIndField

/-! ## §2 The residual scan and the checker's own arity test, read off `isValidIndAppIdx`

`AddInductive.isValidIndAppIdx` is the *only* place the kernel scans a recursive field's index
arguments for block occurrences, and — unlike `checkPositivity`, §3 — it is a **pure `Bool`**: no
monad, no `whnf`, no local context, no fuel.  So its success can be read outright, with no
`M.WF` and no well-formedness hypothesis anywhere.

`Verify/Inductive/CanonGapMeasure.lean` §3 already contains a *transcription* of this check
(`CGMGuard.cgmValidIndApp`) together with `cgm_synPos_iff`.  That is deliberately **not** this: it
is a candidate guard that is *stronger* than the kernel's (its own header records that installing it
would reject the auxiliary blocks `ElimNestedInductive.run` builds for `Lean.Json` and
`Lean.PrefixTreeNode`).  What is below is a statement about `AddInductive.isValidIndAppIdx` itself,
so no transcription fidelity question arises. -/

open Lean in
/-- **A `Bool`-valued `for` loop with an early `return false`, in closed form.**  This is the shape
`do`-notation produces for `for i in [a:b] do if p i then return false` inside `Id.run`: the
accumulator is `Option Bool × Unit`, `none` meaning "no early return yet".  Both of
`isValidIndAppIdx`'s loops have exactly this shape, and the second one is the `k` of the first. -/
theorem forIn_scan_run (p : Nat → Bool) : ∀ (l : List Nat),
    (forIn l ((none : Option Bool), ()) (fun i (_ : Option Bool × Unit) =>
        if p i = true then pure (ForInStep.done (some false, ()))
        else pure (ForInStep.yield ((none : Option Bool), ()))) : Id (Option Bool × Unit))
      = (if l.all (fun i => !p i) = true then ((none : Option Bool), ()) else (some false, ())) := by
  intro l
  induction l with
  | nil => simp; rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.all_cons]
    by_cases hp : p a = true
    · simp only [hp, if_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]; rfl
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, Bool.not_false, Bool.true_and, reduceIte, Bool.false_eq_true]
      exact ih

namespace AddInductive
open Lean

/-- **`isValidIndAppIdx`, in closed form.**  The two `for` loops become two `List.all`s over
`List.range'`, and the `unless` becomes the leading conjunct.  Everything in §2 is a corollary of
this one equation, which is why it is stated as an `=` on `Bool` rather than as an implication. -/
theorem isValidIndAppIdx_eq (stats : InductiveStats) (t : Expr) (i : Nat) :
    isValidIndAppIdx stats t i =
      ((t.getAppFn == stats.indConsts[i]! &&
          t.getAppArgs.size == stats.params.size + stats.nindices[i]!) &&
        (List.range' 0 stats.params.size).all (fun j => stats.params[j]! == t.getAppArgs[j]!) &&
        (List.range' stats.params.size (t.getAppArgs.size - stats.params.size)).all
          (fun j => !hasIndOcc stats.indConsts t.getAppArgs[j]!)) := by
  unfold isValidIndAppIdx
  rw [Lean.Expr.withApp_eq]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_scan_run, forIn_scan_run]
  simp only [bne, Bool.not_not]
  generalize (t.getAppFn == stats.indConsts[i]! &&
      t.getAppArgs.size == stats.params.size + stats.nindices[i]!) = A
  generalize ((List.range' 0 stats.params.size).all fun j => stats.params[j]! == t.getAppArgs[j]!) = B
  generalize ((List.range' stats.params.size (t.getAppArgs.size - stats.params.size)).all
      fun j => !hasIndOcc stats.indConsts t.getAppArgs[j]!) = C
  cases A <;> cases B <;> cases C <;> rfl

variable {stats : InductiveStats} {t : Expr} {i : Nat}

/-- **The head test, as far as it can be read without an axiom.**  `BEq Expr` is
`Lean.Expr.eqv` (`~/lean4/src/Lean/Expr.lean`:811), an `@[extern "lean_expr_eqv"] opaque` with no
Lean body, and it is *alpha*-equivalence ignoring binder names and annotations — so the strongest
axiom-free reading of this conjunct is the `Bool`, and an `Eq` conclusion would be **false** in
general.  `isValidIndAppIdx_head_const` below is the case where it is not. -/
theorem isValidIndAppIdx_head (h : isValidIndAppIdx stats t i = true) :
    (t.getAppFn == stats.indConsts[i]!) = true := by
  rw [isValidIndAppIdx_eq] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

/-- **The head test at a `.const`, where `eqv` *is* equality.**  `checkInductiveTypes` builds every
entry of `stats.indConsts` as `.const indType.name stats.levels` (`Lean4Lean/Inductive/Add.lean`), so
this hypothesis is discharged by construction at every real call site.

This one pays `Lean.Expr.eqv_eq` — the frozen interface axiom on guard 1's whitelist
(`Verify/Axioms.lean`, `Verify/Guard.lean`) that specifies the extern — via
`Lean.Expr.eqv_const`.  It is stated separately from `isValidIndAppIdx_head` precisely so that
`#print axioms` distinguishes the results that pay it from the ones that do not. -/
theorem isValidIndAppIdx_head_const {c : Name} {ls : List Lean.Level}
    (h : isValidIndAppIdx stats t i = true) (hc : stats.indConsts[i]! = .const c ls) :
    t.getAppFn = .const c ls :=
  Lean.Expr.eqv_const.1 (hc ▸ isValidIndAppIdx_head h)

/-- **The checker's arity test.**  This is the implementation counterpart of the conjunct that §1
shows is already implied by the typing half — kept because it is the *only* place the spine length
is pinned on the `Expr` side, and because §4 fires it. -/
theorem isValidIndAppIdx_numArgs (h : isValidIndAppIdx stats t i = true) :
    t.getAppArgs.size = stats.params.size + stats.nindices[i]! := by
  rw [isValidIndAppIdx_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

/-- The parameter prefix is the block's own parameter fvars, entrywise — **up to `Expr.eqv`, and
that is not `Eq`**: `eqv` ignores binder names and annotations, so this conjunct genuinely carries
alpha-equivalence and no more.  Nothing in this file upgrades it, and §5(c) says why that is the
honest statement rather than a gap. -/
theorem isValidIndAppIdx_params (h : isValidIndAppIdx stats t i = true)
    {j : Nat} (hj : j < stats.params.size) :
    (stats.params[j]! == t.getAppArgs[j]!) = true := by
  rw [isValidIndAppIdx_eq] at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.1.2 j (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)

/-- **The residual scan, read off the checker.**  Every argument past the parameter prefix carries
no block occurrence.  This is part (C) of `WFPos` §3.1's three-part check, on the implementation
side, and it costs no monad, no `whnf`, no fuel and no `WF`. -/
theorem isValidIndAppIdx_residual_noOcc (h : isValidIndAppIdx stats t i = true)
    {j : Nat} (hlo : stats.params.size ≤ j) (hhi : j < t.getAppArgs.size) :
    hasIndOcc stats.indConsts t.getAppArgs[j]! = false := by
  rw [isValidIndAppIdx_eq] at h
  simp only [Bool.and_eq_true] at h
  have := List.all_eq_true.1 h.2 j (List.mem_range'_1.2 ⟨hlo, by omega⟩)
  simpa using this

/-- The same in the form the syntactic→abstract transfer consumes: `TrExprS.noConsts` takes an
`anySub … = false`, not a `hasIndOcc … = false`, and `hasIndOcc_eq` is the bridge. -/
theorem isValidIndAppIdx_residual_anySub (h : isValidIndAppIdx stats t i = true)
    {j : Nat} (hlo : stats.params.size ≤ j) (hhi : j < t.getAppArgs.size) :
    anySub (fun e => match e with
      | .const c _ => stats.indConsts.any fun I => I.constName! == c
      | _ => false) t.getAppArgs[j]! = false := by
  exact (hasIndOcc_eq _ _).symm.trans (isValidIndAppIdx_residual_noOcc h hlo hhi)

/-- `isValidIndApp?`'s answer is a member index at which `isValidIndAppIdx` succeeds, so every
statement above transfers to the two-argument form the recursion actually calls. -/
theorem isValidIndAppIdx_of_isValidIndApp? {j : Nat} (h : isValidIndApp? stats t = some j) :
    isValidIndAppIdx stats t j = true := by
  rw [isValidIndApp?] at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  revert h
  generalize (List.range' 0 [:stats.indConsts.size].size 1) = l
  induction l with
  | nil => intro h; exact absurd h nofun
  | cons a l ih =>
    intro h
    rw [List.forIn_cons] at h
    by_cases ha : isValidIndAppIdx stats t a = true
    · simp only [ha, if_true] at h
      cases h; exact ha
    · simp only [ha, Bool.false_eq_true, if_false] at h
      exact ih h

/-- **The converse: the three readable conjuncts *suffice*.**  Together with the four projections
above this makes §2 an exact reading of the check rather than a one-way approximation, and it is what
§4.1's firing uses — a firing by `decide` is impossible here (see §5(c)). -/
theorem isValidIndAppIdx_of (hfn : (t.getAppFn == stats.indConsts[i]!) = true)
    (hlen : t.getAppArgs.size = stats.params.size + stats.nindices[i]!)
    (hp : ∀ j, j < stats.params.size → (stats.params[j]! == t.getAppArgs[j]!) = true)
    (hres : ∀ j, stats.params.size ≤ j → j < t.getAppArgs.size →
      hasIndOcc stats.indConsts t.getAppArgs[j]! = false) :
    isValidIndAppIdx stats t i = true := by
  rw [isValidIndAppIdx_eq]
  refine Bool.and_eq_true .. ▸ ⟨Bool.and_eq_true .. ▸ ⟨Bool.and_eq_true .. ▸ ⟨hfn, ?_⟩, ?_⟩, ?_⟩
  · exact beq_iff_eq.2 hlen
  · exact List.all_eq_true.2 fun j hj =>
      hp j (by have := List.mem_range'_1.1 hj; omega)
  · refine List.all_eq_true.2 fun j hj => ?_
    have hj' := List.mem_range'_1.1 hj
    rw [hres j hj'.1 (by omega)]
    rfl

end AddInductive

/-! ## §3 The binder scan, read off `checkPositivity`

Part (B), `∀ B ∈ r.binders, D.NoBlock B`.  Unlike §2 this cannot be a statement about a `Bool`:
`checkPositivity.loop` is monadic, it consumes fuel, it reduces with `whnf` at every step and it
descends under `withLocalDecl`.

**Deliberately not through `TypeChecker.M.WF`, and not through `AddInductive.M.WF` either.**  The
reason `NoNestedAll.lean` §3 gives is the one that applies: `checkConstantVal.WF` needs `ves.WF env`
and `VEnvs.WF` is unsatisfiable for any environment whose map holds an `.inductInfo`
(`VEnvs.WF.no_inductInfo`, `Verify/InductFlip.lean`), so a fact routed through it would be vacuous at
every environment that has an inductive in it.  `docs/handoff-posscan.md` §2 instantiates that
rather than repeating the prose.  A second, independent reason applies here: the only existing
statement about `whnf` in `AddInductive.M` is `M.WF.whnf`, whose postcondition is a `TrExpr`, i.e. an
untyped `IsDefEqU` — and `M.WF.positivity_none`, which uses it, has `VEnv.IsDefEq.uniq` in its cone
(measured, `docs/handoff-posscan.md` §2 M2).  Everything below is about the raw monadic value and its
cone stays clean.

**The fact that makes part (B) closable at all** is `whnf_forallE`: `whnf'`'s first match arm
(`Lean4Lean/TypeChecker.lean`:529) returns a `.forallE` unchanged, with no cache lookup and no fuel
consumed.  So the loop's `let t ← whnf t` is the **identity while the term is pi-headed**, and the
descent therefore walks the *stored* syntactic pi telescope — the same telescope
`VIndRestore.recogAt` splits with `splitPis S.piArity S`.  See §5(b) for where that stops being
true. -/

open Lean in
/-- The stored syntactic pi-domain telescope of an `Expr`.  Named `pos…` because
`CGMGuard.cgmBinderDoms` (`Verify/Inductive/CanonGapMeasure.lean`) is the same function under a
different name in a module that is **not** in this file's import closure; ledger row 113f's naming
rule applies. -/
def posBinderDoms : Expr → List Expr
  | .forallE _ dom b _ => dom :: posBinderDoms b
  | _ => []

open Lean in
/-- Every stored binder domain is a subterm, so a term-wide `anySub` miss is a miss at each of
them. -/
theorem posBinderDoms_noOcc {p : Expr → Bool} :
    ∀ {e : Expr}, anySub p e = false → ∀ B ∈ posBinderDoms e, anySub p B = false
  | .forallE _ d b _, h, B, hB => by
      rw [posBinderDoms, List.mem_cons] at hB
      obtain ⟨hd, hb⟩ := anySub_forallE h
      exact hB.elim (fun h => h ▸ hd) (posBinderDoms_noOcc hb B)
  | .bvar _, _, _, hB | .sort _, _, _, hB | .const .., _, _, hB | .fvar _, _, _, hB
  | .mvar _, _, _, hB | .lit _, _, _, hB | .app .., _, _, hB | .lam .., _, _, hB
  | .letE .., _, _, hB | .mdata .., _, _, hB | .proj .., _, _, hB => absurd hB nofun

open Lean in
/-- Instantiating shifts each stored domain, and each shifted domain is still a stored domain of the
instantiated term.  The depth `d'` is existential because it depends on how deep the domain sat. -/
theorem posBinderDoms_instantiate1' {a : Expr} :
    ∀ (e : Expr) (d : Nat), ∀ B ∈ posBinderDoms e,
      ∃ d', B.instantiate1' a d' ∈ posBinderDoms (e.instantiate1' a d)
  | .forallE _ t b _, d, B, hB => by
      rw [posBinderDoms, List.mem_cons] at hB
      rw [Expr.instantiate1', posBinderDoms]
      rcases hB with rfl | hB
      · exact ⟨d, List.mem_cons_self ..⟩
      · obtain ⟨d', hd'⟩ := posBinderDoms_instantiate1' b (d+1) B hB
        exact ⟨d', List.mem_cons_of_mem _ hd'⟩
  | .bvar _, _, _, hB | .sort _, _, _, hB | .const .., _, _, hB | .fvar _, _, _, hB
  | .mvar _, _, _, hB | .lit _, _, _, hB | .app .., _, _, hB | .lam .., _, _, hB
  | .letE .., _, _, hB | .mdata .., _, _, hB | .proj .., _, _, hB => absurd hB nofun

/-! ### §3.1 `anySub` under an fvar substitution -/

open Lean in
section
open Lean
variable {p : Lean.Expr → Bool}

theorem anySub_mdata_eq (m) (b) : anySub p (.mdata m b) = (p (.mdata m b) || anySub p b) := by
  rw [anySub_eq]
theorem anySub_proj_eq (s i) (b) : anySub p (.proj s i b) = (p (.proj s i b) || anySub p b) := by
  rw [anySub_eq]
theorem anySub_app_eq (f a) :
    anySub p (.app f a) = (p (.app f a) || (anySub p f || anySub p a)) := by rw [anySub_eq]
theorem anySub_lam_eq (n t b bi) :
    anySub p (.lam n t b bi) = (p (.lam n t b bi) || (anySub p t || anySub p b)) := by rw [anySub_eq]
theorem anySub_forallE_eq (n t b bi) :
    anySub p (.forallE n t b bi) = (p (.forallE n t b bi) || (anySub p t || anySub p b)) := by
  rw [anySub_eq]
theorem anySub_letE_eq (n t v b nd) :
    anySub p (.letE n t v b nd) =
      (p (.letE n t v b nd) || (anySub p t || anySub p v || anySub p b)) := by rw [anySub_eq]
theorem anySub_bvar_eq (i) : anySub p (.bvar i) = p (.bvar i) := by rw [anySub_eq]; simp
theorem anySub_const_eq (c us) : anySub p (.const c us) = p (.const c us) := by
  rw [anySub_eq]; simp

end

/-- `hasIndOcc` at a bare constant: the scan is the membership test and nothing else.  Needed for
§4.1, because the matcher `hasIndOcc_eq` produces does not evaluate under `decide` — `Array.any` goes
through `Array.anyM.loop`, which is well-founded and does not reduce in the kernel. -/
theorem hasIndOcc_const (indConsts : Array Lean.Expr) (c : Name) (us : List Lean.Level) :
    AddInductive.hasIndOcc indConsts (.const c us) = indConsts.any fun I => I.constName! == c := by
  rw [hasIndOcc_eq, anySub_const_eq]

section
open Lean
variable {p : Lean.Expr → Bool}
theorem anySub_fvar_eq (i) : anySub p (.fvar i) = p (.fvar i) := by rw [anySub_eq]; simp

/-- **Substituting an fvar for a loose bvar is invisible to a `.const`-only scan.**  This is what
lets the loop's evidence, which is about `body.instantiate1 (.fvar id)`, be read back as evidence
about the *stored* `body`.  It pays `Lean.Expr.instantiate1_eq` only at the call site, not here:
`instantiate1'` (`Verify/Axioms.lean`:680) is ordinary structural Lean. -/
theorem anySub_instantiate1'_fvar
    (hne : ∀ e : Lean.Expr, (∀ c us, e ≠ .const c us) → p e = false) (id : FVarId) :
    ∀ (e : Lean.Expr) (d : Nat), anySub p (e.instantiate1' (.fvar id) d) = anySub p e := by
  intro e
  induction e with
  | bvar i =>
    intro d
    rw [Expr.instantiate1', anySub_bvar_eq, hne _ (by simp)]
    split
    · rw [anySub_bvar_eq, hne _ (by simp)]
    · split
      · show anySub p ((Lean.Expr.fvar id).liftLooseBVars' 0 d) = false
        rw [show (Lean.Expr.fvar id).liftLooseBVars' 0 d = Lean.Expr.fvar id from rfl,
          anySub_fvar_eq, hne _ (by simp)]
      · rw [anySub_bvar_eq, hne _ (by simp)]
  | sort _ => intro d; rfl
  | const _ _ => intro d; rfl
  | fvar _ => intro d; rfl
  | mvar _ => intro d; rfl
  | lit _ => intro d; rfl
  | mdata m e ih =>
    intro d
    rw [Expr.instantiate1', anySub_mdata_eq, anySub_mdata_eq, ih, hne _ (by simp), hne _ (by simp)]
  | proj s i e ih =>
    intro d
    rw [Expr.instantiate1', anySub_proj_eq, anySub_proj_eq, ih, hne _ (by simp), hne _ (by simp)]
  | app f a ihf iha =>
    intro d
    rw [Expr.instantiate1', anySub_app_eq, anySub_app_eq, ihf, iha,
      hne _ (by simp), hne _ (by simp)]
  | lam n t b bi iht ihb =>
    intro d
    rw [Expr.instantiate1', anySub_lam_eq, anySub_lam_eq, iht, ihb,
      hne _ (by simp), hne _ (by simp)]
  | forallE n t b bi iht ihb =>
    intro d
    rw [Expr.instantiate1', anySub_forallE_eq, anySub_forallE_eq, iht, ihb,
      hne _ (by simp), hne _ (by simp)]
  | letE n t v b nd iht ihv ihb =>
    intro d
    rw [Expr.instantiate1', anySub_letE_eq, anySub_letE_eq, iht, ihv, ihb,
      hne _ (by simp), hne _ (by simp)]

end

open Lean in
/-- The `hasIndOcc` form of the invariance, proved where the predicate is *fixed* by `hasIndOcc_eq`.
Stating it separately is not cosmetic: `fun | .const e _ => … | _ => false` and
`fun e => match e with | .const c _ => … | _ => false` compile to **different** auxiliary matchers, so
a hand-written predicate does not `rw`-match the one `hasIndOcc_eq` produces. -/
theorem hasIndOcc_instantiate1'_fvar (indConsts : Array Expr) (id : FVarId) (e : Expr) (d : Nat) :
    AddInductive.hasIndOcc indConsts (e.instantiate1' (.fvar id) d)
      = AddInductive.hasIndOcc indConsts e := by
  rw [hasIndOcc_eq, hasIndOcc_eq]
  refine anySub_instantiate1'_fvar ?_ id e d
  intro e' he'
  cases e' <;> first | rfl | exact absurd rfl (he' _ _)

namespace AddInductive
open Lean hiding Environment Exception
open Kernel

/-! ### §3.2 The monadic plumbing, and `whnf` on a pi -/

/-- `AddInductive.M`'s `bind`, read backwards from success.  The analogue of `NoNestedAll.lean`'s
`M_bind_ok`, and simpler because `AddInductive.M` has no state. -/
theorem M_bind_ok {α β : Type} {x : M α} {f : α → M β} {c : Context} {r : β}
    (h : (x >>= f) c = .ok r) : ∃ a, x c = .ok a ∧ (f a) c = .ok r := by
  cases hx : x c with
  | error e => exact absurd h (by simp [(· >>= ·), ReaderT.bind, Except.bind, hx])
  | ok a => exact ⟨a, rfl, by simpa [(· >>= ·), ReaderT.bind, Except.bind, hx] using h⟩

/-- The context `withLocalDecl` hands its continuation: `MonadLocalNameGenerator M` takes the
generator's current name and `MonadWithReaderOf LocalContext M` pushes the declaration. -/
def posPush (c : Context) (nm : Name) (ty : Expr) (bi : BinderInfo) : Context :=
  { c with ngen := c.ngen.next, lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ nm ty bi }

/-- `withLocalDecl` in `AddInductive.M` is `rfl` on the nose: no state, no fuel, no failure. -/
theorem withLocalDecl_ok {α : Type} {nm : Name} {bi : BinderInfo} {ty : Expr}
    {k : Expr → M α} {c : Context} {r : α} (h : withLocalDecl nm bi ty k c = .ok r) :
    k (.fvar ⟨c.ngen.curr⟩) (posPush c nm ty bi) = .ok r := h

/-- **`whnf` is the identity on a pi.**  `whnf'`'s first arm returns `.bvar`/`.sort`/`.mvar`/
`.forallE`/`.lit` unchanged before it even reaches the cache (`Lean4Lean/TypeChecker.lean`:529), so
this needs no environment, no `WF` and no fuel hypothesis: at `recDepth = 0` the call throws and the
success hypothesis is contradictory, and at `recDepth = k+1` it returns its input.

This is what makes §3.3's scan a statement about the **stored** telescope. -/
theorem whnf_forallE {nm : Name} {d b : Expr} {bi : BinderInfo} {c : Context} {t' : Expr}
    (h : (liftM (TypeChecker.whnf (.forallE nm d b bi)) : M Expr) c = .ok t') :
    t' = .forallE nm d b bi := by
  revert h
  simp only [liftM, monadLift, MonadLift.monadLift, TypeChecker.whnf, TypeChecker.Inner.whnf,
    TypeChecker.RecM.run, TypeChecker.M.run, readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, bind, StateT.bind, StateT.pure, pure, StateT.run', Except.bind,
    Functor.map, Except.map, Except.pure]
  cases hr : c.fuel.recDepth with
  | zero => simp only [TypeChecker.Methods.withFuel]; intro h; exact absurd h nofun
  | succ k =>
    simp only [TypeChecker.Methods.withFuel, TypeChecker.Inner.whnf']
    intro h
    simp only [pure, StateT.pure, ReaderT.pure, Except.pure] at h
    exact (Except.ok.inj h).symm

/-! ### §3.3 One step of `checkPositivity.loop`, and the whole stored telescope -/

/-- **One step at a pi.**  Either the whole term carries no block occurrence — the loop's early
return, and then every domain is block-free for free — or the domain is block-free *because the
`.forallE` branch's `throw` did not fire*, and the loop descends into the body with a fresh fvar
substituted.

Both disjuncts are established with no hypothesis beyond success. -/
theorem checkPositivity_loop_forallE {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {nm : Name} {dom body : Expr} {bi : BinderInfo} {fuel : Nat} {c : Context} {u : Unit}
    (h : checkPositivity.loop stats ctor idx (.forallE nm dom body bi) (fuel+1) c = .ok u) :
    hasIndOcc stats.indConsts (.forallE nm dom body bi) = false ∨
    (hasIndOcc stats.indConsts dom = false ∧
      ∃ dom' : Expr, consumeAnnotations dom c = .ok dom' ∧
        checkPositivity.loop stats ctor idx (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) fuel
          (posPush c nm dom' bi) = .ok u) := by
  rw [checkPositivity.loop] at h
  obtain ⟨t₁, hw, h⟩ := M_bind_ok h
  cases whnf_forallE hw
  by_cases hocc : hasIndOcc stats.indConsts (Expr.forallE nm dom body bi) = false
  · exact .inl hocc
  · simp only [Bool.not_eq_false] at hocc
    simp only [hocc, Bool.not_true, Bool.false_eq_true, if_false] at h
    have hd : hasIndOcc stats.indConsts dom = false := by
      by_cases hd : hasIndOcc stats.indConsts dom = true
      · simp only [hd, if_true] at h
        exact absurd (M_bind_ok h).choose_spec.1 nofun
      · simpa using hd
    refine .inr ⟨hd, ?_⟩
    simp only [hd, Bool.false_eq_true, if_false] at h
    obtain ⟨dom', hc, h⟩ := M_bind_ok h
    exact ⟨dom', hc, withLocalDecl_ok h⟩

/-- **The non-pi step: the head really is a valid block application.**  Stated at the *reduct*,
because that is where the check happens; combined with §2 this is the residual scan. -/
theorem checkPositivity_loop_validApp {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {t t₁ : Expr} {fuel : Nat} {c : Context} {u : Unit}
    (h : checkPositivity.loop stats ctor idx t (fuel+1) c = .ok u)
    (hw : (liftM (TypeChecker.whnf t) : M Expr) c = .ok t₁)
    (hnf : ∀ nm d b bi, t₁ ≠ .forallE nm d b bi)
    (hocc : hasIndOcc stats.indConsts t₁ = true) :
    ∃ j, isValidIndApp? stats t₁ = some j := by
  rw [checkPositivity.loop] at h
  obtain ⟨t₂, hw₂, h⟩ := M_bind_ok h
  cases Except.ok.inj (hw₂.symm.trans hw)
  simp only [hocc, Bool.not_true, Bool.false_eq_true, if_false] at h
  cases hv : isValidIndApp? stats t₁ with
  | some j => exact ⟨j, rfl⟩
  | none =>
    exfalso
    revert h
    cases t₁ with
    | forallE a b c d => exact absurd rfl (hnf a b c d)
    | bvar _ | sort _ | const _ _ | fvar _ | mvar _ | lit _ | app _ _ | lam _ _ _ _
    | letE _ _ _ _ _ | mdata _ _ | proj _ _ _ => simp only [hv]; exact nofun

/-- **Part (B), on the implementation side, over the whole stored pi telescope.**  A successful
`checkPositivity` run establishes that *every* domain of the field type's stored syntactic pi
telescope is free of block constants.

The induction is on the loop's fuel, and the three facts it consumes are exactly the three §3
lemmas: `whnf_forallE` (the descent follows the stored telescope), `checkPositivity_loop_forallE`
(each step's `throw` did not fire), and `anySub_instantiate1'_fvar` (the evidence, which is about
the fvar-instantiated body, reads back to the stored body).  `Lean.Expr.instantiate1_eq` — guard 1's
whitelisted interface axiom for the extern — is used once, here. -/
theorem checkPositivity_loop_binderDoms {stats : InductiveStats} {ctor : Name} {idx : Nat} :
    ∀ (fuel : Nat) (t : Expr) (c : Context) (u : Unit),
      checkPositivity.loop stats ctor idx t fuel c = .ok u →
      ∀ B ∈ posBinderDoms t, hasIndOcc stats.indConsts B = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro t c u h
    rw [checkPositivity.loop] at h
    exact absurd h nofun
  | succ fuel ih =>
    intro t c u h B hB
    cases t with
    | forallE nm dom body bi =>
      rcases checkPositivity_loop_forallE h with hnone | ⟨hd, dom', -, hrec⟩
      · rw [hasIndOcc_eq] at hnone ⊢
        exact posBinderDoms_noOcc hnone B hB
      · rw [posBinderDoms, List.mem_cons] at hB
        rcases hB with rfl | hB
        · exact hd
        · obtain ⟨d', hd'⟩ :=
            posBinderDoms_instantiate1' (a := .fvar ⟨c.ngen.curr⟩) body 0 B hB
          have := ih _ _ _ hrec (B.instantiate1' (.fvar ⟨c.ngen.curr⟩) d')
            (by rw [Lean.Expr.instantiate1_eq]; exact hd')
          rwa [hasIndOcc_instantiate1'_fvar] at this
    | bvar _ | sort _ | const _ _ | fvar _ | mvar _ | lit _ | app _ _ | lam _ _ _ _
    | letE _ _ _ _ _ | mdata _ _ | proj _ _ _ => exact absurd hB nofun

/-- The same at the entry point `checkPositivity`, which is what `checkConstructors` calls. -/
theorem checkPositivity_binderDoms {stats : InductiveStats} {ctor : Name} {idx : Nat}
    {t : Expr} {c : Context} {u : Unit} (h : checkPositivity stats t ctor idx c = .ok u) :
    ∀ B ∈ posBinderDoms t, hasIndOcc stats.indConsts B = false := by
  rw [checkPositivity] at h
  obtain ⟨-, -, h⟩ := M_bind_ok h
  exact checkPositivity_loop_binderDoms (ctor := ctor) (idx := idx) _ t c u h

end AddInductive

/-! ## §4 The firings

Two, one on each side of the file.

**(a) At the real nested block, with the arity conjunct no longer computed.**  `WFPos` §4 discharges
conjunct 2 by `rfl` at `ntreeAux` — a computation at a closed block, which is exactly the kind of
step §1 shows is not needed.  Here the same three `PosSyn`s come out with conjunct 2 supplied by
`args_len_of_posTy`, i.e. by the typing half, so no conjunct of `PosSyn` is discharged by evaluation
at the block any more: 1 and 9 from the reader (`WFPos` §2/§3.1), 2 from `PosTy`, 3 and 4 from the
empty telescopes.

**(b) On the checker's own data**, where the point is what *cannot* be computed: `BEq Expr` is the
extern `Lean.Expr.eqv`, so `isValidIndAppIdx stats t i = true` is **not** decidable by `decide` at
any concrete `stats` — kernel reduction stops at the opaque.  The head conjunct is therefore
supplied by `Lean.Expr.eqv_refl` (`Verify/Expr.lean`) and the residual conjunct by evaluation of
`anySub`, which *is* pure.  That is the opposite of a regression to `decide`: the firing is forced to
name where its evidence comes from. -/

namespace InductiveDeclExamples

/-- `NTree.node`'s recursive field, with conjunct 2 from the typing half rather than by `rfl`. -/
theorem ntreeNode_field1_posSyn_of_posTy {env₁ env₂ : VEnv}
    (hs : env₁.addIndTypes ntreeAux = some env₂) :
    VIndField.PosSyn ntreeAux 1
      (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default)
      { binders := [], idx := 1, args := [] } :=
  VIndField.posSyn_of_recArgOf_posTy ntreeAux_node_field1_recArgOf nofun nofun
    (ntreeNode_field1_posTy hs)

/-- …and the whole nine-conjunct `some` branch through §1.1's composed producer.  Compare
`WFPos`'s `ntreeNode_field1_WF`, whose `pos` goes through `posSome_of_split` with a separately
computed `PosSyn`. -/
theorem ntreeNode_field1_posSome {env₁ env₂ : VEnv}
    (hs : env₁.addIndTypes ntreeAux = some env₂) :
    match (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default).recArg with
    | none => ∃ A, ntreeAux.NoBlock A ∧
        env₂.IsDefEqType ntreeAux.uvars [.bvar 0, .sort (.succ (.param 0))]
          (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default).type A
    | some r =>
      r.idx < ntreeAux.nm ∧
      r.args.length = (ntreeAux.types.getD r.idx default).indices.length ∧
      (∀ B ∈ r.binders, ntreeAux.NoBlock B) ∧
      (∀ a ∈ r.args, ntreeAux.NoBlock a) ∧
      OnCtx (r.binders.reverse ++ [.bvar 0, .sort (.succ (.param 0))])
        (env₂.IsType ntreeAux.uvars) ∧
      env₂.HasType ntreeAux.uvars (r.binders.reverse ++ [.bvar 0, .sort (.succ (.param 0))])
        (r.canonResult ntreeAux 1) (.sort ntreeAux.lvl) ∧
      (∀ T', ntreeAux.types[r.idx]? = some T' →
        env₂.HasArgs ntreeAux.uvars (r.binders.reverse ++ [.bvar 0, .sort (.succ (.param 0))])
          (VExpr.liftTele (r.binders.length + 1) T'.indices) r.args) ∧
      env₂.IsDefEqType ntreeAux.uvars [.bvar 0, .sort (.succ (.param 0))]
        (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default).type
        (r.canonType ntreeAux 1) ∧
      ntreeAux.ResidualClean (r.binders.length + 1)
        (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default).type :=
  VIndField.posSome_of_recArgOf rfl ntreeAux_node_field1_recArgOf nofun nofun
    (ntreeNode_field1_posTy hs)

end InductiveDeclExamples

namespace AddInductive
open Lean hiding Environment Exception

/-! ### §4.1 The checker side, at a hand-built `InductiveStats`

`psI` is a one-member, zero-parameter, one-index block; `psT` is `psI Nat`, the shape a recursive
field's head-normal form has. -/

namespace PosScanWit

def psStats : InductiveStats where
  levels := []
  resultLevel := .zero
  nindices := #[1]
  indConsts := #[.const `psI []]
  params := #[]
  isNotZero := false

/-- `psI Nat` — one residual argument, block-free. -/
def psT : Expr := (Expr.const `psI []).app (.const ``Nat [])

/-- **The check succeeds, and not by `decide`.**  The head conjunct comes from
`Lean.Expr.eqv_refl` — `decide` cannot reduce it, because `BEq Expr` is the `@[extern] opaque`
`Lean.Expr.eqv`.  The arity conjunct is `Nat`'s `==` and the residual conjunct is `anySub`, both
pure, so those two do evaluate. -/
theorem psStats_indConsts : psStats.indConsts = #[Expr.const `psI []] := rfl

theorem psNat_noOcc : hasIndOcc psStats.indConsts (.const ``Nat []) = false := by
  rw [hasIndOcc_const, psStats_indConsts]; simp [Lean.Expr.constName!]

theorem psI_occ : hasIndOcc psStats.indConsts (.const `psI []) = true := by
  rw [hasIndOcc_const, psStats_indConsts]; simp [Lean.Expr.constName!]

theorem psT_valid : isValidIndAppIdx psStats psT 0 = true :=
  isValidIndAppIdx_of
    (show (psT.getAppFn == psStats.indConsts[0]!) = true from Lean.Expr.eqv_refl _)
    rfl (fun _ h => absurd h nofun)
    (fun j _ hj => by
      rw [show psT.getAppArgs.size = 1 from rfl] at hj
      rw [show j = 0 by omega, show psT.getAppArgs[0]! = Expr.const ``Nat [] from rfl]
      exact psNat_noOcc)

theorem psT_numArgs : psT.getAppArgs.size = psStats.params.size + psStats.nindices[0]! :=
  isValidIndAppIdx_numArgs psT_valid

/-- The residual scan, fired: the one index argument of `psI Nat` carries no block occurrence, and
this is `isValidIndAppIdx_residual_noOcc` rather than a computation of `hasIndOcc`. -/
theorem psT_residual : hasIndOcc psStats.indConsts psT.getAppArgs[0]! = false :=
  isValidIndAppIdx_residual_noOcc psT_valid (Nat.le_refl 0) (by rw [show psT.getAppArgs.size = 1 from rfl]; omega)

/-- A hostile sibling: the same head with the block *inside* the index argument.  Here the check
must fail, and `isValidIndAppIdx_residual_noOcc` is what says so — the two theorems together are the
statement that the residual scan is the load-bearing conjunct. -/
def psBad : Expr := (Expr.const `psI []).app ((Expr.const `psI []).app (.const ``Nat []))

theorem psBad_invalid : isValidIndAppIdx psStats psBad 0 = false := by
  cases h : isValidIndAppIdx psStats psBad 0 with
  | false => rfl
  | true =>
    refine absurd (isValidIndAppIdx_residual_noOcc h (Nat.le_refl 0)
      (by rw [show psBad.getAppArgs.size = 1 from rfl]; omega)) ?_
    rw [show psBad.getAppArgs[0]! = (Expr.const `psI []).app (.const ``Nat []) from rfl,
      hasIndOcc_eq, anySub_app_eq, ← hasIndOcc_eq, ← hasIndOcc_eq]
    exact fun h =>
      absurd ((Bool.or_eq_false_iff.1 (Bool.or_eq_false_iff.1 h).2).1.symm.trans psI_occ) nofun

/-- **The stored binder telescope, and its scan.**  `psField` is `(n : Nat) → psI Nat`, a recursive
field with one non-recursive binder; `posBinderDoms` reports exactly that binder, and
`posBinderDoms_noOcc` is what `checkPositivity_loop_binderDoms`'s early-return branch runs. -/
def psField : Expr := .forallE `n (.const ``Nat []) psT .default

theorem psField_binderDoms : posBinderDoms psField = [.const ``Nat []] := rfl

theorem psField_binder_noOcc :
    ∀ B ∈ posBinderDoms psField, hasIndOcc psStats.indConsts B = false := by
  rw [psField_binderDoms]
  intro B hB
  rw [List.mem_singleton] at hB
  subst hB
  exact psNat_noOcc

end PosScanWit
end AddInductive

/-! ## §5 The limits, each measured or proved

**(a) Part (A) is closed and needs nothing from the implementation** (§1).  Its only hypothesis is
conjunct 1, which the reader supplies.  The limit worth naming is that it is *conditional on the
typing half*: a consumer who wants `PosSyn` alone, with no `PosTy` in hand, still has to supply the
arity equation — and `posSyn_of_recArgOf` is still there for them.  `AddInductive`'s own arity test
is `isValidIndAppIdx_numArgs`, so the implementation route exists too and the two are independent.

**(b) Part (B) is closed on the implementation side, and its limit is exactly the canon gap.**
`checkPositivity_loop_binderDoms` establishes `hasIndOcc … = false` for every domain of the *stored*
syntactic pi telescope (`posBinderDoms`), which is the telescope `VIndRestore.recogAt` splits.  Three
things it does **not** cover, and each is a real term rather than a hedge:

1. **Binders that `whnf` reveals.**  Once the stored pi telescope is exhausted, the loop's `whnf` can
   turn the remainder into a further pi.  `Verify/Inductive/CanonGapMeasure.lean` §1's `cgmRedex` —
   `(fun x : Type => cgmT) Prop`, accepted by all four checkers with the redex stored verbatim, and
   that file's `#eval` self-guards the claim — is the witness that stored and reduced forms genuinely
   differ.  Those extra binders are scanned by the checker and are *not* in `posBinderDoms`, so this
   direction only makes the conclusion weaker, never wrong.
2. **`.mdata`.**  `whnf'` strips `mdata` (`| .mdata _ e => whnf' e`), so the loop descends past an
   annotated pi that `posBinderDoms` stops at.  Again a weakening, and again in the safe direction.
3. **The `Expr → VExpr` transfer.**  `r.binders` is a `List VExpr`; `posBinderDoms` a `List Expr`.
   The transfer is `TrExprS.noConsts` (`Verify/Inductive/Add.lean`, cone 3616 and **hole-free**,
   measured 2026-09-04), whose three side conditions `hctx`/`hlit`/`hproj` that file already
   investigated — two closed outright, the third open with the reason recorded.  What is *not*
   supplied by any of this is the **indexing** correspondence: that the `k`-th entry of
   `posBinderDoms F.type` translates to the `k`-th entry of `r.binders`.  That is R1/R2's telescope
   correspondence (`VLCtx.find?_mkFVars_rev` and siblings, same file), and it is named here rather
   than assumed.

**(c) Part (C) is closed on the implementation side, and one of `isValidIndAppIdx`'s conjuncts is
*not* an `Eq` and cannot be made one.**  `Expr.eqv` is alpha-equivalence ignoring binder names and
annotations, so `isValidIndAppIdx_params` concludes `stats.params[j]! == t.getAppArgs[j]!` and
nothing stronger; stating it as `Eq` would be **false**.  §4.1's `psT_valid` shows the same fact from
the other side: the check is not `decide`-able at a closed `stats`.  The head conjunct escapes only
because `stats.indConsts[i]!` is a `.const` (`isValidIndAppIdx_head_const`), which costs the frozen
whitelisted axiom `Lean.Expr.eqv_eq`.

**(d) `VIndRecArg.exists_indep` is off this file's path, measured.**  Nothing here mentions it and
nothing here has it in its cone; `docs/handoff-posscan.md` §2 reports `scripts/exists.lean` with it
watched.  The reason is structural rather than lucky: all three parts of the check are `Decidable`
statements with no `∃` over independent binders in them, and `exists_indep` is
`VIndField.WF.binders_indep`'s obligation, not `pos`'s — which is what `WFPos` §5(d) already found
for itself.

**(e) What is *not* claimed.**  No statement here is about `VInductDecl'.WF` as a whole, about the
`none` branch (that is `M.WF.positivity_none`'s, and it stops at the sort upgrade), or about
`checkConstructors`' outer loop — `checkPositivity` is called from inside it and this file reads the
callee, not the caller.

## §6 Axiom checks

Every declaration this file introduces, in order.  The split that matters: everything up to and
including §3.1 is `propext`/`Quot.sound` only; `checkPositivity_loop_binderDoms` and its consumers
pay `Lean.Expr.instantiate1_eq`, and `isValidIndAppIdx_head_const`/§4.1 pay `Lean.Expr.eqv_eq` —
both frozen, both already on guard 1's whitelist.
-/

#print axioms Lean4Lean.VIndField.args_len_of_posTy
#print axioms Lean4Lean.VIndField.posSyn_of_recArgOf_posTy
#print axioms Lean4Lean.VIndField.posSome_of_recArgOf
#print axioms Lean4Lean.forIn_scan_run
#print axioms Lean4Lean.AddInductive.isValidIndAppIdx_eq
#print axioms Lean4Lean.AddInductive.isValidIndAppIdx_head
#print axioms Lean4Lean.AddInductive.isValidIndAppIdx_head_const
#print axioms Lean4Lean.AddInductive.isValidIndAppIdx_numArgs
#print axioms Lean4Lean.AddInductive.isValidIndAppIdx_params
#print axioms Lean4Lean.AddInductive.isValidIndAppIdx_residual_noOcc
#print axioms Lean4Lean.AddInductive.isValidIndAppIdx_residual_anySub
#print axioms Lean4Lean.AddInductive.isValidIndAppIdx_of_isValidIndApp?
#print axioms Lean4Lean.posBinderDoms
#print axioms Lean4Lean.posBinderDoms_noOcc
#print axioms Lean4Lean.posBinderDoms_instantiate1'
#print axioms Lean4Lean.anySub_instantiate1'_fvar
#print axioms Lean4Lean.AddInductive.M_bind_ok
#print axioms Lean4Lean.AddInductive.withLocalDecl_ok
#print axioms Lean4Lean.AddInductive.whnf_forallE
#print axioms Lean4Lean.AddInductive.checkPositivity_loop_forallE
#print axioms Lean4Lean.AddInductive.checkPositivity_loop_validApp
#print axioms Lean4Lean.AddInductive.checkPositivity_loop_binderDoms
#print axioms Lean4Lean.AddInductive.checkPositivity_binderDoms
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_field1_posSyn_of_posTy
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_field1_posSome
#print axioms Lean4Lean.AddInductive.PosScanWit.psT_valid
#print axioms Lean4Lean.AddInductive.PosScanWit.psT_numArgs
#print axioms Lean4Lean.AddInductive.PosScanWit.psT_residual
#print axioms Lean4Lean.AddInductive.PosScanWit.psBad_invalid
#print axioms Lean4Lean.AddInductive.PosScanWit.psField_binderDoms
#print axioms Lean4Lean.AddInductive.PosScanWit.psField_binder_noOcc
