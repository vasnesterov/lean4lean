import Lean4Lean.Verify.Typing.ProjLevelWitness
import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Inductive.StructureClosed
-- 2026-09-03: `VEnv.onCtx_of_appendTele_free`, the axiom-free replacement for the
-- `OnCtx.weakN_inv` appeal in `OnCtx.of_appendTele` below (handoff-weakn §7.4 site 1).
import Lean4Lean.Theory.Typing.WeakNProjGate

/-!
# The syntactic core of `TrProj.wf`'s live route

`ProjLevelWitness.lean` refutes the subgoal the current proof of `TrProj.wf`
(`Verify/Typing/Lemmas.lean`) reduces to: `projTerm_hasType`'s `hlv` premise demands
`lvl_k.inst us ≈ .zero` at **every** `k ≤ i`, and at an unused field that is false.  This file
carries the fact that makes the *replacement* route work, and it is purely syntactic.

## The route, and why it is live

`VInductDecl'.projCore`'s only use of the earlier projections is inside its motive,
`instAll ftype (ps.map (·.liftN _) ++ earlier)`.  In `instAll e (as) k` the list element at
position `j` substitutes at de Bruijn index `as.length - 1 - j` (`instAll_cons`), so with
`as = ps ++ earlier`, `|ps| = np`, `|earlier| = i`, the entry `earlier[k]` substitutes at index
`i - 1 - k` — **exactly the index `VIndCtor.not_fieldUsed_skips` proves `ftype` skips** when
field `k` is unused.  So `projTerm … i e` does not mention the projection of an unused earlier
field *at all*: the term the current proof cannot type is not in the term it is typing.

`VIndCtor.not_fieldUsed_skips` is described in `Theory/Inductive/Structure.lean` as "stated and
unused"; this is the use.

That turns the open subgoal from a level equivalence (refuted) into: type the motive body from
the *compressed* spine, dropping the positions the field type skips.  The one judgement that
step needs is single-binder strengthening for a type,

    IsType (A :: Δ) (X.liftN 1)  ⟹  IsType Δ X

which is **already a lemma in this tree** — `VEnv.IsType.weakN_iff`
(`Theory/Typing/UniqueTyping.lean:221`), at `Ctx.LiftN.one`.  It is backed by
`IsDefEqU.weakN_iff`'s `sorry` at `UniqueTyping.lean:172`, i.e. by an *existing* hole owned by
another stream, not by a statement that has to be invented.  `TrProj.wf`'s docstring reaches
the same target and calls it "the rescoped target"; what that docstring got wrong is only the
*shape* of the current subgoal, and `ProjLevelWitness.lean` corrects that.

## What is here, and what is not

Here, in three layers:

1. The substitution lemma (`VExpr.instAll_congr_skips`), its `projCore` instance
   (`VInductDecl'.projCore_congr_earlier`), its multi-position form
   (`VExpr.InstAllSkip` / `instAll_congr_of_skip`), and the `barDecl` demonstration — the
   two-field witness of `ProjLevelWitness.lean`, where field 0 is unused and *not* `≈ .zero`,
   so this is the exact configuration `barRefutes` uses.
2. **The swap machinery.**  `VEnv.HasType.swapSkipped` / `.swapTele` / `.swapCtx` replace the
   unused field binders by the inhabited `VExpr.swapUnit := .sort (.succ .zero)`, at the price
   of exactly one `VEnv.HasType.weakN_iff` per swapped binder.  `VExpr.SwapCtx.build` and
   `VIndCtor.swapCtx_fields` construct the derivation from `VIndCtor.not_fieldUsed_skips`
   *unconditionally* — used positions need nothing, unused ones are covered.
3. **The crux, assembled**: `ftype_hasType_swapped` / `ftype_hasType_swapped_exists`.

Not here: the guarded re-proofs of `projArgs_hasArgs`, `projMotiveBody_hasType`
(`Theory/Inductive/StructureClosed.lean`), `projMinor_hasType` and `projTerm_hasType`
(`Verify/Typing/Lemmas.lean`).  Those are the bulk, and after layer 3 they need no fact that is
not already here — see `docs/handoff-projections.md` for the step-by-step.
-/

namespace Lean4Lean

open VExpr

/-- Substituting at an index the term does not use is independent of what is substituted. -/
theorem VExpr.inst_congr_skips {e : VExpr} {m : Nat} (h : e.Skips' 1 m) (a b : VExpr) :
    e.inst a m = e.inst b m := by
  obtain ⟨e', rfl⟩ := VExpr.skips_iff_exists.1 (VExpr.skips_iff.2 h)
  rw [VExpr.inst_liftN, VExpr.inst_liftN]

/-- **The lemma the route runs on.**  One position of an `instAll` spine is irrelevant as soon
as the term reached just before that position is substituted skips index `k + |post|`. -/
theorem VExpr.instAll_congr_skips {pre post : List VExpr} {e a b : VExpr} {k : Nat}
    (h : (VExpr.instAll e pre (k + post.length + 1)).Skips' 1 (k + post.length)) :
    VExpr.instAll e (pre ++ a :: post) k = VExpr.instAll e (pre ++ b :: post) k := by
  rw [VExpr.instAll_append, VExpr.instAll_append]
  simp only [List.length_cons, VExpr.instAll_cons]
  rw [show k + (post.length + 1) = k + post.length + 1 from by omega,
    VExpr.inst_congr_skips h a b]

/-- **`projCore` does not read the earlier projections it discards.**  Instantiated at the
position of an unused field, this says the projected term is *literally the same* whether or
not the ill-typed projection is supplied. -/
theorem VInductDecl'.projCore_congr_earlier (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps is : List VExpr) (i : Nat) (e : VExpr)
    (pre post : List VExpr) (a b : VExpr)
    (h : (VExpr.instAll ((C.fields.getD i default).type.instL us)
            (ps.map (·.liftN (is.length+1)) ++ pre) (post.length + 1)).Skips' 1 post.length) :
    D.projCore T C us ps is i (pre ++ a :: post) e
      = D.projCore T C us ps is i (pre ++ b :: post) e := by
  simp only [VInductDecl'.projCore]
  rw [show ps.map (·.liftN (is.length+1)) ++ (pre ++ a :: post)
        = (ps.map (·.liftN (is.length+1)) ++ pre) ++ a :: post from by simp,
    show ps.map (·.liftN (is.length+1)) ++ (pre ++ b :: post)
        = (ps.map (·.liftN (is.length+1)) ++ pre) ++ b :: post from by simp,
    VExpr.instAll_congr_skips (k := 0) (by simpa using h)]

/-! ## The demonstration, at the two-field witness

`barDecl`'s field 0 is `Prop` — recorded level `.succ .zero`, *not* `≈ .zero` — and is unused by
field 1's type `∀ p : Prop, p`.  `barRefutes` (`ProjLevelWitness.lean`) uses exactly this to
falsify the current proof's subgoal.  Here the same configuration shows the subgoal is not
needed. -/

/-- **Field 0's projection is irrelevant to `.proj Bar 1`**, by `rfl`: the recursor application
`TrProj` produces is independent of what sits at the unused position. -/
theorem barDecl_projCore_indep (e x y : VExpr) :
    barDecl.projCore barType barCtor [] [] [] 1 [x] e
      = barDecl.projCore barType barCtor [] [] [] 1 [y] e := rfl

/-- …and `projTerm`, which supplies the *ill-typed* `projCore … 0` at that position, is equal to
the instance that supplies a trivially well-typed term instead. -/
theorem barDecl_projTerm_eq (e : VExpr) :
    barDecl.projTerm barType barCtor [] [] [] 1 e
      = barDecl.projCore barType barCtor [] [] [] 1 [.sort .zero] e := rfl

/-- **The whole term, spelled out.**  `Bar.rec (fun _ : Bar => ∀ p : Prop, p)
(fun (n : Prop) (h : ∀ p : Prop, p) => h) e` — there is no occurrence of a projection of
field 0 anywhere in it, which is why `TrProj.wf` is *true* at the witness that refutes its
current proof's subgoal. -/
theorem barDecl_projTerm_spelled (e : VExpr) :
    barDecl.projTerm barType barCtor [] [] [] 1 e
      = .app (.app (.app (VExpr.const `Bar.rec [])
            ((VExpr.const `Bar []).lam ((VExpr.sort .zero).forallE (.bvar 0))))
          ((VExpr.sort .zero).lam (((VExpr.sort .zero).forallE (.bvar 0)).lam (.bvar 0))))
          e := rfl

/-! ## The swap step, and a correction

`docs/handoff-projections.md` §4.3 listed, among "two routes that do **not** work, checked so
nobody re-tries them",

> Replacing the unused telescope entry by an inhabited type (`.sort (.succ .zero)`, inhabited
> by `.sort .zero`) and using the modified context.  The field type's typing then lives in the
> *swapped* context, and "swap a context entry the subject and type both skip" is not free —
> a subderivation may still mention it.

The premise is right and the conclusion is wrong.  The swap is **not** free — but its price is
*exactly* one use of `VEnv.HasType.weakN_iff`, which is the same strengthening the compressed
route pays and which is already in the tree.  Strengthen the binder away, weaken the new one
in.  "A subderivation may still mention it" is precisely what strengthening rules out, so the
objection is an argument for needing strengthening, not against the route.  (`TrProj.wf`'s
own docstring in `Verify/Typing/Lemmas.lean` has been corrected to point here.)

That matters because the swap route is what removes the *inhabitant* problem.  At an unused
field `k` the compressed route must justify dropping the entry; the naive alternative — supply
some well-typed junk at position `k` — needs an inhabitant of field `k`'s type, and there is
none in general (`structure Bar : Prop where (n : Nat) (h : True)` needs an inhabitant of
`Nat` in an arbitrary context and environment).  The swap replaces the *type* by
`.sort (.succ .zero)`, which `.sort .zero` inhabits in every context of every environment, so
the spine can be kept saturated. -/

/-- **Swapping the skipped part of a context.**  If a judgement's subject and type are both
lifts through the same hole, the material in the hole can be replaced wholesale. -/
theorem VEnv.HasType.swapSkipped {env : VEnv} {U : Nat} {Γ₀ Γ Γ' : List VExpr}
    {b B : VExpr} {n k : Nat}
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (W : Ctx.LiftN n k Γ₀ Γ) (W' : Ctx.LiftN n k Γ₀ Γ')
    (H : env.HasType U Γ (b.liftN n k) (B.liftN n k)) :
    env.HasType U Γ' (b.liftN n k) (B.liftN n k) :=
  ((VEnv.HasType.weakN_iff henv hΓ W).1 H).weakN henv.ordered W'

/-- The one-binder instance, which is the one the projection route uses: an *unused* field's
binder type may be replaced by anything, in particular by an inhabited sort. -/
theorem VEnv.HasType.swapSkipped_one {env : VEnv} {U : Nat} {Γ : List VExpr}
    {A A' b B : VExpr}
    (henv : VEnv.WF env) (hΓ : OnCtx (A :: Γ) (env.IsType U))
    (H : env.HasType U (A :: Γ) (b.liftN 1 0) (B.liftN 1 0)) :
    env.HasType U (A' :: Γ) (b.liftN 1 0) (B.liftN 1 0) :=
  VEnv.HasType.swapSkipped henv hΓ Ctx.LiftN.one Ctx.LiftN.one H

/-! ### Non-vacuity of the swap, at the two-field witness's own configuration

`barField1` (`∀ p : Prop, p`) is typed over `[barField0.type]` — the context that binds the
*unused* field 0 — and it is a lift, `barField1.type.liftN 1 0 = barField1.type`.  So the swap
applies to it verbatim.  `VEnv.empty` is `VEnv.WF` (`⟨[], .empty⟩`) and the typing uses no
constant, so the witness needs nothing about `barEnv`. -/

theorem barField1_liftN : barField1.type.liftN 1 0 = barField1.type := rfl

theorem barField1_hasType_empty :
    VEnv.HasType .empty 0 [barField0.type] barField1.type (.sort barField1.lvl) :=
  .forallEDF (.sortDF trivial trivial (.refl _)) (.bvar (.zero ..))

/-- **The unused field's binder can be swapped for an inhabited sort**, and the used field's
type keeps its typing.  This is the step `TrProj.wf`'s docstring set aside. -/
theorem barField1_hasType_swapped :
    VEnv.HasType .empty 0 [.sort (.succ .zero)] barField1.type (.sort barField1.lvl) := by
  have hΓ : OnCtx [barField0.type] (VEnv.empty.IsType 0) := by
    refine ⟨trivial, .succ .zero, ?_⟩
    show VEnv.HasType .empty 0 [] (.sort .zero) _
    exact .sortDF trivial trivial (.refl _)
  have H : VEnv.HasType .empty 0 [barField0.type]
      (barField1.type.liftN 1 0) ((VExpr.sort barField1.lvl).liftN 1 0) :=
    barField1_hasType_empty
  exact VEnv.HasType.swapSkipped_one (A' := .sort (.succ .zero)) ⟨[], .empty⟩ hΓ H

/-- …and the sort that replaces it really is inhabited, in every context of every
environment. -/
theorem sort_succ_zero_inhabited {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) :=
  .sortDF trivial trivial (.refl _)

/-! ## The multi-position form

`projCore_congr_earlier` replaces one entry.  The route replaces the entries at *every* unused
position at once, and the condition at each one has to be read *after* the substitutions to its
left have happened — which is what the inductive below records. -/

/-- `InstAllSkip e as bs k`: substituting `as` and substituting `bs` into `e` (both saturated,
at base index `k`) agree, because at every position where the two lists differ the term reached
just before that position skips the index being substituted. -/
inductive VExpr.InstAllSkip : VExpr → List VExpr → List VExpr → Nat → Prop
  | nil {e k} : VExpr.InstAllSkip e [] [] k
  | same {e a as bs k} (hl : as.length = bs.length)
      (h : VExpr.InstAllSkip (e.inst a (k + as.length)) as bs k) :
      VExpr.InstAllSkip e (a :: as) (a :: bs) k
  | skip {e a b as bs k} (hl : as.length = bs.length)
      (hs : e.Skips' 1 (k + as.length))
      (h : VExpr.InstAllSkip (e.inst a (k + as.length)) as bs k) :
      VExpr.InstAllSkip e (a :: as) (b :: bs) k

theorem VExpr.instAll_congr_of_skip : ∀ {e : VExpr} {as bs : List VExpr} {k : Nat},
    VExpr.InstAllSkip e as bs k → VExpr.instAll e as k = VExpr.instAll e bs k
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .same hl h => by
    rw [VExpr.instAll_cons, VExpr.instAll_cons, ← hl, VExpr.instAll_congr_of_skip h]
  | e, _, _, _, .skip (a := a) (b := b) hl hs h => by
    rw [VExpr.instAll_cons, VExpr.instAll_cons, ← hl,
      VExpr.inst_congr_skips hs a b] at *
    exact VExpr.instAll_congr_of_skip h

/-! ### The swap in the middle of a telescope

`Ctx.LiftN.tele` (`Theory/Inductive/Lemmas.lean`, B6) already builds the `Ctx.LiftN` for a
declaration-order telescope sitting above a hole, so the middle-of-the-telescope swap is one
line on top of `swapSkipped`.  This is the shape the projection route needs: the unused field's
binder sits *below* the later field binders, and those later binders provably do not mention it
(`VIndCtor.not_fieldUsed_skips`), which is exactly `As = liftTele 1 As₀ 0`. -/

/-- **Swapping one binder in the middle of a telescope.**  `A` is a binder of the context with
the declaration-order telescope `As` above it; `As` does not mention `A` (it is a `liftTele`),
and the judgement's subject and type do not either.  Then `A` may be replaced by any `A'`. -/
theorem VEnv.HasType.swapTele {env : VEnv} {U : Nat} {Γ As : List VExpr}
    {A A' b B : VExpr} (henv : VEnv.WF env)
    (hΓ : OnCtx ((liftTele 1 As 0).reverse ++ A :: Γ) (env.IsType U))
    (H : env.HasType U ((liftTele 1 As 0).reverse ++ A :: Γ)
      (b.liftN 1 As.length) (B.liftN 1 As.length)) :
    env.HasType U ((liftTele 1 As 0).reverse ++ A' :: Γ)
      (b.liftN 1 As.length) (B.liftN 1 As.length) := by
  have W : Ctx.LiftN 1 As.length (As.reverse ++ Γ)
      ((liftTele 1 As 0).reverse ++ A :: Γ) := by
    have := Ctx.LiftN.tele (As := As) (n := 1) (k := 0) (Γ := Γ)
      (Γ' := A :: Γ) Ctx.LiftN.one
    rwa [Nat.zero_add] at this
  have W' : Ctx.LiftN 1 As.length (As.reverse ++ Γ)
      ((liftTele 1 As 0).reverse ++ A' :: Γ) := by
    have := Ctx.LiftN.tele (As := As) (n := 1) (k := 0) (Γ := Γ)
      (Γ' := A' :: Γ) Ctx.LiftN.one
    rwa [Nat.zero_add] at this
  exact VEnv.HasType.swapSkipped henv hΓ W W' H

/-! ### Non-vacuity, with the swapped binder *not* innermost

`barDecl`'s field 0 is unused, so field 1's binder can sit above it and the swap still applies.
The context is `[barField1.type, barField0.type]`, the swapped entry is the outer one, and the
subject is field 1's own variable. -/

theorem barField1_type_lift : barField1.type.liftN 1 1 = barField1.type := rfl

theorem bar_swapTele_source :
    VEnv.HasType .empty 0 [barField1.type, barField0.type] (.bvar 0) barField1.type :=
  .bvar (.zero ..)

/-- **The unused binder can be swapped from *under* a later binder**, which is the
configuration `TrProj.wf`'s route actually meets. -/
theorem bar_swapTele :
    VEnv.HasType .empty 0 [barField1.type, .sort (.succ .zero)] (.bvar 0) barField1.type := by
  have hΓ : OnCtx [barField1.type, barField0.type] (VEnv.empty.IsType 0) := by
    refine ⟨⟨trivial, .succ .zero, ?_⟩, barField1.lvl, barField1_hasType_empty⟩
    show VEnv.HasType .empty 0 [] (.sort .zero) _
    exact .sortDF trivial trivial (.refl _)
  have H : VEnv.HasType .empty 0
      ((liftTele 1 [barField1.type] 0).reverse ++ barField0.type :: [])
      ((VExpr.bvar 0).liftN 1 [barField1.type].length)
      (barField1.type.liftN 1 [barField1.type].length) := bar_swapTele_source
  have := VEnv.HasType.swapTele (env := .empty) (U := 0) (Γ := []) (As := [barField1.type])
    (A := barField0.type) (A' := .sort (.succ .zero)) (b := .bvar 0) (B := barField1.type)
    ⟨[], .empty⟩ hΓ H
  exact this

/-! ## Swapping the whole telescope

The projection route swaps *every* unused field binder at once.  `SwapCtx` below records
exactly the side conditions each individual swap needs, in the shape the telescope recursion
produces them, and `VEnv.HasType.swapCtx` discharges the whole family with one `swapTele` per
swapped position.

The replacement type is fixed to `.sort (.succ .zero)`: it is a type in every context of every
environment and it is *inhabited* there by `.sort .zero`, which is what keeps the projection's
spine saturated without ever needing an inhabitant of a field's own type.  That is the point of
the swap route — the compressed route would instead have to justify a shorter spine. -/

/-- The type a swapped-out binder is replaced by. -/
def VExpr.swapUnit : VExpr := .sort (.succ .zero)

theorem VExpr.swapUnit_isType {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.IsType U Γ VExpr.swapUnit := ⟨_, .sortDF trivial trivial (.refl _)⟩

/-- …and it is inhabited, in every context of every environment. -/
theorem VExpr.swapUnit_inhabited {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ (.sort .zero) VExpr.swapUnit := .sortDF trivial trivial (.refl _)

/-- `SwapCtx b B Fs Fs'`: the declaration-order telescopes `Fs` and `Fs'` agree except at
positions replaced by `VExpr.swapUnit`, and at every such position the rest of the telescope,
the subject `b` and the type `B` are all lifts through it. -/
inductive VExpr.SwapCtx (b B : VExpr) : List VExpr → List VExpr → Prop
  | nil : VExpr.SwapCtx b B [] []
  | keep {F : VExpr} {Fs Fs' : List VExpr} :
      VExpr.SwapCtx b B Fs Fs' → VExpr.SwapCtx b B (F :: Fs) (F :: Fs')
  | swap {F b₀ B₀ : VExpr} {Fs Fs' Fs₀ : List VExpr} : Fs = liftTele 1 Fs₀ 0 →
      b = b₀.liftN 1 Fs₀.length → B = B₀.liftN 1 Fs₀.length →
      VExpr.SwapCtx b B Fs Fs' → VExpr.SwapCtx b B (F :: Fs) (VExpr.swapUnit :: Fs')

/-- A context of the form `As.reverse ++ Γ` has `Γ` well-formed.

**No strengthening here.**  This used to be `OnCtx.weakN_inv henv (Ctx.LiftN.zero …)`, i.e. a
call to `VEnv.IsDefEqU.weakN_iff`'s typing wrapper -- but a `Ctx.LiftN n 0` only *appends* a
block, and dropping an appended block from an `OnCtx` is a two-line list induction with no
`VEnv.WF`, no hypothesis and no hole: `VEnv.onCtx_of_appendTele_free`
(`Theory/Typing/WeakNProjGate.lean`, `#print axioms`: depends on no axioms).  See
`docs/handoff-weakn.md` §7.4 site 1 and `docs/handoff-pidescend.md` §1. -/
theorem OnCtx.of_appendTele {env : VEnv} {U : Nat} :
    ∀ {As Γ : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) → OnCtx Γ (env.IsType U) :=
  fun {_ _} h => VEnv.onCtx_of_appendTele_free h

/-- **Every unused binder of a telescope can be swapped at once.** -/
theorem VEnv.HasType.swapCtx {env : VEnv} {U : Nat} (henv : VEnv.WF env) {b B : VExpr} :
    ∀ {Fs Fs' : List VExpr}, VExpr.SwapCtx b B Fs Fs' → ∀ {Γ : List VExpr},
      OnCtx (Fs.reverse ++ Γ) (env.IsType U) →
      env.HasType U (Fs.reverse ++ Γ) b B →
      env.HasType U (Fs'.reverse ++ Γ) b B
  | _, _, .nil, _, _, H => H
  | _, _, .keep (F := F) h, Γ, hΓ, H => by
    rw [VExpr.tele_ctx_cons] at hΓ H ⊢
    exact VEnv.HasType.swapCtx henv h hΓ H
  | _, _, .swap (F := F) (Fs₀ := Fs₀) (b₀ := b₀) (B₀ := B₀) hFs hb hB h, Γ, hΓ, H => by
    subst hFs hb hB
    rw [VExpr.tele_ctx_cons] at hΓ H
    have hΓ0 : OnCtx Γ (env.IsType U) := by
      have := OnCtx.of_appendTele (As := liftTele 1 Fs₀ 0) (Γ := F :: Γ) hΓ
      exact this.1
    have hΓ' : OnCtx ((liftTele 1 Fs₀ 0).reverse ++ VExpr.swapUnit :: Γ) (env.IsType U) := by
      refine OnCtx.weakTele henv.ordered Ctx.LiftN.one ⟨hΓ0, VExpr.swapUnit_isType⟩ ?_
      have W : Ctx.LiftN 1 Fs₀.length (Fs₀.reverse ++ Γ)
          ((liftTele 1 Fs₀ 0).reverse ++ F :: Γ) := by
        have := Ctx.LiftN.tele (As := Fs₀) (n := 1) (k := 0) (Γ := Γ) (Γ' := F :: Γ)
          Ctx.LiftN.one
        rwa [Nat.zero_add] at this
      exact OnCtx.weakN_inv henv W hΓ
    have H1 := VEnv.HasType.swapTele (A' := VExpr.swapUnit) henv hΓ H
    rw [VExpr.tele_ctx_cons]
    exact VEnv.HasType.swapCtx henv h hΓ' H1

/-- The `OnCtx` half of `VEnv.HasType.swapCtx`: the swapped context is well-formed. -/
theorem OnCtx.swapCtx {env : VEnv} {U : Nat} {b B : VExpr} (henv : VEnv.WF env) :
    ∀ {Fs Fs' : List VExpr}, VExpr.SwapCtx b B Fs Fs' → ∀ {Γ : List VExpr},
      OnCtx (Fs.reverse ++ Γ) (env.IsType U) → OnCtx (Fs'.reverse ++ Γ) (env.IsType U)
  | _, _, .nil, _, h => h
  | _, _, .keep (F := F) h, Γ, hΓ => by
    rw [VExpr.tele_ctx_cons] at hΓ ⊢
    exact OnCtx.swapCtx henv h hΓ
  | _, _, .swap (F := F) (Fs₀ := Fs₀) hFs hb hB h, Γ, hΓ => by
    subst hFs
    rw [VExpr.tele_ctx_cons] at hΓ
    have hΓ0 : OnCtx Γ (env.IsType U) := by
      have := OnCtx.of_appendTele (As := liftTele 1 Fs₀ 0) (Γ := F :: Γ) hΓ
      exact this.1
    have hΓ' : OnCtx ((liftTele 1 Fs₀ 0).reverse ++ VExpr.swapUnit :: Γ) (env.IsType U) := by
      refine VEnv.OnCtx.weakTele henv.ordered Ctx.LiftN.one ⟨hΓ0, VExpr.swapUnit_isType⟩ ?_
      have W : Ctx.LiftN 1 Fs₀.length (Fs₀.reverse ++ Γ)
          ((liftTele 1 Fs₀ 0).reverse ++ F :: Γ) := by
        have := Ctx.LiftN.tele (As := Fs₀) (n := 1) (k := 0) (Γ := Γ) (Γ' := F :: Γ)
          Ctx.LiftN.one
        rwa [Nat.zero_add] at this
      exact OnCtx.weakN_inv henv W hΓ
    rw [VExpr.tele_ctx_cons]
    exact OnCtx.swapCtx henv h hΓ'

/-! ### Supplying `SwapCtx`'s side conditions

Two small facts turn `VIndCtor.not_fieldUsed_skips` into a `SwapCtx` derivation.  `Skips` is
preserved by `instL`, so the *stored* skip fact survives the move to the use site's levels; and
a telescope all of whose entries skip their own offset **is** a `liftTele`, which is the
`.swap` constructor's first premise. -/

theorem VExpr.Skips.instL' {ls : List VLevel} {e : VExpr} {n k : Nat} (h : e.Skips n k) :
    (VExpr.instL ls e).Skips n k := by
  obtain ⟨e', rfl⟩ := VExpr.skips_iff_exists.1 h
  exact VExpr.skips_iff_exists.2 ⟨VExpr.instL ls e', by rw [VExpr.instL_liftN]⟩

/-- **A telescope whose entries each skip their own offset is a `liftTele`.**  This is the
`.swap` constructor's `Fs = liftTele 1 Fs₀ 0` premise, and the shape of the hypothesis is
exactly what `VIndCtor.not_fieldUsed_skips` delivers for the fields above an unused one. -/
theorem VExpr.liftTele_of_skips : ∀ {As : List VExpr} {k : Nat},
    (∀ j (X : VExpr), As[j]? = some X → VExpr.Skips' 1 X (k + j)) →
    ∃ As₀, As = liftTele 1 As₀ k
  | [], _, _ => ⟨[], rfl⟩
  | A :: As, k, h => by
    obtain ⟨A₀, rfl⟩ := VExpr.skips_iff_exists.1
      (VExpr.skips_iff.2 (by simpa using h 0 A rfl))
    obtain ⟨As₀, hAs⟩ := VExpr.liftTele_of_skips (As := As) (k := k + 1)
      (fun j X hX => by
        have := h (j + 1) X (by simpa using hX)
        rwa [show k + (j + 1) = k + 1 + j from by omega] at this)
    exact ⟨A₀ :: As₀, by rw [VExpr.liftTele_cons, hAs]⟩

/-! ### Non-vacuity of `SwapCtx`, at the two-field witness

Both constructors fire: `.swap` at `barDecl`'s unused field 0, `.keep` at its used field 1. -/

theorem bar_swapCtx_deriv :
    VExpr.SwapCtx (.bvar 0) barField1.type
      [barField0.type, barField1.type] [VExpr.swapUnit, barField1.type] :=
  .swap (Fs₀ := [barField1.type]) (b₀ := .bvar 0) (B₀ := barField1.type)
    rfl rfl rfl (.keep .nil)

/-- **The whole-telescope swap, run.**  Same conclusion as `bar_swapTele`, obtained from the
general machinery rather than by hand. -/
theorem bar_swapCtx :
    VEnv.HasType .empty 0 [barField1.type, VExpr.swapUnit] (.bvar 0) barField1.type := by
  have hΓ : OnCtx ([barField0.type, barField1.type].reverse ++ [])
      (VEnv.empty.IsType 0) := by
    refine ⟨⟨trivial, .succ .zero, ?_⟩, barField1.lvl, barField1_hasType_empty⟩
    show VEnv.HasType .empty 0 [] (.sort .zero) _
    exact .sortDF trivial trivial (.refl _)
  exact VEnv.HasType.swapCtx (Γ := []) ⟨[], .empty⟩ bar_swapCtx_deriv hΓ bar_swapTele_source

/-- The `.swap` premise is not hand-waved at the witness either: field 1's type really does
skip field 0's binder, and `liftTele_of_skips` turns that into the telescope shape. -/
theorem bar_liftTele_of_skips : ∃ As₀, [barField1.type] = liftTele 1 As₀ 0 :=
  VExpr.liftTele_of_skips (k := 0) (by
    intro j X hX
    match j, hX with
    | 0, hX =>
      have : X = barField1.type := by simpa using hX.symm
      subst this
      exact VExpr.skips_iff.1
        (VExpr.skips_iff_exists.2 ⟨barField1.type, barField1_liftN.symm⟩)
    | (_+1), hX => simp at hX)

/-- `SwapCtx` extends over an untouched outer prefix — the projection's *parameter* telescope,
which is never swapped. -/
theorem VExpr.SwapCtx.appendKeep {b B : VExpr} : ∀ (ps : List VExpr) {Fs Fs' : List VExpr},
    VExpr.SwapCtx b B Fs Fs' → VExpr.SwapCtx b B (ps ++ Fs) (ps ++ Fs')
  | [], _, _, h => h
  | _ :: ps, _, _, h => .keep (VExpr.SwapCtx.appendKeep ps h)

/-- **Substituting above a skipped index preserves the skip.**  This is the step that carries
the stored skip fact through the parameter spine: the parameters substitute at indices `≥ i`,
and an unused field's index is `< i`. -/
theorem VExpr.Skips.inst_of_lt {e a : VExpr} {m p : Nat} (h : e.Skips 1 m) (hlt : m < p) :
    (e.inst a p).Skips 1 m := by
  obtain ⟨e', rfl⟩ := VExpr.skips_iff_exists.1 h
  refine VExpr.skips_iff_exists.2 ⟨e'.inst a (p - 1), ?_⟩
  have h1 := VExpr.liftN_instN_lo 1 e' a (p - 1) m (by omega)
  rw [show 1 + (p - 1) = p from by omega] at h1
  exact h1.symm

/-- The `instAll` form: a whole spine substituted at indices above `m` leaves the skip at `m`
alone. -/
theorem VExpr.Skips.instAll_of_lt : ∀ {as : List VExpr} {e : VExpr} {m k : Nat},
    e.Skips 1 m → m < k → (VExpr.instAll e as k).Skips 1 m
  | [], _, _, _, h, _ => h
  | a :: as, e, m, k, h, hlt => by
    rw [VExpr.instAll_cons]
    exact VExpr.Skips.instAll_of_lt (h.inst_of_lt (by omega)) hlt

/-! ### The builder

Every position of the field prefix is either *used* — where `SwapCtx.keep` applies with no side
condition at all — or *unused*, where `VIndCtor.not_fieldUsed_skips` supplies every premise of
`SwapCtx.swap` at once.  So the `SwapCtx` derivation exists **unconditionally**; the only input
is the pointwise skip data, and `P` below is instantiated at `¬ C.FieldUsed D 0 ·`. -/

theorem VExpr.SwapCtx.build {b B : VExpr} (P : Nat → Prop) :
    ∀ (Fs : List VExpr),
      (∀ j, j < Fs.length → P j →
        (∀ j', j < j' → j' < Fs.length →
            VExpr.Skips (Fs.getD j' default) 1 (j' - j - 1)) ∧
          b.Skips 1 (Fs.length - j - 1) ∧ B.Skips 1 (Fs.length - j - 1)) →
      ∃ Fs', VExpr.SwapCtx b B Fs Fs' ∧ Fs'.length = Fs.length ∧
        (∀ j, ¬ P j → Fs'.getD j default = Fs.getD j default) ∧
        (∀ j, Fs'.getD j default = Fs.getD j default
          ∨ Fs'.getD j default = VExpr.swapUnit)
  | [], _ => ⟨[], .nil, rfl, fun _ _ => rfl, fun _ => .inl rfl⟩
  | F :: Fs, h => by
    have hrec : ∀ j, j < Fs.length → P (j + 1) →
        (∀ j', j < j' → j' < Fs.length →
            VExpr.Skips (Fs.getD j' default) 1 (j' - j - 1)) ∧
          b.Skips 1 (Fs.length - j - 1) ∧ B.Skips 1 (Fs.length - j - 1) := by
      intro j hj hP
      obtain ⟨h1, h2, h3⟩ := h (j + 1) (by simp; omega) hP
      refine ⟨fun j' hj' hj'' => ?_, ?_, ?_⟩
      · have := h1 (j' + 1) (by omega) (by simp; omega)
        rw [show (F :: Fs).getD (j' + 1) default = Fs.getD j' default from rfl,
          show j' + 1 - (j + 1) - 1 = j' - j - 1 from by omega] at this
        exact this
      · rw [show Fs.length - j - 1 = (F :: Fs).length - (j + 1) - 1 from by simp] at *
        exact h2
      · rw [show Fs.length - j - 1 = (F :: Fs).length - (j + 1) - 1 from by simp] at *
        exact h3
    obtain ⟨Fs', hsw, hlen, hkeep, halt⟩ := VExpr.SwapCtx.build (b := b) (B := B)
      (fun j => P (j + 1)) Fs hrec
    by_cases hP : P 0
    · obtain ⟨h1, h2, h3⟩ := h 0 (by simp) hP
      obtain ⟨Fs₀, hFs₀⟩ := VExpr.liftTele_of_skips (As := Fs) (k := 0) (by
        intro j X hX
        have hj : j < Fs.length := by
          rcases Nat.lt_or_ge j Fs.length with h' | h'
          · exact h'
          · rw [List.getElem?_eq_none h'] at hX; exact absurd hX nofun
        have := h1 (j + 1) (by omega) (by simp; omega)
        rw [show (F :: Fs).getD (j + 1) default = Fs.getD j default from rfl,
          show j + 1 - 0 - 1 = j from by omega] at this
        rw [show Fs.getD j default = X from by
          rw [List.getD_eq_getElem?_getD, hX]; rfl] at this
        simpa [Nat.zero_add] using VExpr.skips_iff.1 this)
      have hlen₀ : Fs₀.length = Fs.length := by
        rw [hFs₀]; simp [VExpr.length_liftTele]
      obtain ⟨b₀, hb₀⟩ := VExpr.skips_iff_exists.1
        (show b.Skips 1 Fs₀.length by rw [hlen₀]; simpa using h2)
      obtain ⟨B₀, hB₀⟩ := VExpr.skips_iff_exists.1
        (show B.Skips 1 Fs₀.length by rw [hlen₀]; simpa using h3)
      refine ⟨VExpr.swapUnit :: Fs', .swap hFs₀ hb₀ hB₀ hsw, by simp [hlen], ?_, ?_⟩
      · intro j hj
        match j with
        | 0 => exact absurd hP hj
        | j+1 => exact hkeep j hj
      · intro j
        match j with
        | 0 => exact .inr rfl
        | j+1 => exact halt j
    · refine ⟨F :: Fs', .keep hsw, by simp [hlen], ?_, ?_⟩
      · intro j hj
        match j with
        | 0 => rfl
        | j+1 => exact hkeep j hj
      · intro j
        match j with
        | 0 => exact .inl rfl
        | j+1 => exact halt j

/-- **The `SwapCtx` derivation for a constructor's field prefix, unconditionally.**  Every
premise `SwapCtx.swap` needs at an unused position is `VIndCtor.not_fieldUsed_skips`, moved to
the use site's levels by `Skips.instL'`; used positions need nothing.

Together with `VEnv.HasType.swapCtx` this replaces `ftype_hasType`'s context by one in which
every unused field binder is the *inhabited* `VExpr.swapUnit`, which is what lets the
projection's spine stay saturated without an inhabitant of the unused field's own type. -/
theorem VIndCtor.swapCtx_fields (C : VIndCtor) (D : VInductDecl') (jt : Nat)
    (us : List VLevel) {i : Nat} (hi : i < C.fields.length) :
    ∃ Fs', VExpr.SwapCtx ((C.fields.getD i default).type.instL us)
        (.sort ((C.fields.getD i default).lvl.inst us))
        ((C.fields.take i).map (fun F => F.type.instL us)) Fs' ∧
      Fs'.length = i ∧
      (∀ k, k < i → C.FieldUsed D jt k →
        Fs'.getD k default = (C.fields.getD k default).type.instL us) ∧
      (∀ k, k < i → Fs'.getD k default = (C.fields.getD k default).type.instL us
        ∨ Fs'.getD k default = VExpr.swapUnit) := by
  have hFlen : ((C.fields.take i).map (fun F => F.type.instL us)).length = i := by
    simp; omega
  have hget : ∀ k, k < i → ((C.fields.take i).map (fun F => F.type.instL us)).getD k default
      = (C.fields.getD k default).type.instL us := by
    intro k hk
    have hk' : k < C.fields.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hk,
      List.getElem?_eq_getElem hk', List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk']
    rfl
  obtain ⟨Fs', hsw, hlen, hkeep, halt⟩ :=
    VExpr.SwapCtx.build (b := (C.fields.getD i default).type.instL us)
      (B := .sort ((C.fields.getD i default).lvl.inst us))
      (fun j => ¬ C.FieldUsed D jt j)
      ((C.fields.take i).map (fun F => F.type.instL us)) (by
        intro j hj hP
        rw [hFlen] at hj
        refine ⟨fun j' hj' hj'' => ?_, ?_, ?_⟩
        · rw [hFlen] at hj''
          rw [hget j' hj'']
          have := C.not_fieldUsed_skips (D := D) (j := jt) hP hj' (by omega)
          rw [show j' - 1 - j = j' - j - 1 from by omega] at this
          exact (VExpr.skips_iff.2 this).instL'
        · rw [hFlen]
          have := C.not_fieldUsed_skips (D := D) (j := jt) hP hj hi
          rw [show i - 1 - j = i - j - 1 from by omega] at this
          exact (VExpr.skips_iff.2 this).instL'
        · exact VExpr.skips_iff_exists.2
            ⟨.sort ((C.fields.getD i default).lvl.inst us), rfl⟩)
  refine ⟨Fs', hsw, by omega, fun k hk hu => ?_, fun k hk => ?_⟩
  · rw [hkeep k (not_not_intro hu), hget k hk]
  · rcases halt k with h | h
    · exact .inl (by rw [h, hget k hk])
    · exact .inr h

/-! ## The crux, assembled

`ftype_hasType` types field `i` over the *full* field prefix.  `ftype_hasType_swapped` types it
over the prefix with every unused binder replaced by `VExpr.swapUnit` — and that is the whole
of `TrProj.wf`'s remaining mathematical content.  What is left after this is plumbing:
`VEnv.HasType.instAll` at the swapped telescope (its spine now has `.sort .zero` at the
swapped positions, which `VExpr.swapUnit_inhabited` types), and threading `TrProj`'s *guarded*
F17 clause through `projArgs_hasArgs` / `projMotiveBody_hasType` / `projMinor_hasType` /
`projTerm_hasType`, none of which needs a fact that is not already here.

The one dependency the swap introduces is `VEnv.HasType.weakN_iff`, backed by
`IsDefEqU.weakN_iff`'s `sorry` (`Theory/Typing/UniqueTyping.lean:172`) — an existing hole owned
by another stream, not a new statement. -/

/-- **Field `i`'s type, typed over the swapped field prefix.** -/
theorem ftype_hasType_swapped {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (H : env.IsStructure S D T C) (hI : D.IotaCtx env)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length) {Γ'' : List VExpr}
    (hΓ : OnCtx ((D.params.map (VExpr.instL us)
      ++ (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Γ'') (env.IsType U))
    {Fs' : List VExpr}
    (hsw : VExpr.SwapCtx ((C.fields.getD i default).type.instL us)
        (.sort ((C.fields.getD i default).lvl.inst us))
        ((C.fields.take i).map (fun F => F.type.instL us)) Fs') :
    env.HasType U ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Γ'')
      ((C.fields.getD i default).type.instL us)
      (.sort ((C.fields.getD i default).lvl.inst us)) :=
  VEnv.HasType.swapCtx henv (hsw.appendKeep (D.params.map (VExpr.instL us))) hΓ
    (ftype_hasType henv.ordered H hI h3 h7 hcl hi Γ'')

/-- …packaged with the telescope that does the swapping, which is what the caller has to build
its `HasArgs` over: it agrees with the original at every *used* position, and is the inhabited
`VExpr.swapUnit` elsewhere. -/
theorem ftype_hasType_swapped_exists {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (H : env.IsStructure S D T C) (hI : D.IotaCtx env)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length) {Γ'' : List VExpr}
    (hΓ : OnCtx ((D.params.map (VExpr.instL us)
      ++ (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Γ'') (env.IsType U)) :
    ∃ Fs' : List VExpr, Fs'.length = i ∧
      (∀ k, k < i → C.FieldUsed D 0 k →
        Fs'.getD k default = (C.fields.getD k default).type.instL us) ∧
      (∀ k, k < i → Fs'.getD k default = (C.fields.getD k default).type.instL us
        ∨ Fs'.getD k default = VExpr.swapUnit) ∧
      env.HasType U ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Γ'')
        ((C.fields.getD i default).type.instL us)
        (.sort ((C.fields.getD i default).lvl.inst us)) := by
  obtain ⟨Fs', hsw, hlen, hkeep, halt⟩ := C.swapCtx_fields D 0 us hi
  exact ⟨Fs', hlen, hkeep, halt,
    ftype_hasType_swapped henv H hI h3 h7 hcl hi hΓ hsw⟩

/-- **The builder for `InstAllSkip`.**  Only the *original* term's skip data is needed: a
substitution at a strictly higher index cannot create an occurrence at a lower one
(`VExpr.Skips.inst_of_lt`), so the condition never has to be re-established as the spine is
consumed.  Positions `j` where the two spines agree need nothing at all. -/
theorem VExpr.InstAllSkip.build : ∀ {as bs : List VExpr} {e : VExpr} {k : Nat},
    as.length = bs.length →
    (∀ j, j < as.length → as.getD j default ≠ bs.getD j default →
      e.Skips 1 (k + as.length - 1 - j)) →
    VExpr.InstAllSkip e as bs k
  | [], [], _, _, _, _ => .nil
  | a :: as, b :: bs, e, k, hl, h => by
    have hl' : as.length = bs.length := by simpa using hl
    have hrec : ∀ j, j < as.length →
        as.getD j default ≠ bs.getD j default →
        (e.inst a (k + as.length)).Skips 1 (k + as.length - 1 - j) := by
      intro j hj hne
      have h1 := h (j + 1) (by simp; omega) (by simpa using hne)
      rw [show k + (a :: as).length - 1 - (j + 1) = k + as.length - 1 - j from by
        simp; omega] at h1
      exact h1.inst_of_lt (by omega)
    by_cases hab : a = b
    · subst hab
      exact .same hl' (VExpr.InstAllSkip.build hl' hrec)
    · have hs : e.Skips' 1 (k + as.length) := by
        have h0 := h 0 (by simp) (by simpa using hab)
        rw [show k + (a :: as).length - 1 - 0 = k + as.length from by simp] at h0
        exact VExpr.skips_iff.1 h0
      exact .skip hl' hs (VExpr.InstAllSkip.build hl' hrec)

/-- **The paired builder.**  The projection route needs the swapped *telescope* and the swapped
*spine* to be swapped at the same positions, so they are built in one recursion.  `d` is the
term supplied at a swapped position; the caller takes `d := .sort .zero`, which
`VExpr.swapUnit_inhabited` types against `VExpr.swapUnit`. -/
theorem VExpr.SwapCtx.buildPair {b B : VExpr} (P : Nat → Prop) (d : VExpr) :
    ∀ (Fs es : List VExpr), Fs.length = es.length →
      (∀ j, j < Fs.length → P j →
        (∀ j', j < j' → j' < Fs.length →
            VExpr.Skips (Fs.getD j' default) 1 (j' - j - 1)) ∧
          b.Skips 1 (Fs.length - j - 1) ∧ B.Skips 1 (Fs.length - j - 1)) →
      ∃ Fs' es' : List VExpr, VExpr.SwapCtx b B Fs Fs' ∧ Fs'.length = Fs.length ∧
        es'.length = es.length ∧
        (∀ j, ¬ P j → Fs'.getD j default = Fs.getD j default
          ∧ es'.getD j default = es.getD j default) ∧
        (∀ j, P j → j < Fs.length →
          Fs'.getD j default = VExpr.swapUnit ∧ es'.getD j default = d)
  | [], es, hlen, _ =>
    ⟨[], es, .nil, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ hj => absurd hj (by simp)⟩
  | F :: Fs, [], hlen, _ => by simp at hlen
  | F :: Fs, e :: es, hlen, h => by
    have hlen' : Fs.length = es.length := by simpa using hlen
    have hrec : ∀ j, j < Fs.length → P (j + 1) →
        (∀ j', j < j' → j' < Fs.length →
            VExpr.Skips (Fs.getD j' default) 1 (j' - j - 1)) ∧
          b.Skips 1 (Fs.length - j - 1) ∧ B.Skips 1 (Fs.length - j - 1) := by
      intro j hj hP
      obtain ⟨h1, h2, h3⟩ := h (j + 1) (by simp; omega) hP
      refine ⟨fun j' hj' hj'' => ?_, ?_, ?_⟩
      · have := h1 (j' + 1) (by omega) (by simp; omega)
        rw [show (F :: Fs).getD (j' + 1) default = Fs.getD j' default from rfl,
          show j' + 1 - (j + 1) - 1 = j' - j - 1 from by omega] at this
        exact this
      · rw [show Fs.length - j - 1 = (F :: Fs).length - (j + 1) - 1 from by simp] at *
        exact h2
      · rw [show Fs.length - j - 1 = (F :: Fs).length - (j + 1) - 1 from by simp] at *
        exact h3
    obtain ⟨Fs', es', hsw, hlenF, hlenE, hkeep, hswap⟩ :=
      VExpr.SwapCtx.buildPair (b := b) (B := B) (fun j => P (j + 1)) d Fs es hlen' hrec
    by_cases hP : P 0
    · obtain ⟨h1, h2, h3⟩ := h 0 (by simp) hP
      obtain ⟨Fs₀, hFs₀⟩ := VExpr.liftTele_of_skips (As := Fs) (k := 0) (by
        intro j X hX
        have hj : j < Fs.length := by
          rcases Nat.lt_or_ge j Fs.length with h' | h'
          · exact h'
          · rw [List.getElem?_eq_none h'] at hX; exact absurd hX nofun
        have := h1 (j + 1) (by omega) (by simp; omega)
        rw [show (F :: Fs).getD (j + 1) default = Fs.getD j default from rfl,
          show j + 1 - 0 - 1 = j from by omega] at this
        rw [show Fs.getD j default = X from by
          rw [List.getD_eq_getElem?_getD, hX]; rfl] at this
        simpa [Nat.zero_add] using VExpr.skips_iff.1 this)
      have hlen₀ : Fs₀.length = Fs.length := by rw [hFs₀]; simp [VExpr.length_liftTele]
      obtain ⟨b₀, hb₀⟩ := VExpr.skips_iff_exists.1
        (show b.Skips 1 Fs₀.length by rw [hlen₀]; simpa using h2)
      obtain ⟨B₀, hB₀⟩ := VExpr.skips_iff_exists.1
        (show B.Skips 1 Fs₀.length by rw [hlen₀]; simpa using h3)
      refine ⟨VExpr.swapUnit :: Fs', d :: es', .swap hFs₀ hb₀ hB₀ hsw,
        by simp [hlenF], by simp [hlenE], ?_, ?_⟩
      · intro j hj
        match j with
        | 0 => exact absurd hP hj
        | j+1 => exact hkeep j hj
      · intro j hj hjl
        match j with
        | 0 => exact ⟨rfl, rfl⟩
        | j+1 => exact hswap j hj (by simpa using hjl)
    · refine ⟨F :: Fs', e :: es', .keep hsw, by simp [hlenF], by simp [hlenE], ?_, ?_⟩
      · intro j hj
        match j with
        | 0 => exact ⟨rfl, rfl⟩
        | j+1 => exact hkeep j hj
      · intro j hj hjl
        match j with
        | 0 => exact absurd hj hP
        | j+1 => exact hswap j hj (by simpa using hjl)

/-! ## The projection instance of the paired builder -/

/-- The field-prefix context at the use site's levels, over any well-formed `Δ`.  This is
`projMinor_hasType`'s `hΓ'`, extracted so the swapped route can reuse it. -/
theorem onCtxFields_instL {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : env.Ordered) (hI : D.IotaCtx env) (H : env.IsStructure S D T C)
    (h7 : ∀ l ∈ us, l.WF U) {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U)) (i : Nat) :
    OnCtx ((D.params.map (VExpr.instL us)
      ++ (C.fields.take i).map (fun F => F.type.instL us)).reverse ++ Δ) (env.IsType U) := by
  have hCwf : VIndCtor.WF env D 0 T C := hI.toRecCtx.ctors 0 T H.types0 C H.memCtor
  have h0 := OnCtx.instL (env := env) (ls := us) (U' := U) h7 (hCwf.onCtxFields henv i)
  rw [List.map_append, List.map_reverse, List.map_reverse, ← List.reverse_append] at h0
  simp only [List.map_map, Function.comp_def] at h0
  exact OnCtx.appendR henv hΔ (OnCtx.ctxClosed henv h0) h0

/-- **The swap data for the projection, in one package.**  The telescope and the spine are
swapped at the same positions — the ones the *guarded* F17 clause says nothing about — the
swapped term is provably the same term, and the field type is typed over the swapped
context. -/
theorem VIndCtor.swapData {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (H : env.IsStructure S D T C) (hI : D.IotaCtx env)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U) (hcl : D.ProjClosed T C)
    {i : Nat} (hi : i < C.fields.length)
    {Δ : List VExpr} (hΔ : OnCtx Δ (env.IsType U))
    (qs es : List VExpr) (hes : es.length = i) :
    ∃ Fs' es' : List VExpr, Fs'.length = i ∧ es'.length = i ∧
      (∀ k, k < i → C.FieldUsed D 0 k →
        Fs'.getD k default = (C.fields.getD k default).type.instL us
        ∧ es'.getD k default = es.getD k default) ∧
      (∀ k, k < i → ¬ C.FieldUsed D 0 k →
        Fs'.getD k default = VExpr.swapUnit ∧ es'.getD k default = VExpr.sort .zero) ∧
      VExpr.instAll ((C.fields.getD i default).type.instL us) (qs ++ es) 0
        = VExpr.instAll ((C.fields.getD i default).type.instL us) (qs ++ es') 0 ∧
      env.HasType U ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Δ)
        ((C.fields.getD i default).type.instL us)
        (.sort ((C.fields.getD i default).lvl.inst us)) ∧
      OnCtx ((D.params.map (VExpr.instL us) ++ Fs').reverse ++ Δ) (env.IsType U) := by
  have hFlen : ((C.fields.take i).map (fun F => F.type.instL us)).length = i := by
    simp; omega
  have hget : ∀ k, k < i → ((C.fields.take i).map (fun F => F.type.instL us)).getD k default
      = (C.fields.getD k default).type.instL us := by
    intro k hk
    have hk' : k < C.fields.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hk,
      List.getElem?_eq_getElem hk', List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk']
    rfl
  obtain ⟨Fs', es', hsw, hlenF, hlenE, hkeep, hswap⟩ :=
    VExpr.SwapCtx.buildPair (b := (C.fields.getD i default).type.instL us)
      (B := .sort ((C.fields.getD i default).lvl.inst us))
      (fun j => ¬ C.FieldUsed D 0 j) (VExpr.sort .zero)
      ((C.fields.take i).map (fun F => F.type.instL us)) es (by rw [hFlen, hes]) (by
        intro j hj hP
        rw [hFlen] at hj
        refine ⟨fun j' hj' hj'' => ?_, ?_, ?_⟩
        · rw [hFlen] at hj''
          rw [hget j' hj'']
          have := C.not_fieldUsed_skips (D := D) (j := 0) hP hj' (by omega)
          rw [show j' - 1 - j = j' - j - 1 from by omega] at this
          exact (VExpr.skips_iff.2 this).instL'
        · rw [hFlen]
          have := C.not_fieldUsed_skips (D := D) (j := 0) hP hj hi
          rw [show i - 1 - j = i - j - 1 from by omega] at this
          exact (VExpr.skips_iff.2 this).instL'
        · exact VExpr.skips_iff_exists.2
            ⟨.sort ((C.fields.getD i default).lvl.inst us), rfl⟩)
  rw [hFlen] at hlenF
  rw [hes] at hlenE
  refine ⟨Fs', es', hlenF, hlenE, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hu
    obtain ⟨h1, h2⟩ := hkeep k (not_not_intro hu)
    exact ⟨by rw [h1, hget k hk], h2⟩
  · intro k hk hu
    exact hswap k hu (by rw [hFlen]; exact hk)
  · rw [VExpr.instAll_append, VExpr.instAll_append, hlenE, hes]
    refine VExpr.instAll_congr_of_skip (VExpr.InstAllSkip.build (by omega) ?_)
    intro j hj hne
    have hju : ¬ C.FieldUsed D 0 j := by
      intro hu
      exact hne (hkeep j (not_not_intro hu)).2.symm
    have hji : j < i := by omega
    have hsk := (VExpr.skips_iff.2
      (C.not_fieldUsed_skips (D := D) (j := 0) hju hji hi)).instL'
      (ls := us)
    rw [show i - 1 - j = 0 + es.length - 1 - j from by omega] at hsk
    exact hsk.instAll_of_lt (by omega)
  · exact ftype_hasType_swapped henv H hI h3 h7 hcl hi
      (onCtxFields_instL henv.ordered hI H h7 hΔ i) hsw
  · exact OnCtx.swapCtx henv (hsw.appendKeep (D.params.map (VExpr.instL us)))
      (onCtxFields_instL henv.ordered hI H h7 hΔ i)

/-! ## Consuming the swapped data

Three small lemmas turn `swapData` into the two typing facts the projection chain needs. -/

/-- `HasArgs.ofMap` with the spine given by `getD` rather than by a function — which is the
form a *swapped* spine takes, since it is not `(range i).map f`. -/
theorem VEnv.HasArgs.ofGetD {env : VEnv} {U : Nat} {Γ : List VExpr}
    {As as es : List VExpr} : ∀ {i : Nat}, i ≤ As.length → es.length = i →
      (∀ k, k < i → env.HasType U Γ (es.getD k default)
        (VExpr.instAll (As.getD k default) (as ++ es.take k))) →
      env.HasArgs U Γ (VExpr.instAllTele (As.take i) as) es
  | 0, _, hes, _ => by
    rw [List.eq_nil_of_length_eq_zero hes]; simp; exact .nil
  | i+1, hi, hes, h => by
    have hlt : i < As.length := by omega
    have htake : As.take (i+1) = As.take i ++ [As.getD i default] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have hei : i < es.length := by omega
    have hesplit : es = es.take i ++ [es.getD i default] := by
      have h1 : es.take (i + 1) = es := List.take_of_length_le (by omega)
      conv => lhs; rw [← h1]
      rw [List.take_add_one, List.getElem?_eq_getElem hei]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hei]
    rw [htake, VExpr.instAllTele_append]
    conv => rhs; rw [hesplit]
    refine VEnv.HasArgs.append
      (VEnv.HasArgs.ofGetD (es := es.take i) (by omega) (by simp; omega) fun k hk => ?_) ?_
    · rw [List.take_take, show min k i = k from by omega,
        show (es.take i).getD k default = es.getD k default from by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_take_of_lt hk]]
      exact h k (by omega)
    · have hlen : (es.take i).length = i := by simp; omega
      simp only [List.length_take, Nat.zero_add, Nat.min_def]
      rw [if_pos (by omega)]
      simp only [VExpr.instAllTele_cons, VExpr.instAllTele_nil]
      refine .cons ?_ .nil
      have := h i (by omega)
      rwa [VExpr.instAll_append, hlen, Nat.zero_add] at this

/-- **Swapping the spine does not change the term.**  Field `j`'s type skips every unused
position below `j`, so a spine that differs from the real one only there substitutes to the
same thing.  This is `instAll_congr_of_skip` at the projection's own indices. -/
theorem VIndCtor.instAll_swap_eq (C : VIndCtor) (D : VInductDecl') (us : List VLevel)
    {j : Nat} (hj : j < C.fields.length) {es es' qs : List VExpr}
    (hlen : es.length = es'.length) (hes : es.length = j)
    (hagree : ∀ k, k < es.length → C.FieldUsed D 0 k →
      es.getD k default = es'.getD k default) :
    VExpr.instAll ((C.fields.getD j default).type.instL us) (qs ++ es) 0
      = VExpr.instAll ((C.fields.getD j default).type.instL us) (qs ++ es') 0 := by
  rw [VExpr.instAll_append, VExpr.instAll_append, ← hlen]
  refine VExpr.instAll_congr_of_skip (VExpr.InstAllSkip.build hlen ?_)
  intro m hm hne
  have hmu : ¬ C.FieldUsed D 0 m := fun hu => hne (hagree m hm hu)
  have hmj : m < j := by omega
  have hsk := (VExpr.skips_iff.2
    (C.not_fieldUsed_skips (D := D) (j := 0) hmu hmj hj)).instL' (ls := us)
  rw [show j - 1 - m = 0 + es.length - 1 - m from by omega] at hsk
  exact hsk.instAll_of_lt (by omega)

/-- **The swapped `instAll_field_isType`.**  The spine is still saturated — the swapped
positions carry `.sort .zero` — so this is the *existing* `VEnv.HasType.instAll`, applied to
the swapped context. -/
theorem instAll_field_isType_swapped {env : VEnv} {U : Nat} (henv : env.Ordered)
    {Δ qs es es' Fs' As : List VExpr} {b : VExpr} {B' : VLevel}
    (hqs : env.HasArgs U Δ As qs)
    (hes' : env.HasArgs U Δ (VExpr.instAllTele Fs' qs) es')
    (hty : env.HasType U ((As ++ Fs').reverse ++ Δ) b (.sort B'))
    (heq : VExpr.instAll b (qs ++ es) 0 = VExpr.instAll b (qs ++ es') 0) :
    env.HasType U Δ (VExpr.instAll b (qs ++ es)) (.sort B') := by
  rw [heq]
  have := VEnv.HasType.instAll henv (VEnv.HasArgs.append hqs hes') hty
  rwa [VExpr.instAll_sort] at this

/-! ## The swapped induction hypothesis

`projArgs_hasArgs` packages the induction hypothesis at *every* `k < i`, which is exactly what
the refuted route needed and cannot have.  The swapped version needs it only at the **used**
`k`; the unused positions are filled by `VExpr.swapUnit_inhabited`, which needs nothing. -/

theorem projArgs_hasArgs_swapped {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (IH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    {Fs' es' : List VExpr}
    (hlenF : Fs'.length = i) (hlenE : es'.length = i)
    (hused : ∀ k, k < i → C.FieldUsed D 0 k →
      Fs'.getD k default = (C.fields.getD k default).type.instL us
      ∧ es'.getD k default = D.projTerm T C us (ps.map (·.liftN (T.indices.length+1)))
          (bvars 1 T.indices.length) k (.bvar 0))
    (hunused : ∀ k, k < i → ¬ C.FieldUsed D 0 k →
      Fs'.getD k default = VExpr.swapUnit ∧ es'.getD k default = VExpr.sort .zero) :
    env.HasArgs U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAllTele Fs' (ps.map (·.liftN (T.indices.length+1)))) es' := by
  obtain ⟨hOnΔ1, hctorTy⟩ := motiveCtx_wf henv hI H h3 h7 hΓ hps hpsA
  have hclI : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) ps.length := by
    rw [hps]; exact VExpr.ClosedTele.map_instL hcl.indices
  have hΔ : OnCtx
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U) := ⟨hOnΔ1, hctorTy⟩
  have hW : Ctx.LiftN (T.indices.length + 1) 0 Γ
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)) := by
    have := Ctx.LiftN.zero (Γ := Γ) (n := T.indices.length + 1)
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse) (by simp)
    simpa using this
  have hqs := VEnv.HasArgs.weakN henv hW hpsA
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL hcl.params) (Nat.zero_le _)] at hqs
  have hjs := VEnv.HasArgs.bvars (env := env) (U := U)
    (Δ := [(VExpr.const T.name us).mkApp
      (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)])
    (As := VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) (Γ₀ := Γ)
  rw [List.length_cons, List.length_nil, VExpr.length_instAllTele, List.length_map,
    show 0 + 1 = 1 from rfl, Nat.add_comm 1 T.indices.length,
    VExpr.liftTele_instAllTele₀ hclI, List.singleton_append] at hjs
  have hbv0 : env.HasType U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (.bvar 0)
      ((VExpr.const S us).mkApp
        (ps.map (·.liftN (T.indices.length+1)) ++ bvars 1 T.indices.length)) := by
    have h := VEnv.HasType.bvar (env := env) (U := U) (Lookup.zero
      (Γ := (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)
      (ty := (VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)))
    rw [VExpr.lift, VExpr.liftN_mkApp, VExpr.liftN, List.map_append, List.map_map,
      Function.comp_def, VExpr.map_liftN_bvars_lo (Nat.zero_le _)] at h
    simp only [VExpr.liftN_liftN] at h
    rw [← H.name]
    exact h
  have hFtake : Fs'.take i = Fs' := List.take_of_length_le (by omega)
  rw [← hFtake]
  refine VEnv.HasArgs.ofGetD (by omega) hlenE fun k hk => ?_
  by_cases hu : C.FieldUsed D 0 k
  · obtain ⟨hF, hE⟩ := hused k hk hu
    rw [hF, hE]
    have hIHk := IH k hk hu hΔ hbv0 (by simp [hps]) (by simp) hqs hjs
    have heq : VExpr.instAll ((C.fields.getD k default).type.instL us)
        ((ps.map (·.liftN (T.indices.length+1)))
          ++ (List.range k).map (fun m => D.projTerm T C us
              (ps.map (·.liftN (T.indices.length+1))) (bvars 1 T.indices.length) m (.bvar 0))) 0
        = VExpr.instAll ((C.fields.getD k default).type.instL us)
            ((ps.map (·.liftN (T.indices.length+1))) ++ es'.take k) 0 := by
      refine C.instAll_swap_eq D us (by omega) (by simp; omega) (by simp) ?_
      intro m hm hmu
      have hmk : m < k := by simpa using hm
      obtain ⟨-, hEm⟩ := hused m (by omega) hmu
      rw [show ((List.range k).map (fun m => D.projTerm T C us
            (ps.map (·.liftN (T.indices.length+1))) (bvars 1 T.indices.length) m
            (.bvar 0))).getD m default
          = D.projTerm T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) m (.bvar 0) from by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range (by omega)]; rfl,
        show (es'.take k).getD m default = es'.getD m default from by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_take_of_lt hmk],
        hEm]
    rw [← heq]
    exact hIHk
  · obtain ⟨hF, hE⟩ := hunused k hk hu
    rw [hF, hE]
    simp only [VExpr.swapUnit, VExpr.instAll_sort]
    exact VExpr.swapUnit_inhabited

/-- **The motive's body is a type**, from the *swapped* spine — the guarded F17 clause supplies
`hlv` at `k = i` only, and nothing is asked at the unused earlier positions. -/
theorem projMotiveBody_hasType_swapped {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : env.Ordered) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (hlv : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    {Γ ps : List VExpr} (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    {earlier es' Fs' : List VExpr}
    (hes' : env.HasArgs U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAllTele Fs' (ps.map (·.liftN (T.indices.length+1)))) es')
    (hty : env.HasType U ((D.params.map (VExpr.instL us) ++ Fs').reverse ++
        (((VExpr.const T.name us).mkApp
            (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
          :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)))
      ((C.fields.getD i default).type.instL us)
      (.sort ((C.fields.getD i default).lvl.inst us)))
    (heq : VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1)) ++ earlier) 0
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
          (ps.map (·.liftN (T.indices.length+1)) ++ es') 0) :
    env.HasType U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1)) ++ earlier))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  have hW : Ctx.LiftN (T.indices.length + 1) 0 Γ
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ)) := by
    have := Ctx.LiftN.zero (Γ := Γ) (n := T.indices.length + 1)
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse) (by simp)
    simpa using this
  have hqs := VEnv.HasArgs.weakN henv hW hpsA
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL hcl.params) (Nat.zero_le _)] at hqs
  have hbody := instAll_field_isType_swapped henv hqs hes' hty heq
  exact VEnv.IsDefEq.defeqDF
    (VEnv.IsDefEq.sortDF (VLevel.WF.inst h7)
      (VLevel.WF.inst (VInductDecl'.projLvls_wf (C := C) h7 i)) hlv) hbody

/-- **The motive inhabits the recursor's motive binder**, from the guarded hypotheses.  Same
conclusion as `projMotiveTerm_hasType`; the difference is entirely in what is assumed —
`ProjHasType` at the **used** earlier indices only, and `hlv` at `i` only. -/
theorem projMotiveTerm_hasType_swapped {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U Γ (projMotiveTerm D T C us ps i)
      (VExpr.instAll ((D.motiveType 0).instL (D.projLvls C us i)) ps) := by
  have hord := henv.ordered
  obtain ⟨hOnΔ1, uc, hctorTy⟩ := motiveCtx_wf hord hI H h3 h7 hΓ hps hpsA
  have hΔ : OnCtx
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U) := ⟨hOnΔ1, uc, hctorTy⟩
  obtain ⟨Fs', es', hlenF, hlenE, hused, hunused, heq, hty, -⟩ :=
    C.swapData henv H hI h3 h7 hcl hi hΔ (ps.map (·.liftN (T.indices.length+1)))
      (D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
        (bvars 1 T.indices.length) i)
      (D.length_projArgs T C us ..)
  have hgetArgs : ∀ k, k < i →
      (D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
        (bvars 1 T.indices.length) i).getD k default
      = D.projTerm T C us (ps.map (·.liftN (T.indices.length+1)))
          (bvars 1 T.indices.length) k (.bvar 0) := by
    intro k hk
    rw [D.projArgs_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk]
    rfl
  have hes' := projArgs_hasArgs_swapped hord hI H h3 h7 hcl hi hIH hΓ hps hpsA
    hlenF hlenE
    (fun k hk hu => ⟨(hused k hk hu).1, by rw [(hused k hk hu).2, hgetArgs k hk]⟩)
    hunused
  rw [projMotiveTerm, motiveType_instL_instAll D T C H.typesD h3 hps]
  exact VEnv.HasType.mkLams hOnΔ1 (VEnv.HasType.lam hctorTy
    (projMotiveBody_hasType_swapped hord hI H h3 h7 hcl hi hlvi hps hpsA hes' hty heq))

/-! ## More swapped plumbing -/

/-- Any spine can be swapped at the same positions; no side condition is involved, because a
spine — unlike a telescope — has nothing above it that could mention the swapped entry.  This
is what lets the *two* spines of `instAllCongrSort` be swapped in step. -/
theorem VExpr.swapSpine_exists (P : Nat → Prop) (d : VExpr) : ∀ (es : List VExpr),
    ∃ es' : List VExpr, es'.length = es.length ∧
      (∀ k, ¬ P k → es'.getD k default = es.getD k default) ∧
      (∀ k, P k → k < es.length → es'.getD k default = d)
  | [] => ⟨[], rfl, fun _ _ => rfl, fun _ _ h => absurd h (by simp)⟩
  | e :: es => by
    obtain ⟨es', hl, h1, h2⟩ := VExpr.swapSpine_exists (fun j => P (j + 1)) d es
    by_cases hP : P 0
    · refine ⟨d :: es', by simp [hl], fun k hk => ?_, fun k hk hkl => ?_⟩
      · match k with
        | 0 => exact absurd hP hk
        | k+1 => exact h1 k hk
      · match k with
        | 0 => rfl
        | k+1 => exact h2 k hk (by simpa using hkl)
    · refine ⟨e :: es', by simp [hl], fun k hk => ?_, fun k hk hkl => ?_⟩
      · match k with
        | 0 => rfl
        | k+1 => exact h1 k hk
      · match k with
        | 0 => exact absurd hk hP
        | k+1 => exact h2 k hk (by simpa using hkl)

/-- `HasArgsDF.ofMap` with both spines given by `getD`. -/
theorem VEnv.HasArgsDF.ofGetD {env : VEnv} {U : Nat} {Γ : List VExpr}
    {As as es fs : List VExpr} : ∀ {i : Nat}, i ≤ As.length →
      es.length = i → fs.length = i →
      (∀ k, k < i → env.IsDefEq U Γ (es.getD k default) (fs.getD k default)
        (VExpr.instAll (As.getD k default) (as ++ es.take k))) →
      env.HasArgsDF U Γ (VExpr.instAllTele (As.take i) as) es fs
  | 0, _, hes, hfs, _ => by
    rw [List.eq_nil_of_length_eq_zero hes, List.eq_nil_of_length_eq_zero hfs]
    simp; exact .nil
  | i+1, hi, hes, hfs, h => by
    obtain ⟨es₀, e, rfl⟩ : ∃ es₀ e, es = es₀ ++ [e] := by
      rcases List.eq_nil_or_concat es with rfl | ⟨L, b, rfl⟩
      · simp at hes
      · exact ⟨L, b, List.concat_eq_append⟩
    obtain ⟨fs₀, f, rfl⟩ : ∃ fs₀ f, fs = fs₀ ++ [f] := by
      rcases List.eq_nil_or_concat fs with rfl | ⟨L, b, rfl⟩
      · simp at hfs
      · exact ⟨L, b, List.concat_eq_append⟩
    have hes₀ : es₀.length = i := by simpa using hes
    have hfs₀ : fs₀.length = i := by simpa using hfs
    have hlt : i < As.length := by omega
    have htake : As.take (i+1) = As.take i ++ [As.getD i default] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have hetake : (es₀ ++ [e]).take i = es₀ := List.take_left' hes₀
    have hftake : (fs₀ ++ [f]).take i = fs₀ := List.take_left' hfs₀
    have hegetD : (es₀ ++ [e]).getD i default = e := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hes₀]
      simp
    have hfgetD : (fs₀ ++ [f]).getD i default = f := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hfs₀]
      simp
    rw [htake, VExpr.instAllTele_append]
    refine VEnv.HasArgsDF.append
      (VEnv.HasArgsDF.ofGetD (es := es₀) (fs := fs₀) (by omega) hes₀ hfs₀ fun k hk => ?_) ?_
    · have := h k (by omega)
      rw [show (es₀ ++ [e]).getD k default = es₀.getD k default from by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega)],
        show (fs₀ ++ [f]).getD k default = fs₀.getD k default from by
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega)],
        show (es₀ ++ [e]).take k = es₀.take k from by
          rw [List.take_append_of_le_length (by omega)]] at this
      exact this
    · simp only [List.length_take, Nat.zero_add, Nat.min_def]
      rw [if_pos (by omega)]
      simp only [VExpr.instAllTele_cons, VExpr.instAllTele_nil]
      refine .cons ?_ .nil
      have := h i (by omega)
      rw [hegetD, hfgetD, hetake, VExpr.instAll_append, hes₀, Nat.zero_add] at this
      exact this

/-- `projMotiveBody_hasType` with the guarded hypotheses, at the real `projArgs` spine: the
swap data is built internally, so the caller only supplies the used-index induction
hypothesis. -/
theorem projMotiveBody_hasType_guarded {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : env.IsStructure S D T C) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    (hcl : D.ProjClosed T C) {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasType env U S D T C us k)
    {Γ ps : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (T.indices.length+1))
          ++ D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
              (bvars 1 T.indices.length) i))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  have hord := henv.ordered
  obtain ⟨hOnΔ1, uc, hctorTy⟩ := motiveCtx_wf hord hI H h3 h7 hΓ hps hpsA
  have hΔ : OnCtx
      (((VExpr.const T.name us).mkApp
          (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
        :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U) := ⟨hOnΔ1, uc, hctorTy⟩
  obtain ⟨Fs', es', hlenF, hlenE, hused, hunused, heq, hty, -⟩ :=
    C.swapData henv H hI h3 h7 hcl hi hΔ (ps.map (·.liftN (T.indices.length+1)))
      (D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
        (bvars 1 T.indices.length) i)
      (D.length_projArgs T C us ..)
  have hgetArgs : ∀ k, k < i →
      (D.projArgs T C us (ps.map (·.liftN (T.indices.length+1)))
        (bvars 1 T.indices.length) i).getD k default
      = D.projTerm T C us (ps.map (·.liftN (T.indices.length+1)))
          (bvars 1 T.indices.length) k (.bvar 0) := by
    intro k hk
    rw [D.projArgs_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk]
    rfl
  have hes' := projArgs_hasArgs_swapped hord hI H h3 h7 hcl hi hIH hΓ hps hpsA
    hlenF hlenE
    (fun k hk hu => ⟨(hused k hk hu).1, by rw [(hused k hk hu).2, hgetArgs k hk]⟩)
    hunused
  exact projMotiveBody_hasType_swapped hord hI H h3 h7 hcl hi hlvi hps hpsA hes' hty heq

/-- The `take`-form of `instAll_swap_eq`, which is what the `HasArgs`/`HasArgsDF` builders
need: at position `k` the spine already consumed is `ts.take k`, and the real spine there is
`(List.range k).map f`. -/
theorem VIndCtor.instAll_take_swap_eq (C : VIndCtor) (D : VInductDecl') (us : List VLevel)
    {k : Nat} (hk : k < C.fields.length) {ts qs : List VExpr} {f : Nat → VExpr}
    (hlen : k ≤ ts.length)
    (hagree : ∀ m, m < k → C.FieldUsed D 0 m → ts.getD m default = f m) :
    VExpr.instAll ((C.fields.getD k default).type.instL us)
        (qs ++ (List.range k).map f) 0
      = VExpr.instAll ((C.fields.getD k default).type.instL us) (qs ++ ts.take k) 0 := by
  refine C.instAll_swap_eq D us hk (by simp; omega) (by simp) ?_
  intro m hm hmu
  have hmk : m < k := by simpa using hm
  rw [show ((List.range k).map f).getD m default = f m from by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hmk]; rfl,
    show (ts.take k).getD m default = ts.getD m default from by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt hmk]]
  exact (hagree m hmk hmu).symm

end Lean4Lean
