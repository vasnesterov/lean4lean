import Lean4Lean.Verify.Typing.ProjWeakInv

/-!
# `TrProj.weak'_inv`: an **exact** (two-directional) residual, and the first `TrProj` witness

Round of 2026-09-03.  Scope: the two projection-existence holes,
`Lean4Lean.TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean:902`) and
`Lean4Lean.TypeChecker.Inner.inferProj.WF` (`Verify/TypeChecker/InferType.lean:468`).
`docs/handoff-projexistclose.md` carries the ledger; this file carries the statements.

Two things here are new relative to `ProjWeakInv.lean` / `ProjWeakInvSplit.lean`:

1. **§1: an equivalence.**  `docs/handoff-trproj-weakinv.md` §5.3 records "an exact
   (two-directional) split — not achieved", and warns that the split's two hypotheses "may be
   *jointly stronger* than the residual".  §1 closes that gap for the residual at the shape the
   hole actually has: `VEnv.ProjDataStrengthen` is **equivalent** to the `sorry`'s statement,
   `iff`, and the reduction is *hole-free* — it never calls `VEnv.HasArgs.of_mkApp`, so
   `rigidShapeUniqNS` and `forallE_inv_stratified` both leave the cone that
   `TrProj.weak'_inv_of_strengthen` (3661, three holes) carries.  The price of the equivalence is
   that the residual keeps the two `HasArgs` fields, which the `ConstAppTypeStrengthen` form
   discards and then re-derives; §1.4 states that trade precisely.

2. **§2: `TrProj` is inhabited.**  `inferProj.WF`'s docstring says the statement is "vacuously
   true today (`TrProj` has no inhabitants until the keystone lands)", and the same parenthesis
   is repeated in the projection docs.  **The parenthesis is false**, and §2 exhibits the
   witness: one `VInductDecl'.WF .empty` declaration, `structure Prj : Type where fld : Prop`,
   whose `addInduct'` succeeds by `rfl`, whose environment is `VEnv.WF` outright, and at which
   `TrProj` — all ten fields — holds with **no** hypotheses at all.  `TrProj.weak'` then fires
   the `weak'_inv` `sorry`'s own premise at a depth-one lift, so neither the hypothesis nor the
   conclusion of that hole is vacuous.  (Scope, stated up front: the inserted binder is
   inhabited, so this instance lies inside the region `constAppTypeStrengthen_inhab` already
   proves.  §2.5.)

Nothing here discharges a `sorry`; the census does not move.
-/

namespace Lean4Lean

open VExpr

/-! ## 1. The residual, exactly

`TrProj.mk` has ten fields.  Six of them — `hS`, the three lengths, `hi`, `hlv` and `hF17` —
mention no context at all, and two more (`hargs`, `hιargs`) plus the major-premise typing
`hty` are the only ones that live in `Γ`.  So `weak'_inv` *is* the strengthening of those three,
and the statement below says exactly that, with the block `(D, T, C)` and the levels `us`
existentially quantified in the conclusion because `TrProj`'s own conclusion quantifies them.

Quantifying the block is not a concession: `TrProj Γ S i e e''` never claims that `S` belongs
to one block (that is ledger G4, and `VEnv.IsStructure`'s docstring says leaving it out is the
point), so a residual that *fixed* the block would be strictly stronger than the hole and the
`iff` below would fail in the `→` direction.  Read positively: **`weak'_inv` neither needs nor
supplies block uniqueness.**
-/

/-- The `sorry`'s statement, ∀-quantified at a fixed `env` and `U` so that it can appear on
both sides of an `iff`.  `TrProj.weak'_inv`'s statement is `∀ env U, VEnv.WF env → …`, i.e.
`∀ env, env.WF → ∀ U, env.ProjStrengthen U` (`projStrengthen_iff_weak'_inv` below). -/
def VEnv.ProjStrengthen (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr},
    OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
    TrProj env U Γ' s i (e.lift' l) e' → ∃ e'', TrProj env U Γ s i e e''

/-- **The residual, at the shape the hole has.**  Every hypothesis is a field of `TrProj.mk`
read at `Γ'`, and every conclusion is the same field read at `Γ`. -/
def VEnv.ProjDataStrengthen (env : VEnv) (U : Nat) : Prop :=
  ∀ {l : Lift} {Γ Γ' : List VExpr} {S : Lean.Name} {D : VInductDecl'} {T : VIndType}
    {C : VIndCtor} {us : List VLevel} {ps ιs : List VExpr} {i : Nat} {e : VExpr},
    OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
    env.IsStructure S D T C →
    env.HasType U Γ' (e.lift' l) ((VExpr.const S us).mkApp (ps ++ ιs)) →
    us.length = D.uvars → ps.length = D.np → ιs.length = T.indices.length →
    i < C.fields.length → (∀ u ∈ us, u.WF U) →
    env.HasArgs U Γ' (D.params.map (VExpr.instL us)) ps →
    env.HasArgs U Γ' (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs →
    (D.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    ∃ (D' : VInductDecl') (T' : VIndType) (C' : VIndCtor) (us' : List VLevel) (ps' ιs' : List VExpr),
      env.IsStructure S D' T' C' ∧
      env.HasType U Γ e ((VExpr.const S us').mkApp (ps' ++ ιs')) ∧
      us'.length = D'.uvars ∧ ps'.length = D'.np ∧ ιs'.length = T'.indices.length ∧
      i < C'.fields.length ∧ (∀ u ∈ us', u.WF U) ∧
      env.HasArgs U Γ (D'.params.map (VExpr.instL us')) ps' ∧
      env.HasArgs U Γ (VExpr.instAllTele (T'.indices.map (VExpr.instL us')) ps') ιs' ∧
      (D'.isLE = true ∨ ∀ k, k ≤ i → (k = i ∨ C'.FieldUsed D' 0 k) →
        (C'.fields.getD k default).lvl.inst us' ≈ .zero)

variable {env : VEnv} {U : Nat}

/-- **The reduction.**  Nothing is re-derived: `TrProj.mk`'s fields go in, `TrProj.mk`'s
fields come out. -/
theorem VEnv.ProjDataStrengthen.projStrengthen (h : env.ProjDataStrengthen U) :
    env.ProjStrengthen U := by
  intro Γ Γ' l s i e e' hΓ' W H
  cases H with
  | mk hS hty hus hps hιs hi hlv hargs hιargs hF17 =>
    obtain ⟨D', T', C', us', ps', ιs', hS', hty', hus', hps', hιs', hi', hlv', hargs', hιargs',
      hF17'⟩ := h hΓ' W hS hty hus hps hιs hi hlv hargs hιargs hF17
    exact ⟨_, .mk hS' hty' hus' hps' hιs' hi' hlv' hargs' hιargs' hF17'⟩

/-- **The converse.**  The residual's hypotheses are exactly enough to *build* the `TrProj` the
hole consumes, so the hole implies the residual back.  This is what `ProjWeakInvSplit.lean` §5.3
did not have. -/
theorem VEnv.ProjStrengthen.projDataStrengthen (h : env.ProjStrengthen U) :
    env.ProjDataStrengthen U := by
  intro l Γ Γ' S D T C us ps ιs i e hΓ' W hS hty hus hps hιs hi hlv hargs hιargs hF17
  obtain ⟨e'', H⟩ := h hΓ' W (.mk hS hty hus hps hιs hi hlv hargs hιargs hF17)
  cases H with
  | mk hS' hty' hus' hps' hιs' hi' hlv' hargs' hιargs' hF17' =>
    exact ⟨_, _, _, _, _, _, hS', hty', hus', hps', hιs', hi', hlv', hargs', hιargs', hF17'⟩

/-- **§1's headline: the residual is the hole.** -/
theorem VEnv.projStrengthen_iff (env : VEnv) (U : Nat) :
    env.ProjStrengthen U ↔ env.ProjDataStrengthen U :=
  ⟨VEnv.ProjStrengthen.projDataStrengthen, VEnv.ProjDataStrengthen.projStrengthen⟩

/-- …and `ProjStrengthen` really is the `sorry`'s statement, not a paraphrase: this is
`TrProj.weak'_inv`'s type with the body replaced by the assumption. -/
theorem TrProj.weak'_inv_of_projStrengthen
    {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (h : env.ProjStrengthen U) (_henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.Lift' l Γ Γ') (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' := h hΓ' W H

/-- The same at the residual, so that the `iff` is usable at the `sorry` in one step. -/
theorem TrProj.weak'_inv_of_projDataStrengthen
    {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (h : env.ProjDataStrengthen U) (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.Lift' l Γ Γ') (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.weak'_inv_of_projStrengthen h.projStrengthen henv hΓ' W H

/-! ## 2. `TrProj` is inhabited — and so is `weak'_inv`'s premise

`inferProj.WF`'s docstring (`Verify/TypeChecker/InferType.lean:425`) says its statement is
"**vacuously true today** (`TrProj` has no inhabitants until the keystone lands)".  The
parenthetical is **false**, and the rest of this section is the witness.  (The *vacuity of
`inferProj.WF`* is a separate and correct claim: it rests on `TrEnv.not_inductInfo`, which is
about the `VContext`'s constant map, not about `TrProj`.  §2.6 keeps the two apart.)

The block is the smallest one that gets past F17: `TrProj.mk`'s last field asks for
`D.isLE = true` *or* every involved field to be a proof, and `fooDecl`
(`Theory/Inductive/DeclExamples.lean`) — the tree's only pre-existing structure-shaped
`VInductDecl'.WF` witness — satisfies **neither** (`isLE := false`, and its one field has
`lvl = .succ .zero ≉ .zero`).  So `TrProj` really has no derivation at `fooEnv`, which is
presumably how the "no inhabitants" reading arose.  One character of the declaration is
different here: the block is `Type`-valued rather than `Prop`-valued, which makes
`LECond`'s *first* disjunct (`D.lvl.IsNeverZero`) available and hence `isLE := true` legal. -/

/-- `structure Prj : Type where fld : Prop` — one non-`Prop` type, one constructor, one
non-recursive field, large-eliminating. -/
def prjDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  types := [{ name := `Prj, type := .sort (.succ .zero), indices := [],
              ctors := [{ name := `Prj.mk, params := [],
                          fields := [{ type := .sort .zero, lvl := .succ .zero,
                                       recArg := none }],
                          args := [] }] }]
  isLE := true

/-- `fooDecl_WF`'s proof, with `isLE` discharged through `LECond`'s first disjunct. -/
theorem prjDecl_WF : prjDecl.WF .empty where
  types_ne := by simp [prjDecl]
  params := trivial
  types := by
    intro T hT
    simp [prjDecl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp [prjDecl] at hT
      subst hT
      simp at hC
      subst hC
      have hc : env₁.constants `Prj = some ⟨0, VExpr.sort (.succ .zero)⟩ := by
        simp [VEnv.addIndTypes, VEnv.addConstList, VInductDecl'.typeConsts, prjDecl,
          VEnv.addConst, VEnv.empty] at he
        subst he; simp
      refine { params_len := rfl, params_eq := .zero, fields := ?_,
               args_len := rfl, args_fresh := by simp, args_ty := .nil,
               result := .constDF hc nofun nofun rfl .nil }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp at hF
        subst hF
        exact { hasType := .sortDF trivial trivial (.refl _)
                level := fun ls => by simp [VLevel.eval, prjDecl, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, .sortDF trivial trivial (.refl _)⟩ }
  isLE _ := .inl fun ls => by simp [prjDecl, VLevel.eval]

/-- …and `addInduct'` accepts it. -/
theorem prjEnv_eq : ∃ e, VEnv.empty.addInduct' prjDecl = some e := ⟨_, rfl⟩

noncomputable def prjEnv : VEnv := prjEnv_eq.choose

theorem prjEnv_spec : VEnv.empty.addInduct' prjDecl = some prjEnv := prjEnv_eq.choose_spec

/-- **The environment is `VEnv.WF` outright** — no keystone, no hypothesis.  This is
`fooHistory`'s (`Theory/Inductive/Nested.lean`) argument at `prjDecl`. -/
theorem prjEnv_WF : VEnv.WF prjEnv :=
  ⟨_, .decl (.induct prjDecl_WF prjEnv_spec) .empty⟩

theorem prjEnv_ordered : VEnv.Ordered prjEnv := prjEnv_WF.ordered

abbrev prjTy : VIndType := prjDecl.types[0]!
abbrev prjCtor : VIndCtor := prjTy.ctors[0]!

theorem prjEnv_isStructure : prjEnv.IsStructure `Prj prjDecl prjTy prjCtor where
  types := rfl
  name := rfl
  ctors := rfl
  noRec := rfl
  decl := ⟨.empty, prjEnv, prjDecl_WF, prjEnv_spec, VEnv.LE.rfl⟩

theorem prjEnv_constants : prjEnv.constants `Prj = some ⟨0, .sort (.succ .zero)⟩ := by
  have h := prjEnv_spec
  rw [VEnv.addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, h2⟩ := h
  rw [← h2, VEnv.addIndRules_constants]
  exact VEnv.addConstList_constants h1 (`Prj, ⟨0, .sort (.succ .zero)⟩)
    (by simp [VInductDecl'.allConsts, VInductDecl'.typeConsts, prjDecl])

/-- The structure's own type, as a type of the empty context. -/
theorem prjEnv_isType_nil : prjEnv.IsType 0 [] (.const `Prj []) :=
  ⟨_, .constDF prjEnv_constants nofun nofun rfl .nil⟩

/-- One binder, of type `Prj`. -/
abbrev prjCtx : List VExpr := [.const `Prj []]

theorem prjEnv_onCtx : OnCtx prjCtx (prjEnv.IsType 0) := ⟨trivial, prjEnv_isType_nil⟩

/-- **The first `TrProj` derivation in the tree, at no hypotheses at all.**  Ten fields, at a
`VEnv.WF` environment (`prjEnv_WF`), with the projected field `0` of a one-field
large-eliminating structure. -/
theorem prjEnv_trProj :
    TrProj prjEnv 0 prjCtx `Prj 0 (.bvar 0)
      (prjDecl.projTerm prjTy prjCtor [] [] [] 0 (.bvar 0)) := by
  refine .mk prjEnv_isStructure ?_ rfl rfl rfl (by simp [prjDecl]) (by simp) ?_ ?_ (.inl rfl)
  · simpa using VEnv.HasType.bvar (Γ := prjCtx) (A := .const `Prj []) .zero
  · simpa [prjDecl] using VEnv.HasArgs.nil (env := prjEnv) (U := 0) (Γ := prjCtx)
  · simpa [prjDecl] using VEnv.HasArgs.nil (env := prjEnv) (U := 0) (Γ := prjCtx)

/-! ### 2.5 The `sorry`'s own premises fire, and so does its conclusion

`TrProj.weak'` lifts the witness across a depth-one insertion, which produces exactly the shape
`TrProj.weak'_inv` consumes (`TrProj env U Γ' s i (e.lift' l) e'`), at
`henv := prjEnv_WF` and `hΓ' := prjEnv_onCtx'`.  So the hole is **not** vacuous in the
hypothesis direction — and its conclusion holds at the same instance, so it is not vacuous in
the conclusion direction either.

**Scope, stated rather than implied.**  The inserted binder is `Prop`, which is *inhabited*, so
this instance falls inside the region `constAppTypeStrengthen_inhab` (`ProjWeakInv.lean:387`)
already proves outright; it witnesses satisfiability and **nothing** about the obstruction, which
`ProjInhab.lean` §1 pins to the existence of an uninhabited type, i.e. to `env.Consistent`.  An
*uninhabited* binder over `prjEnv` would need `prjEnv.Consistent`, which is not proved here or
anywhere (`uninhabited_binder_of_consistent` takes it as a hypothesis). -/

abbrev prjCtx' : List VExpr := .sort .zero :: prjCtx

theorem prjEnv_onCtx' : OnCtx prjCtx' (prjEnv.IsType 0) :=
  ⟨prjEnv_onCtx, _, .sortDF trivial trivial (.refl _)⟩

theorem prjEnv_lift : Ctx.Lift' (.skip .refl) prjCtx prjCtx' := .skip .refl

/-- The premise of `TrProj.weak'_inv`, at a genuine depth-one lift. -/
theorem prjEnv_trProj_lifted :
    TrProj prjEnv 0 prjCtx' `Prj 0 ((VExpr.bvar 0).lift' (.skip .refl))
      ((prjDecl.projTerm prjTy prjCtor [] [] [] 0 (.bvar 0)).lift' (.skip .refl)) :=
  prjEnv_trProj.weak' prjEnv_ordered prjEnv_lift

/-- **`TrProj.weak'_inv` is not vacuous, in either direction.**  Every hypothesis of the `sorry`
is satisfied simultaneously, and at that instance its conclusion holds too. -/
theorem trProj_weak'_inv_fires :
    ∃ (env : VEnv) (U : Nat) (Γ Γ' : List VExpr) (l : Lift) (s : Lean.Name) (i : Nat)
      (e e' : VExpr),
      VEnv.WF env ∧ OnCtx Γ' (env.IsType U) ∧ Ctx.Lift' l Γ Γ' ∧
      TrProj env U Γ' s i (e.lift' l) e' ∧ ∃ e'', TrProj env U Γ s i e e'' :=
  ⟨prjEnv, 0, prjCtx, prjCtx', .skip .refl, `Prj, 0, .bvar 0, _,
    prjEnv_WF, prjEnv_onCtx', prjEnv_lift, prjEnv_trProj_lifted, _, prjEnv_trProj⟩

/-- …and therefore the residual of §1 is not vacuous either: `ProjDataStrengthen`'s hypotheses
are satisfiable at the same instance, with the block `prjDecl` and empty spines. -/
theorem projDataStrengthen_fires :
    ∃ (env : VEnv) (U : Nat), VEnv.WF env ∧
      ∃ (l : Lift) (Γ Γ' : List VExpr) (S : Lean.Name) (D : VInductDecl') (T : VIndType)
        (C : VIndCtor) (us : List VLevel) (ps ιs : List VExpr) (i : Nat) (e : VExpr),
        OnCtx Γ' (env.IsType U) ∧ Ctx.Lift' l Γ Γ' ∧ env.IsStructure S D T C ∧
        env.HasType U Γ' (e.lift' l) ((VExpr.const S us).mkApp (ps ++ ιs)) ∧
        us.length = D.uvars ∧ ps.length = D.np ∧ ιs.length = T.indices.length ∧
        i < C.fields.length ∧ (∀ u ∈ us, u.WF U) ∧
        env.HasArgs U Γ' (D.params.map (VExpr.instL us)) ps ∧
        env.HasArgs U Γ' (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) ιs := by
  refine ⟨prjEnv, 0, prjEnv_WF, .skip .refl, prjCtx, prjCtx', `Prj, prjDecl, prjTy, prjCtor,
    [], [], [], 0, .bvar 0, prjEnv_onCtx', prjEnv_lift, prjEnv_isStructure, ?_, rfl, rfl, rfl,
    (by simp [prjDecl]), (by simp), ?_, ?_⟩
  · simpa using VEnv.HasType.bvar (Γ := prjCtx') (A := VExpr.const `Prj []) (.succ .zero)
  · exact (by simpa [prjDecl] using VEnv.HasArgs.nil (env := prjEnv) (U := 0) (Γ := prjCtx'))
  · exact (by simpa [prjDecl] using VEnv.HasArgs.nil (env := prjEnv) (U := 0) (Γ := prjCtx'))

/-! ### 2.6 What this does *not* say about `inferProj.WF`

`inferProj.WF`'s vacuity is unaffected: it comes from `TrEnv.not_inductInfo`
(`Verify/TypeChecker/Reduce.lean`), which forbids a **translated** environment's constant map
from holding an `.inductInfo`, and `prjEnv` is a bare `VEnv` with no `TrEnv` over it.  What §2
does contradict is the *reason* the docstring gives, and the same parenthetical wherever it is
repeated: `TrProj` has inhabitants **now**, at a `VEnv.WF` environment, with no keystone.  The
two `IsStructure` fields `inferProj` fails to check (`types`, `noRec`, `bugs-found.md` item 10)
are untouched by this — `prjDecl` satisfies both, which is *why* the witness exists. -/

/-! ## 3. Where the new residual sits relative to the old one

The `iff` of §1 would be worthless if `ProjDataStrengthen` were *stronger* than the residual all
the existing bounds are stated against (`ProjWeakInv.lean`, `ProjInhab.lean`,
`ProjWeakInvSplit.lean`).  It is not: `VEnv.ConstAppTypeStrengthen` implies it, by composing the
old reduction with §1's converse.  So every upper bound already proved for the old residual —
depth zero (`constAppTypeStrengthen_depth_zero`), inhabited lifts at every depth
(`constAppTypeStrengthen_inhab`), `AllTypesInhabited`
(`VEnv.AllTypesInhabited.constAppTypeStrengthen`), one uninhabited binder
(`constAppTypeStrengthen_of_skipUninhab`), and the `TypingStrengthening + ConstAppDefeqStrengthen`
split — bounds `ProjDataStrengthen` too, at the price of `VEnv.WF env`.

This one declaration is `sorryAx`-tainted, and deliberately: it inherits
`{weakN_iff, forallE_inv_stratified, rigidShapeUniqNS}` from `TrProj.weak'_inv_of_strengthen`,
which is the whole point — the *taint is in the old reduction*, not in the residual, and §1's
route to the `sorry` avoids it entirely. -/
theorem VEnv.ConstAppTypeStrengthen.projDataStrengthen (henv : VEnv.WF env)
    (hst : env.ConstAppTypeStrengthen U) : env.ProjDataStrengthen U :=
  VEnv.ProjStrengthen.projDataStrengthen
    (fun hΓ' W H => TrProj.weak'_inv_of_strengthen henv hst hΓ' W H)

end Lean4Lean
