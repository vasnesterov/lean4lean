import Lean4Lean.Verify.Inductive.B6

/-!
# `VIndField.WF.pos`'s `some` branch: what its residual clause really demands, and where it is free

**Read the first three paragraphs before pricing anything in this file.**  The brief this file was
written to said that `VIndField.WF.pos`'s `some` branch is "the last consumer of the populated
`recArg` that nobody has discharged", and that discharging it at the real nested block was the
deliverable.  That is **false**, and `docs/handoff-wfpos.md` §2 records how it was found false on
the third tool call of the round rather than after a day of re-derivation:

* `Theory/Inductive/DeclExamples.lean` holds three complete `VInductDecl'.WF .empty` witnesses
  whose constructors have recursive fields — `accDecl_WF`, `mutDecl_WF`, `wDecl_WF` — so the nine
  conjuncts of the `some` branch have been discharged since those landed;
* and `Theory/Inductive/NestedHead.lean`:943 holds **`InductiveDeclExamples.ntreeAux_WF' :
  ntreeAux.WF env₁`**, at an *arbitrary* environment, with 32 application sites in 14 files.  So
  `VInductDecl'.WF` at the real nested block is not a target, it is a *lemma other people already
  use*.

What is genuinely missing is one level down, and `scripts/shape.lean` on the conclusion head
`VInductDecl'.ResidualClean` is what shows it: the entire population that concludes the residual
clause is the two trivial producers in `Decl.lean`, the `decide` instance, `WF.pos` itself, and two
*witnesses*.  **Every existing firing of the `some` branch discharges conjunct 9 by `by decide` at
a closed block, and nothing says why it holds.**  Line 241 of `Decl.lean` states the clause's
purpose in prose — "constrains the residual of a *stored* uniform occurrence" — and this file turns
that prose into two theorems and reports their exact limit.

## What is here

* **§1 the core, and it is unconditional** (migrated 2026-09-04 to `Theory/Inductive/Decl.lean`
  so that `Theory/`-side witnesses can cite it; §1 below records the move).
  `VInductDecl'.residualClean_canonType`: at the
  *canonical* form `r.canonType D i`, F7's residual clause follows from `pos`'s own conjunct 4
  (`∀ a ∈ r.args, D.NoBlock a`) — **no environment, no typing, no `Ordered`, no block hypothesis at
  all.**  Two cases and they are the whole content of the clause: with `r.binders = []` the trigger
  fires and the residual it reports *is* `r.args` (whatever member index it decides to report —
  the residual is `spineArgs.drop D.np`, which does not depend on the reported index, so the
  theorem needs nothing about `memberIdx` and survives duplicate member names); with
  `r.binders ≠ []` the canonical form is `.forallE`-headed, `spineFn` is not a `.const`, and the
  trigger cannot fire at all.  §1.1 lifts it to a field (`residualClean_of_canon`), to a
  constructor (`VIndCtor.residualClean_of_canonical`) and to a block
  (`VInductDecl'.residualClean_of_canonical`), so **at a canonical block conjunct 9 of
  `VIndField.WF.pos` is redundant: it is implied by conjunct 4, which is already there.**
* **§2 the reader route, which is the one on the critical path.**  The refinement does not hand a
  spec-writer a canonical field; it hands the answer of `VInductDecl'.recArgOf`, B6's two-stage
  reader.  `residualClean_of_recog` and `residualClean_of_recArgOf` say that **on the whole range
  of the reader, conjunct 9 is again implied by conjunct 4** — for `recog` because `recog_sound`
  makes its answer canonical (`canonTypeR_id` at the identity restoration), and for the two-stage
  `recArgOf` because a firing trigger forces `spineFn` to be a `.const`, so the head β step of
  stage 2 is the identity there (`betaHead_eq_self_of_spineFn_const`, the sharpening of B6 §1's
  `betaHead_eq_self_of_noLam` that this needs: `noLam` of the *whole* term is far more than a
  non-`.lam` head).
* **§3 the split, named.**  `VIndField.PosSyn` (conjuncts 1-4 and 9, pure syntax, `Decidable`) and
  `VIndField.PosTy` (conjuncts 5-8, the typing in the staged environment), `posSome_iff` that the
  two together are exactly `pos`'s `some` branch, and `posSyn_of_recArgOf` — **the reader plus a
  three-part decidable check gives all five syntactic conjuncts**, because conjunct 1 comes from
  `recArgOf_idx_lt` and conjunct 9 from §2.  That is the composition `addDecl.WF`'s `inductDecl`
  branch needs and it did not exist.
* **§4 the firing, at the real nested block and through the reader.**  `ntreeAux`'s three recursive
  fields, with conjunct 9 supplied by §1/§2 instead of by `decide`, `recArg` supplied by the reader
  (B6 §4's `recArgOf_surfHeader`/`recArg_surfInductDeclR?` and `ntreeAux_node_field1_recArg`), and
  a complete `VIndField.PosSyn` for each.  Then `ntreeNode_field1_posSome`, a full `some` branch at
  the block, whose conjunct 9 is an instance of §1 and whose conjunct 1 is an instance of the
  reader — and `ntreeAux_WF'`'s own `pos` is *not* used to build it (§5).
* **§5 the limits, stated and where possible proved.**  The canonicity hypothesis of §1 **cannot be
  dropped**: `MRedex.TQWit.tqHostile` (`Theory/Inductive/IndexedNested.lean` §8) is a stored field
  type satisfying conjuncts 1-8 at which conjunct 9 is false, so conjunct 9 is *independent* of the
  first eight and §1 is exactly as strong as it can be.  `IndexedNested` is **deliberately not
  imported** (see below), so that citation is prose here and a measurement in the handoff.  And the
  firing's own honest limit: `ntreeAux` has no indices, so every `r.args = []` and the trigger
  fires with an **empty** residual — the trigger is exercised (which `.forallE`-headed `accIntro`
  never does) but the scan has nothing to scan.

## Structural exclusions

This file imports **exactly one** module, `Lean4Lean.Verify.Inductive.B6`.  Two modules that hold a
hand-built instance of what §1 concludes are *not* in the closure and are named so the exclusion is
checkable rather than asserted: `Theory.Inductive.IndexedNested`
(`MRedex.TQWit.tq_hostile_not_residualClean`, the refutation) and `Theory.Inductive.NestedFresh`
(`InductiveDeclExamples.ntreeAux_residualClean_badSpine`, a negative witness).  Neither is imported
and neither is cited by any proof term here.

`Theory.Inductive.NestedHead` **is** in the closure and cannot be excluded — it declares `ntreeAux`,
`ntreeRestore`, `canonTypeR_id`, `tyAppR_id` and `ntreeAux_Canonical`, all of which §1/§4 are
statements *about*.  It also holds `ntreeAux_WF'`, whose `pos` fields discharge conjunct 9 by
`decide`.  So the exclusion that matters is measured rather than structural: `docs/handoff-wfpos.md`
§2 reports `scripts/exists.lean` with `ntreeAux_WF'` **watched**, and no declaration in this file
has it in its cone.
-/

set_option autoImplicit false

namespace Lean4Lean

open VExpr (mkPi mkLams mkApp bvars liftTele shift)

/-! ## §1 The core: at the canonical form, F7's residual clause is conjunct 4

`VIndField.WF.pos`'s `some` branch has nine conjuncts.  Numbering them as they are written in
`Theory/Inductive/Decl.lean`:

1. `r.idx < D.nm`
2. `r.args.length = (D.types.getD r.idx default).indices.length`
3. `∀ B ∈ r.binders, D.NoBlock B`
4. `∀ a ∈ r.args, D.NoBlock a`
5. `OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars)`
6. `env.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl)`
7. the `HasArgs` derivation for the index arguments
8. `env.IsDefEqType D.uvars Γ F.type (r.canonType D i)`
9. `D.ResidualClean (r.binders.length + i) F.type`

1-4 and 9 are pure syntax; 5-8 are typing in the staged environment.  This section is about 9, and
its content is that **9 is not independent information once the stored type is the canonical one**.

**These three declarations no longer live here.**  `VInductDecl'.spineArgs_drop_tyApp`,
`VInductDecl'.uniformOcc?_canonResult_snd` and `VInductDecl'.residualClean_canonType` were migrated
to `Theory/Inductive/Decl.lean` (§ "Canonical residuals", after `VIndCtor.recFields`) on 2026-09-04,
verbatim and with no proof change -- see `docs/handoff-migrate2.md`.  They mention nothing outside
`Decl.lean`, and `scripts/can-cite.py` showed that `Theory.Inductive.NestedHead` (closure 50) and
`Theory.Inductive.DeclExamples` (closure 30) -- which hold the `WF` witnesses that discharge conjunct
9 by `by decide` -- could not cite them while they sat in `Verify/`.  Everything below cites them from
their new home; nothing here changed but the address. -/

/-! ### §1.1 Lifted to a field, a constructor and a block

`VIndCtor.Canonical` (`Theory/Inductive/Restore.lean`:586) is exactly the hypothesis §1 needs, field
by field: `∀ i F r, C.fields[i]? = some F → F.recArg = some r → F.type = r.canonType D i`.  So the
conclusion of this subsection is the sentence **"at a canonical block, `VIndField.WF.pos`'s conjunct
9 is redundant"**, and `InductiveDeclExamples.ntreeAux_Canonical` says the real nested block is one.

A caution that belongs here rather than in a handoff: `Canonical` is *not* a property of every block
Lean accepts.  `CGMAbstract.cgm_not_canonical` (`Verify/Inductive/CanonGapMeasure.lean`) machine-checks
that `ElimNestedInductive.run` manufactures a non-canonical recursive field whenever a block nests
through an inductive with a dependent parameter, and `Lean.Json` and `Lean.PrefixTreeNode` both do.
§2 is what covers those: they are still inside the *reader's* range. -/

/-- Conjunct 9 at a canonical field. -/
theorem VIndField.residualClean_of_canon {D : VInductDecl'} {i : Nat} {F : VIndField}
    {r : VIndRecArg} (hcanon : F.type = r.canonType D i) (hargs : ∀ a ∈ r.args, D.NoBlock a) :
    D.ResidualClean (r.binders.length + i) F.type :=
  hcanon ▸ VInductDecl'.residualClean_canonType hargs

/-- Conjunct 9 for every recursive field of a canonical constructor, from conjunct 4. -/
theorem VIndCtor.residualClean_of_canonical {D : VInductDecl'} {C : VIndCtor}
    (hC : C.Canonical D) {i : Nat} {F : VIndField} {r : VIndRecArg}
    (hF : C.fields[i]? = some F) (hr : F.recArg = some r)
    (hargs : ∀ a ∈ r.args, D.NoBlock a) :
    D.ResidualClean (r.binders.length + i) F.type :=
  VIndField.residualClean_of_canon (hC i F r hF hr) hargs

/-- …and at the block. -/
theorem VInductDecl'.residualClean_of_canonical {D : VInductDecl'} (hD : D.Canonical)
    {j : Nat} {C : VIndCtor} (hC : (j, C) ∈ D.ctorsAll) {i : Nat} {F : VIndField}
    {r : VIndRecArg} (hF : C.fields[i]? = some F) (hr : F.recArg = some r)
    (hargs : ∀ a ∈ r.args, D.NoBlock a) :
    D.ResidualClean (r.binders.length + i) F.type :=
  VIndCtor.residualClean_of_canonical (hD j C hC) hF hr hargs

/-! ## §2 The reader route: conjunct 9 is free on the whole range of B6's two-stage reader

§1 needs the stored type to *be* the canonical form.  The refinement does not deliver that — it
delivers the answer of `VInductDecl'.recArgOf`, and `Verify/Inductive/CanonGapMeasure.lean` shows
real blocks whose stored field type is a β-redex.  This section is the version that applies there.

The mechanism is one observation: **`uniformOcc?` can only fire on a `.const`-headed spine**, because
its outer `match` is on `e.spineFn` and every arm but `.const` returns `none`.  So at a firing
trigger the head β step of the reader's second stage is the identity, and stage 2's answer restores
to the stored type on the nose exactly where the clause has anything to say.  B6 §1's
`betaHead_eq_self_of_noLam` is too strong for this — it asks `noLam` of the *whole* term, and a
stored field type may well contain a `.lam` deep inside an argument (`tqAuxNodeB`'s does). -/

namespace VExpr

/-- **The head β step is the identity on a `.const`-headed spine.**  Weaker hypothesis than
`betaHead_eq_self_of_noLam` (B6 §1), which asks `.lam`-freeness of every subterm; here only the
spine head is constrained, which is all a firing trigger gives. -/
theorem betaHead_eq_self_of_spineFn_const {e : VExpr} {c : Name} {ls : List VLevel}
    (h : e.spineFn = .const c ls) : betaHead e = e := by
  rw [betaHead, betaSpine_eq_mkApp _ (by rw [h]; exact fun _ _ => nofun),
    mkApp_spineFn_spineArgs]

end VExpr

/-- The trigger only fires on a `.const`-headed spine. -/
theorem VInductDecl'.spineFn_const_of_uniformOcc? {D : VInductDecl'} {k : Nat} {e : VExpr}
    {j : Nat} {rest : List VExpr} (h : D.uniformOcc? k e = some (j, rest)) :
    ∃ c ls, e.spineFn = .const c ls := by
  rw [uniformOcc?] at h
  split at h
  · exact ⟨_, _, by assumption⟩
  · exact absurd h nofun

/-- **Conjunct 9 from the single-stage recogniser.**  `VIndRestore.recog_sound` says the recogniser's
answer restores to what it was given, and at the identity restoration `canonTypeR` *is* `canonType`
(`VIndRecArg.canonTypeR_id`), so the stored type is canonical by construction — §1 then applies. -/
theorem VInductDecl'.residualClean_of_recog {D : VInductDecl'} {i : Nat} {S : VExpr}
    {r : VIndRecArg} (h : D.idRestore.recog D.nm i S = some r)
    (hargs : ∀ a ∈ r.args, D.NoBlock a) :
    D.ResidualClean (r.binders.length + i) S := by
  have hc : r.canonType D i = S := (r.canonTypeR_id D i).symm.trans (VIndRestore.recog_sound h D)
  exact hc ▸ residualClean_canonType hargs

/-- **Conjunct 9 from the two-stage reader — the statement on the critical path.**

`VInductDecl'.recArgOf` is what B6 populates `recArg` with, and its second stage runs `recog` on
`VExpr.betaHead S`, so its answer is canonical only up to one head β step.  That is enough: where
the residual clause says anything at all the trigger has fired, and a firing trigger forces `S` to be
`.const`-headed, so `betaHead S = S` there.  Hence **on the entire range of the reader, F7's residual
clause is implied by `pos`'s conjunct 4** — the reader contributes no failure mode of its own, and
the only thing that can go wrong is a residual argument that mentions the block, which is exactly
what `isValidIndAppIdx` scans for. -/
theorem VInductDecl'.residualClean_of_recArgOf {D : VInductDecl'} {i : Nat} {S : VExpr}
    {r : VIndRecArg} (h : D.recArgOf i S = some r) (hargs : ∀ a ∈ r.args, D.NoBlock a) :
    D.ResidualClean (r.binders.length + i) S := by
  intro j rest hocc
  obtain ⟨c, ls, hsp⟩ := spineFn_const_of_uniformOcc? hocc
  have hbeta : VExpr.betaHead S = S := VExpr.betaHead_eq_self_of_spineFn_const hsp
  have hc : r.canonType D i = S := by
    have := recArgOf_sound h
    rw [r.canonTypeR_id D i] at this
    exact this.elim id fun h' => h'.trans hbeta
  exact residualClean_canonType hargs j rest (hc ▸ hocc)

/-! ## §3 The split, named: `PosSyn` (decidable) and `PosTy` (the typing)

`VIndField.WF.pos` is a `match` on `F.recArg`, so its `some` branch has no name and cannot be talked
about.  This section gives it one, splits it where the round's evidence says it splits, and proves the
two halves reassemble into exactly the structure field — so a producer can be written against the
named halves and handed to `VIndField.WF.mk` unchanged. -/

namespace VIndField

/-- **The syntactic half of `pos`'s `some` branch**: conjuncts 1-4 and 9.  No `VEnv` occurs, so this
is a closed computation at a concrete block, and `Decidable` below is what makes that a `decide`. -/
structure PosSyn (D : VInductDecl') (i : Nat) (F : VIndField) (r : VIndRecArg) : Prop where
  idx_lt : r.idx < D.nm
  args_len : r.args.length = (D.types.getD r.idx default).indices.length
  binders_noBlock : ∀ B ∈ r.binders, D.NoBlock B
  args_noBlock : ∀ a ∈ r.args, D.NoBlock a
  residual : D.ResidualClean (r.binders.length + i) F.type

/-- **The typing half**: conjuncts 5-8, all four of them relative to `Γ` or to `ξ.reverse ++ Γ`. -/
structure PosTy (env : VEnv) (D : VInductDecl') (Γ : List VExpr) (i : Nat) (F : VIndField)
    (r : VIndRecArg) : Prop where
  onCtx : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars)
  canonResult : env.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl)
  indexArgs : ∀ T', D.types[r.idx]? = some T' →
    env.HasArgs D.uvars (r.binders.reverse ++ Γ)
      (liftTele (r.binders.length + i) T'.indices) r.args
  defeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i)

/-- **The two halves are exactly the field.**  Stated as a producer for `VIndField.WF.mk`'s `pos`
argument rather than as an `Iff`, because that argument's type is a `match` on `F.recArg` and only
becomes a proposition once `F.recArg` is known. -/
theorem posSome_of_split {env : VEnv} {D : VInductDecl'} {Γ : List VExpr} {i : Nat}
    {F : VIndField} {r : VIndRecArg} (hr : F.recArg = some r)
    (hsyn : PosSyn D i F r) (hty : PosTy env D Γ i F r) :
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
          (liftTele (r.binders.length + i) T'.indices) r.args) ∧
      env.IsDefEqType D.uvars Γ F.type (r.canonType D i) ∧
      D.ResidualClean (r.binders.length + i) F.type := by
  rw [hr]
  exact ⟨hsyn.idx_lt, hsyn.args_len, hsyn.binders_noBlock, hsyn.args_noBlock, hty.onCtx,
    hty.canonResult, hty.indexArgs, hty.defeq, hsyn.residual⟩

/-- …and the converse projection, so a consumer holding a `VIndField.WF` can name the halves. -/
theorem WF.posSyn {env : VEnv} {D : VInductDecl'} {pre : List VIndField} {Γ : List VExpr}
    {i : Nat} {F : VIndField} (h : F.WF env D pre Γ i) {r : VIndRecArg} (hr : F.recArg = some r) :
    PosSyn D i F r := by
  have := h.pos
  rw [hr] at this
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.2.2.2.2⟩

theorem WF.posTy {env : VEnv} {D : VInductDecl'} {pre : List VIndField} {Γ : List VExpr}
    {i : Nat} {F : VIndField} (h : F.WF env D pre Γ i) {r : VIndRecArg} (hr : F.recArg = some r) :
    PosTy env D Γ i F r := by
  have := h.pos
  rw [hr] at this
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.1⟩

/-- **The syntactic half is a decision.**  Every conjunct is: `Nat` comparison, list length,
`decidableNoBlock` entrywise, and `decidableResidualClean`. -/
instance decidablePosSyn (D : VInductDecl') (i : Nat) (F : VIndField) (r : VIndRecArg) :
    Decidable (PosSyn D i F r) :=
  decidable_of_iff
    (r.idx < D.nm ∧ r.args.length = (D.types.getD r.idx default).indices.length ∧
      (∀ B ∈ r.binders, D.NoBlock B) ∧ (∀ a ∈ r.args, D.NoBlock a) ∧
      D.ResidualClean (r.binders.length + i) F.type)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

/-! ### §3.1 The reader supplies two of the five syntactic conjuncts

This is the composition `addDecl.WF`'s `inductDecl` branch needs and it did not exist: given that the
*reader* produced `r` from the stored type, conjuncts **1** (`recArgOf_idx_lt`) and **9** (§2) come
for free, and what is left is a three-part decidable check — the index-arity equation, and the two
`NoBlock` scans that are the abstract form of `checkPositivity`'s `hasIndOcc` calls and
`isValidIndAppIdx`'s residual scan. -/

/-- **The reader plus one three-part decidable check gives all five syntactic conjuncts.** -/
theorem posSyn_of_recArgOf {D : VInductDecl'} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (h : D.recArgOf i F.type = some r)
    (hlen : r.args.length = (D.types.getD r.idx default).indices.length)
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hargs : ∀ a ∈ r.args, D.NoBlock a) :
    PosSyn D i F r where
  idx_lt := recArgOf_idx_lt h
  args_len := hlen
  binders_noBlock := hbind
  args_noBlock := hargs
  residual := D.residualClean_of_recArgOf h hargs

/-- The same at a canonical field, where the reader is not needed at all — conjunct 1 has to be
supplied, and conjunct 9 still comes from conjunct 4. -/
theorem posSyn_of_canon {D : VInductDecl'} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (hcanon : F.type = r.canonType D i) (hidx : r.idx < D.nm)
    (hlen : r.args.length = (D.types.getD r.idx default).indices.length)
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hargs : ∀ a ∈ r.args, D.NoBlock a) :
    PosSyn D i F r where
  idx_lt := hidx
  args_len := hlen
  binders_noBlock := hbind
  args_noBlock := hargs
  residual := residualClean_of_canon hcanon hargs

end VIndField

/-! ## §4 The firing, at the real nested block, through the reader

`InductiveDeclExamples.ntreeAux` is the block `ElimNestedInductive.run` produces for
`inductive NTree (α) | node : α → List (NTree α) → NTree α`: two members, `NTree` and the auxiliary
`_nested.List_1`, three constructors, **three** recursive fields between them — including
`_nested.List_1.cons`'s *first* field, which is recursive only because instantiating at `NTree α`
turned `List`'s parameter position into one.  That is the configuration nested induction exists for.

Everything below is anchored on the block's own field records (`types.getD … ctors.getD … fields.getD`)
rather than on re-typed literals, so it cannot drift if `ntreeAux` is edited.

**What is new here and what is not.**  `ntreeAux_WF'` (`NestedHead.lean`:943) already proves the whole
of `VInductDecl'.WF` at this block, conjunct 9 included, by `by decide` three times.  What is new is
that conjunct 9 now arrives as an *instance of §1/§2* — from the reader's answer and the block's
canonicity — so the same fact holds at any block the reader populates, and the `decide`s were not
carrying information.  No proof term below mentions `ntreeAux_WF'`. -/

namespace InductiveDeclExamples

/-- The three recursive fields of the block, read off the reader B6 populates `recArg` with.
`rfl`, so this is the reader *computing*, not a statement about it. -/
theorem ntreeAux_node_field1_recArgOf :
    ntreeAux.recArgOf 1
        (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default).type
      = some { binders := [], idx := 1, args := [] } := rfl

theorem ntreeAux_cons_field0_recArgOf :
    ntreeAux.recArgOf 0
        (((ntreeAux.types.getD 1 default).ctors.getD 1 default).fields.getD 0 default).type
      = some { binders := [], idx := 0, args := [] } := rfl

theorem ntreeAux_cons_field1_recArgOf :
    ntreeAux.recArgOf 1
        (((ntreeAux.types.getD 1 default).ctors.getD 1 default).fields.getD 1 default).type
      = some { binders := [], idx := 1, args := [] } := rfl

/-- …and each agrees with the datum the block stores — B6's `ntreeAux_node_field1_recArg` is the
first of the three, stated there as a `rfl` about `recArg` alone. -/
theorem ntreeAux_recArgOf_eq_stored :
    ntreeAux.recArgOf 1
        (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default).type
      = (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default).recArg ∧
    ntreeAux.recArgOf 0
        (((ntreeAux.types.getD 1 default).ctors.getD 1 default).fields.getD 0 default).type
      = (((ntreeAux.types.getD 1 default).ctors.getD 1 default).fields.getD 0 default).recArg ∧
    ntreeAux.recArgOf 1
        (((ntreeAux.types.getD 1 default).ctors.getD 1 default).fields.getD 1 default).type
      = (((ntreeAux.types.getD 1 default).ctors.getD 1 default).fields.getD 1 default).recArg :=
  ⟨rfl, rfl, rfl⟩

/-! ### §4.1 `PosSyn` at all three, from the reader — no `decide` on the residual clause -/

theorem ntreeNode_field1_posSyn :
    VIndField.PosSyn ntreeAux 1
      (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default)
      { binders := [], idx := 1, args := [] } :=
  VIndField.posSyn_of_recArgOf ntreeAux_node_field1_recArgOf rfl nofun nofun

theorem nlistCons_field0_posSyn :
    VIndField.PosSyn ntreeAux 0
      (((ntreeAux.types.getD 1 default).ctors.getD 1 default).fields.getD 0 default)
      { binders := [], idx := 0, args := [] } :=
  VIndField.posSyn_of_recArgOf ntreeAux_cons_field0_recArgOf rfl nofun nofun

theorem nlistCons_field1_posSyn :
    VIndField.PosSyn ntreeAux 1
      (((ntreeAux.types.getD 1 default).ctors.getD 1 default).fields.getD 1 default)
      { binders := [], idx := 1, args := [] } :=
  VIndField.posSyn_of_recArgOf ntreeAux_cons_field1_recArgOf rfl nofun nofun

/-- **The same three, by the canonicity route instead of the reader route** — `ntreeAux_Canonical`
plus conjunct 4.  Two independent derivations of the same five conjuncts, which is what says §1 and
§2 are consistent at the block rather than two unrelated arguments. -/
theorem ntreeAux_residualClean_of_canonical {j : Nat} {C : VIndCtor}
    (hC : (j, C) ∈ ntreeAux.ctorsAll) {i : Nat} {F : VIndField} {r : VIndRecArg}
    (hF : C.fields[i]? = some F) (hr : F.recArg = some r)
    (hargs : ∀ a ∈ r.args, ntreeAux.NoBlock a) :
    ntreeAux.ResidualClean (r.binders.length + i) F.type :=
  VInductDecl'.residualClean_of_canonical ntreeAux_Canonical hC hF hr hargs

/-! ### §4.2 …and a complete `some` branch at the block, typing included

The typing half is built here rather than taken from `ntreeAux_WF'`, so that the assembled `pos` is
this file's and the exclusion in the header is real.  It is `ntreeAux_params_WF` and
`nlist_const_staged` — typing lemmas of the block, not `pos` instances — plus `type_tac`. -/

/-- The field context of `NTree.node`'s second field: `α : Sort (u+1)`, then `a : α`. -/
theorem ntreeNode_field1_ctx :
    ((((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.take 1).map (·.type)).reverse
        ++ ntreeAux.params.reverse
      = [.bvar 0, .sort (.succ (.param 0))] := rfl

theorem ntreeNode_field1_posTy {env₁ env₂ : VEnv}
    (hs : env₁.addIndTypes ntreeAux = some env₂) :
    VIndField.PosTy env₂ ntreeAux [.bvar 0, .sort (.succ (.param 0))] 1
      (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default)
      { binders := [], idx := 1, args := [] } := by
  have hf := nlist_const_staged hs
  exact { onCtx := ⟨ntreeAux_params_WF, _, by type_tac⟩
          canonResult := by type_tac
          indexArgs := fun T' hT' => by cases hT'; exact .nil
          defeq := ⟨_, by type_tac⟩ }

/-- **The firing.**  `VIndField.WF` for the block's flagship recursive field — the one whose type is
the auxiliary member applied to the block's parameter — assembled from §3's two halves, with the
residual clause an instance of §2 (the reader) and the block's own typing lemmas for the rest. -/
theorem ntreeNode_field1_WF {env₁ env₂ : VEnv} (hs : env₁.addIndTypes ntreeAux = some env₂) :
    VIndField.WF env₂ ntreeAux
      (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.take 1)
      [.bvar 0, .sort (.succ (.param 0))] 1
      (((ntreeAux.types.getD 0 default).ctors.getD 0 default).fields.getD 1 default) := by
  have hf := nlist_const_staged hs
  exact { hasType := by type_tac
          level := fun ls => by simp [VLevel.eval, ntreeAux, ntreeNode, Lean.Nat.imax]
          binders_indep := fun r hr => by cases hr; exact ntreeAux_binders_indep rfl
          pos := VIndField.posSome_of_split rfl ntreeNode_field1_posSyn
            (ntreeNode_field1_posTy hs) }

end InductiveDeclExamples

/-! ## §5 The limits of this result, and where they are proved rather than asserted

**(a) The canonicity hypothesis of §1 cannot be dropped — conjunct 9 is genuinely independent of
conjuncts 1-8.**  `MRedex.TQWit` (`Theory/Inductive/IndexedNested.lean` §8) is an *indexed* nested
block with a stored field type `tqHostile` for which that file proves, separately, the `OnCtx`
(`tq_hostile_ctx_onCtx`), the `canonResult` typing (`tq_hostile_canonResult_hasType`), the `HasArgs`
derivation (`tq_hostile_hasArgs`) and the conversion to the canonical form
(`tq_hostile_defeq_canon`), while `binders = []` and `args = [Prop]` are block-free — and then proves
`tq_hostile_not_residualClean`.  So conjuncts 1-8 hold there and conjunct 9 fails, which is exactly
what §1 predicts: `tqHostile` is *not* `r.canonType D i`, only definitionally equal to it.  §1 is
therefore as strong as a theorem of its shape can be, and F7's residual clause is not redundant in
the specification — only on the canonical range and on the reader's range.

That module is deliberately **not imported** (header), so this paragraph is a citation and not a
proof term; `docs/handoff-wfpos.md` §2 carries the measurement.

**(b) The firing's residual is empty.**  `ntreeAux` has no indices, so every recursive field has
`r.args = []` and the trigger fires with an empty residual: the trigger is *exercised* — which
`accDecl_WF`'s `.forallE`-headed field never does — but the scan has nothing to scan.  So §4 tests
`uniformOcc?`'s parameter-prefix test at `np = 1` (which `mutDecl_WF`, at `np = 0`, does not) and does
**not** test the residual scan.  The block that tests the scan is `TQWit`'s, and there the answer is
negative by design.

**(c) `PosTy` is untouched by all of this.**  Conjuncts 5-8 are typing in the staged environment and
nothing here makes them cheaper; §3 exists to say so precisely rather than to improve them.

**(d) What this does *not* say about `VInductDecl'.WF` as a whole.**  `pos` is not the only field that
reads `recArg`: `VIndField.WF.binders_indep` reads it too, and that one *is* backed by the census hole
`VIndRecArg.exists_indep`.  Nothing in this file touches `exists_indep`, and nothing in this file is
in its cone — measured, not asserted (`docs/handoff-wfpos.md` §2, `scripts/exists.lean` with
`exists_indep` watched).  At `ntreeAux` `binders_indep` is discharged directly because every `ξ` is
empty (`ntreeAux_binders_indep`), which is why the hole is off the path *at this block* and not in
general.

## §6 Axiom checks

Every declaration this file introduces, in order, followed by the three that §1 migrated to
`Theory/Inductive/Decl.lean` -- those are *not* introduced here any more, and the checks are kept
because dropping them would silently drop the only axiom coverage this stream had on them.
-/

#print axioms Lean4Lean.VInductDecl'.spineArgs_drop_tyApp
#print axioms Lean4Lean.VInductDecl'.uniformOcc?_canonResult_snd
#print axioms Lean4Lean.VInductDecl'.residualClean_canonType
#print axioms Lean4Lean.VIndField.residualClean_of_canon
#print axioms Lean4Lean.VIndCtor.residualClean_of_canonical
#print axioms Lean4Lean.VInductDecl'.residualClean_of_canonical
#print axioms Lean4Lean.VExpr.betaHead_eq_self_of_spineFn_const
#print axioms Lean4Lean.VInductDecl'.spineFn_const_of_uniformOcc?
#print axioms Lean4Lean.VInductDecl'.residualClean_of_recog
#print axioms Lean4Lean.VInductDecl'.residualClean_of_recArgOf
#print axioms Lean4Lean.VIndField.PosSyn
#print axioms Lean4Lean.VIndField.PosTy
#print axioms Lean4Lean.VIndField.posSome_of_split
#print axioms Lean4Lean.VIndField.WF.posSyn
#print axioms Lean4Lean.VIndField.WF.posTy
#print axioms Lean4Lean.VIndField.decidablePosSyn
#print axioms Lean4Lean.VIndField.posSyn_of_recArgOf
#print axioms Lean4Lean.VIndField.posSyn_of_canon
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_node_field1_recArgOf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_cons_field0_recArgOf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_cons_field1_recArgOf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_recArgOf_eq_stored
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_field1_posSyn
#print axioms Lean4Lean.InductiveDeclExamples.nlistCons_field0_posSyn
#print axioms Lean4Lean.InductiveDeclExamples.nlistCons_field1_posSyn
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_residualClean_of_canonical
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_field1_ctx
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_field1_posTy
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_field1_WF
