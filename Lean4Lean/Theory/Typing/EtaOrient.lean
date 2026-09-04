import Lean4Lean.Theory.Typing.CRSEScope

/-!
# The structure-eta rules, fired — and the parallel contraction relation, retired

Round of 2026-09-04, `docs/handoff-etaorient.md`; **rewritten 2026-09-04 after the flip landed**,
`docs/handoff-flipland.md`.  **Pricing and firing only** — nothing here is a confluence result and
nothing here repairs `NormalEq.descend` or `NormalEq.parRed`.

## What this file was, and why five of its seven sections are gone

It argued that `VEnv.ParRedSE.structEta` was mis-oriented.  As written it was an *expansion*,
`ParRedSE Γ e (η e)`; `CRSEScope.StructEtaSite.iterate` shows the site re-fires on its own output
needing only that the output is typed, so the chain `e ≫ η e ≫ η (η e) ≫ …` had no last term and
`VEnv.parRedSES_rigid`'s hypothesis was **false** at every site.  To price the alternative without
touching a file it did not own, this file declared a **parallel relation** `VEnv.ParRedSEC` —
`ParRedSE`'s nine other constructors verbatim, the tenth flipped — and ported eight downstream
proofs onto it.

`Theory/Typing/ConfluenceRebuildPrice.lean:433-438` was then flipped, so **`ParRedSE` *is* the
contraction** and `ParRedSEC` was duplicate machinery.  Measured before deleting: a verbatim
re-declaration of `ParRedSEC` against the post-flip `ParRedSE` is **provably** the same relation
in both directions (ten cases each, and the same for the reflexive-transitive closures) but
**not definitionally** the same — `@ParRedSEC = @ParRedSE` by `rfl` fails, and so does `Iff.rfl`,
because they are two distinct `inductive` types with pointwise-identical constructor lists.  So
every SEC declaration duplicated one that already existed, and each is deleted in favour of it:

| deleted | replaced by |
|---|---|
| `VEnv.ParRedSEC`, `.rfl`, `ParRedSECS`, `parRedSECS_rigid` | `VEnv.ParRedSE`, `.rfl`, `ParRedSES`, `parRedSES_rigid` (`ConfluenceRebuildPrice.lean`) |
| `ParRedSEC.rigid_of_eq_bvar`, `parRedSEC_rigid_bvar`, `ParRedSEC.rigid_of_eq_sort`, `parRedSEC_rigid_sort` | `CRSEScope.lean` §2, same four names on `ParRedSE` |
| `StructEtaStepC`, `.toParRedSEC`, `.sizeOf_lt`, `no_infinite_structEtaStepC`, `parRedSECS_etaIter_down` | `CRSEScope.lean` §4's `StructEtaStep`, `.toParRedSE`, `.sizeOf_lt`, `no_infinite_structEtaStep`, `parRedSES_etaIter_down` |
| `parRedSEC_iff_of_no_defeqs`, `parRedSECS_iff_of_no_defeqs`, `ParRedStatementSEC`, `not_parRedStatementSEC_of_propMajor`, `DescendStatementSEC`, `descendStatementSEC_iff_of_no_defeqs`, `descendSEC_uniq_sortUniq_not_all` | the un-suffixed originals in `ConfluenceRebuildPrice.lean` §4–§6 |

Its old §1–§2 — `VExpr.sizeOf_le_mkApp`, `mkApp_eq_or_app`, `sizeOf_lt_mkApp_of_mem`,
`VInductDecl'.sizeOf_lt_projCoreG`, `_projTermG`, `_etaExpansionG`, `etaExpansionG_ne_bvar`,
`_ne_sort`, `_ne_lam`, `_ne_forallE`, `etaExpansionG_ne` — are **relocated** to
`Theory/Typing/CRSEScope.lean` §0 under their existing fully-qualified names, because §2 and §4
there need them and this file is downstream.  Nothing outside these two files cited them
(grepped 2026-09-04), so the move is invisible.

## What is proved here now

**The three new SE rules, fired.**  `MutField.unitEnv_structEtaSite` and
`MutField.declEnv_structEtaSite` are the first `VEnv.StructEtaSite` witnesses anywhere in the
tree — at the zero-field member `A` of `MutField.decl` (subject: the axiom `MutField.foo`) and at
its **positive-field** member `B` (`bCtor.fields.length = 1`, subject `.bvar 0`).  Neither needs a
`Params` instance and neither needs `VEnv.WF`.  On top of them, `ParRedSE.structEta`,
`NormalEqSE.structEtaL` and `NormalEqSE.structEtaR` all fire at both shapes.

**CORRECTED 2026-09-04** (kept from the pre-flip text, still true): this used to add "`VEnv.WF
declEnv` is open for everybody and is *not* used", which is **false**.  `MutField.declEnv_wf` and
`unitEnv_wf` (`Verify/TypeChecker/EtaUnitRefute.lean`) are `sorryAx`-free theorems, and
`can-cite.py` says they sat inside this file's own 232-module closure while that sentence was
being written.  The witnesses genuinely do not use them — which is a **stronger** result than the
sentence claimed — but not for the stated reason.

## The expansion firing does not survive, and this is the honest statement of that

Pre-flip this file's §6 fired the expansion rule twice
(`unitEnv_parRedSE_structEta : ParRedSE [] e (η e)`) and closed with `declEnv_rigidity_flips`,
whose left conjunct was `CRSEScope.not_parRedSE_rigid_of_structEtaSite` instantiated for the first
time: `¬ (∀ o, ParRedSE bCtx (.bvar 0) o → o = .bvar 0)`.

**That result is now false, not merely unstatable.**  `VEnv.parRedSE_rigid_bvar` (`CRSEScope` §2)
proves `∀ o, ParRedSE Γ (.bvar i) o → o = .bvar i` with no hypotheses at all, and this file's
positive-field witness is a site whose subject is exactly `.bvar 0`.  So the pre-flip negative
result is gone **at the site's subject**, and no restatement can recover it there.

What survives is the same fact one term along the step.  The redex is now the *expansion*, so it
is the expansion that fails to be rigid: `VEnv.not_parRedSE_rigid_etaExpansionG_of_structEtaSite`
(`CRSEScope` §2), under the same two hypotheses (a site, and `η e ≠ e`) and the same one-line
proof up to `.symm`.  `declEnv_rigidity_flips` below is restated as exactly that pair, so the
before/after is still machine-checked at a positive-field structure — with both conjuncts having
changed side.  **Nothing was quietly dropped: `unitEnv_parRedSE_structEta` and
`declEnv_parRedSE_structEta` keep their names and now state the contraction**, and the two
`…_parRedSEC_structEtaC` firings are deleted because after the flip they are literally the same
statements.  Eight firings became six.

## What re-orientation costs, and what breaks

**The `Params` firings are conditional, and not because of eta.**  `VEnv.StructEtaSite` takes no
`Params` instance, so the two site witnesses are unconditional.  But `NormalEqSE` and `ParRedSE`
live under `variable [Params]`, and `Params.extra_pat` demands that *every* `env.defeqs` rule be
`Pat`-registered.  `StructEtaSite.isStruct` is `env.IsStructureG`, and
`IsStructureG.not_of_no_defeqs` holds precisely because `IsStructureG.decl` puts the block's
**ι-rules** into `env.defeqs`.  Registering an ι-rule is `PatWF`'s ι case, which
`Theory/Typing/ParamsBuild.lean` says needs `IsDefEqU.forallE_inv`.  So the firings carry
`env = unitEnv` / `env = declEnv` hypotheses.

**CORRECTED 2026-09-04, twice over** (kept).  This paragraph used to end "and **no `Params`
instance satisfying them exists today**".  Both halves of its reasoning were wrong.  First,
`IsDefEqU.forallE_inv` is **not a hole** — measured arity 10, cone 3574, `own value is a hole:
false` — it is a theorem standing on `forallE_inv_stratified` and `WF.rigidShapeUniqNS`, which are
the real census entries; `ParamsBuild.lean`'s "(open)" was the source and is corrected there.
Second, and consequently, the instance **does** exist: `Theory/Typing/ParamsStruct.lean` builds
`MutField.declParams` at the positive-field structure environment with **no hypotheses at all**,
priced at those two holes, and restates the firings without the environment pin.  Its §1 lifts the
*site* pin too, stating the rules at an arbitrary `env.WF` with an arbitrary `StructEtaSite`, so
`MutField` drops from "the only statable place" to one instantiation.
`Theory/Typing/ParamsCR.lean` later showed the instance is **not** a counterexample generator —
Church–Rosser is not false there, and the one hypothesis that fails is **false**, not unproved.

**What the expansion form gave that the contraction does not.**  `ParRedSE.structEta` composed
with `NormalEqSE.structEtaL`/`structEtaR` in the obvious way: the conversion rule peels `η e` on
one side and the reduction rule *produced* `η e`, so `descend`'s "the conversion rule has a reduct
to descend to" discipline was satisfied by construction (that is the stated reason
`ConfluenceRebuildPrice` §4 chose the expansion).  Under the contraction the reduction runs
`η e ⟶ e` while `structEtaL`/`structEtaR` still recurse *on* `η e`, so at a `structEtaL` node the
reduction available at the subject `e` no longer reaches the term the conversion rule recurses on.
**That is the real cost, and it is a cost on `descend` alone** — `NormalEqSE` itself is unchanged
and is orientation-symmetric, because it peels rather than produces.  It is also a cost against a
statement that is already refuted at 13 constructors and again at 14 in either orientation
(`descendSE_uniq_sortUniq_not_all`, `not_parRedStatementSE_of_propMajor`, both in
`ConfluenceRebuildPrice.lean`, both unmoved by the flip), so nothing that was working stops
working.

## Consuming module

`Theory/Typing/ParamsStruct.lean`, which removes the `env = unitEnv` / `env = declEnv` pins from
every firing below.
-/

namespace Lean4Lean

open VExpr

/-! ## §1 The three rules, fired -/

namespace MutField

/-- **Site witness 1 — the zero-field member.**  `StructEtaPrice` §5's `structEtaSE_foo` premises,
bundled as `VEnv.StructEtaSite`.  Takes no `Params` instance and no `VEnv.WF`. -/
theorem unitEnv_structEtaSite :
    VEnv.StructEtaSite unitEnv 0 [] `MutField.A decl 0 aTy aCtor [] []
      ((VExpr.const `MutField.foo []).mkApp []) where
  isStruct := unitEnv_IsStructureG_0
  indices := rfl
  recFields := rfl
  nuvars := rfl
  levelWF := nofun
  np := rfl
  args := .nil
  typed := unitEnv_foo_hasType.toSE
  small := .inr (by simp [aCtor])

/-- **Site witness 2 — the positive-field member**, `bCtor.fields.length = 1`. -/
theorem declEnv_structEtaSite :
    VEnv.StructEtaSite declEnv 0 bCtx `MutField.B decl 1 bTy bCtor [] [] (.bvar 0) where
  isStruct := declEnv_IsStructureG
  indices := rfl
  recFields := rfl
  nuvars := rfl
  levelWF := nofun
  np := rfl
  args := .nil
  typed := VEnv.IsDefEq.toSE (.bvar (.zero ..))
  small := .inr bCtor_field_prop

/-- The positive-field member really is positive-field. -/
theorem bCtor_fields_pos : 0 < bCtor.fields.length := by decide

/-- …and the expansion there differs from its subject, so
`not_parRedSE_rigid_etaExpansionG_of_structEtaSite` has something to bite on. -/
theorem declEnv_etaExpansionG_ne :
    decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0) ≠ .bvar 0 :=
  decl.etaExpansionG_ne bTy bCtor [] bCtor_fields_pos

/-- The zero-field firing of `IsDefEqSE.structEta`, kept in the *raw* `etaExpansionG` form
(`StructEtaPrice`'s `structEtaSE_foo` has already rewritten it to `.const MutField.A.mk []`).

Note that the **typing judgement**'s eta rule is symmetric (`IsDefEqSE` is an equality), so it is
untouched by the reduction relation's orientation; only `ParRedSE` had a direction to flip. -/
theorem unitEnv_isDefEqSE_eta :
    unitEnv.IsDefEqSE 0 [] ((VExpr.const `MutField.foo []).mkApp [])
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.A []).mkApp []) :=
  VEnv.structEtaGSE unitEnv unitEnv_IsStructureG_0 rfl rfl rfl nofun rfl .nil
    unitEnv_foo_hasType (.inr (by simp [aCtor]))

/-- The expansion is typed at the zero-field site — `NormalEqSE.refl`'s premise. -/
theorem unitEnv_eta_hasType :
    unitEnv.IsDefEqSE 0 [] (decl.etaExpansionG aTy aCtor [] [] 0
        ((VExpr.const `MutField.foo []).mkApp []))
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.A []).mkApp []) :=
  unitEnv_isDefEqSE_eta.symm.trans unitEnv_isDefEqSE_eta

/-- The same at the positive-field site; `structEtaSE_B` is already in raw form. -/
theorem declEnv_eta_hasType :
    declEnv.IsDefEqSE 0 bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0))
      (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0))
      ((VExpr.const `MutField.B []).mkApp []) :=
  structEtaSE_B.symm.trans structEtaSE_B

section
variable [VEnv.Params]
open VEnv VEnv.Params

/-- Site witness 1, moved onto a `Params` instance sitting over `unitEnv`. -/
theorem unitEnv_site_at_params (he : env = unitEnv) (hu : univs = 0) :
    StructEtaSite env univs [] `MutField.A decl 0 aTy aCtor [] []
      ((VExpr.const `MutField.foo []).mkApp []) := by
  rw [he, hu]; exact unitEnv_structEtaSite

/-- Site witness 2, likewise. -/
theorem declEnv_site_at_params (he : env = declEnv) (hu : univs = 0) :
    StructEtaSite env univs bCtx `MutField.B decl 1 bTy bCtor [] [] (.bvar 0) := by
  rw [he, hu]; exact declEnv_structEtaSite

/-! ### `ParRedSE.structEta` — the **contraction**, both shapes

Same names as before the flip, opposite endpoints.  The pre-flip statements
(`ParRedSE [] e (η e)`) are not merely unproved now, they are not derivable: the only rule that
could conclude about `.bvar 0` is `bvar` itself (`parRedSE_rigid_bvar`). -/

theorem unitEnv_parRedSE_structEta (he : env = unitEnv) (hu : univs = 0) :
    ParRedSE [] (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.foo []).mkApp []) :=
  .structEta (unitEnv_site_at_params he hu)

theorem declEnv_parRedSE_structEta (he : env = declEnv) (hu : univs = 0) :
    ParRedSE bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) (.bvar 0) :=
  .structEta (declEnv_site_at_params he hu)

/-! ### `NormalEqSE.structEtaL` / `structEtaR` — both shapes, unchanged by the flip -/

theorem unitEnv_normalEqSE_structEtaL (he : env = unitEnv) (hu : univs = 0) :
    NormalEqSE [] ((VExpr.const `MutField.foo []).mkApp [])
      (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp [])) := by
  refine .structEtaL (unitEnv_site_at_params he hu)
    (.refl (A := (VExpr.const `MutField.A []).mkApp []) ?_)
  show IsDefEqSE env univs _ _ _ _
  rw [he, hu]; exact unitEnv_eta_hasType

theorem unitEnv_normalEqSE_structEtaR (he : env = unitEnv) (hu : univs = 0) :
    NormalEqSE [] (decl.etaExpansionG aTy aCtor [] [] 0 ((VExpr.const `MutField.foo []).mkApp []))
      ((VExpr.const `MutField.foo []).mkApp []) := by
  refine .structEtaR (unitEnv_site_at_params he hu)
    (.refl (A := (VExpr.const `MutField.A []).mkApp []) ?_)
  show IsDefEqSE env univs _ _ _ _
  rw [he, hu]; exact unitEnv_eta_hasType

theorem declEnv_normalEqSE_structEtaL (he : env = declEnv) (hu : univs = 0) :
    NormalEqSE bCtx (.bvar 0) (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) := by
  refine .structEtaL (declEnv_site_at_params he hu)
    (.refl (A := (VExpr.const `MutField.B []).mkApp []) ?_)
  show IsDefEqSE env univs _ _ _ _
  rw [he, hu]; exact declEnv_eta_hasType

theorem declEnv_normalEqSE_structEtaR (he : env = declEnv) (hu : univs = 0) :
    NormalEqSE bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) (.bvar 0) := by
  refine .structEtaR (declEnv_site_at_params he hu)
    (.refl (A := (VExpr.const `MutField.B []).mkApp []) ?_)
  show IsDefEqSE env univs _ _ _ _
  rw [he, hu]; exact declEnv_eta_hasType

/-! ### The before/after, at the positive-field site -/

/-- **What re-orientation bought, machine-checked at a positive-field structure.**  Both conjuncts
changed side when `ParRedSE.structEta` was flipped, which is the whole content of the flip:

* Left, **new**: the site's subject `.bvar 0` **is** `ParRedSE`-rigid, and unconditionally —
  `parRedSE_rigid_bvar` needs neither the site nor any hypothesis on the environment.  Pre-flip
  this conjunct read `¬ (∀ o, ParRedSE bCtx (.bvar 0) o → o = .bvar 0)`, i.e. exactly its own
  negation, and that was this file's headline instantiation of
  `CRSEScope.not_parRedSE_rigid_of_structEtaSite`.  **That statement is now false**, and is not
  recoverable at the subject in any form.
* Right, **the surviving half of it**: rigidity still fails at the site, but at the *expansion*,
  which is now the redex.

So the flip did not delete the negative result, it moved it one term along the step — and the
positive result it put in its place is what every `ParRed`-normality argument in the tree needs.
See `Theory/Typing/ParamsStruct.lean` for the same pair with the environment pin removed. -/
theorem declEnv_rigidity_flips (he : env = declEnv) (hu : univs = 0) :
    (∀ o, ParRedSE bCtx (.bvar 0) o → o = .bvar 0) ∧
      ¬ (∀ o, ParRedSE bCtx (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) o
          → o = decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)) :=
  ⟨parRedSE_rigid_bvar,
    not_parRedSE_rigid_etaExpansionG_of_structEtaSite (declEnv_site_at_params he hu)
      declEnv_etaExpansionG_ne⟩

end

end MutField

end Lean4Lean

/-! ## §2 The axiom sweep, inline

`#print axioms` on **every** declaration this file adds, in the file, where the claim cannot go
stale.  Expected: everything `sorryAx`-free — in particular the firings, whose only hypotheses are
`env = unitEnv` / `env = declEnv`, and which must **not** pull in `VEnv.WF declEnv`. -/

#print axioms Lean4Lean.MutField.unitEnv_structEtaSite
#print axioms Lean4Lean.MutField.declEnv_structEtaSite
#print axioms Lean4Lean.MutField.bCtor_fields_pos
#print axioms Lean4Lean.MutField.declEnv_etaExpansionG_ne
#print axioms Lean4Lean.MutField.unitEnv_isDefEqSE_eta
#print axioms Lean4Lean.MutField.unitEnv_eta_hasType
#print axioms Lean4Lean.MutField.declEnv_eta_hasType
#print axioms Lean4Lean.MutField.unitEnv_site_at_params
#print axioms Lean4Lean.MutField.declEnv_site_at_params
#print axioms Lean4Lean.MutField.unitEnv_parRedSE_structEta
#print axioms Lean4Lean.MutField.declEnv_parRedSE_structEta
#print axioms Lean4Lean.MutField.unitEnv_normalEqSE_structEtaL
#print axioms Lean4Lean.MutField.unitEnv_normalEqSE_structEtaR
#print axioms Lean4Lean.MutField.declEnv_normalEqSE_structEtaL
#print axioms Lean4Lean.MutField.declEnv_normalEqSE_structEtaR
#print axioms Lean4Lean.MutField.declEnv_rigidity_flips
