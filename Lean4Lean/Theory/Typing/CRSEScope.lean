import Lean4Lean.Theory.Typing.ConfluenceRebuildPrice

/-!
# Scoping the Church-Rosser-over-`IsDefEqSE` target: the new rules' orientation

Round of 2026-09-04, `docs/handoff-crse.md`.  **Pricing only** — nothing here repairs anything
and nothing here is a confluence result.

`Theory/Typing/ConfluenceRebuildPrice.lean` §4 re-erects the confluence layer over the
fourteen-constructor relation, adding `NormalEqSE.structEtaL`/`structEtaR` to the conversion and
`ParRedSE.structEta` to the reduction.  Its §7 checks vacuity — but **only at `refEnv`**, where
its own §6 proves the three new rules are dead (`refEnv_no_structEtaSite`).  Read across the
whole tree, `VEnv.StructEtaSite` and the three new constructors occur in *that file alone*, and
every occurrence is a definition or a refutation (`absurd hs (StructEtaSite.not_of_no_defeqs …)`).
**The three new rules have therefore never been fired anywhere.**  This file measures the first
thing that shows up when you try.

## What is proved

* §1 `StructEtaSite.iterate` — the site **re-fires on its own output**, and the only thing it
  needs is that the output is typed at the same type.  Every other field of `StructEtaSite` is
  about `S, D, j, T, C, us, ps` and is untouched by replacing `e`.  So `ParRedSE.structEta` is an
  **expansion that re-applies to its own result**: `e ≫ η e ≫ η (η e) ≫ …`.
* §2 `not_parRedSE_rigid_of_structEtaSite` — consequently `VEnv.parRedSES_rigid`'s hypothesis
  (`∀ o, ParRedSE Γ e o → o = e`) is **false** at any structure-eta site whose expansion is not
  the subject itself.  That hypothesis is what `not_parRedStatementSE_of_propMajor` consumes and
  what every `ParRed`-normality argument in the tree is built on.
* §3 `etaExpansionG_idem_of_no_fields` — and the regress is a **positive-fields** phenomenon
  only.  At zero fields `VInductDecl'.etaExpansionG` does not mention `e` at all
  (`etaExpansionG_of_no_fields`: it is `(.const C.name us).mkApp ps`), so it is a *constant* map
  and its own fixed point after one step.
* §4 `EtaRegress` and `parRedSES_etaIter` — the honest form of the regress: it is an unbounded
  `ParRedSES` chain as soon as every stage is typed, stated as a hypothesis because no witness of
  `StructEtaSite` exists anywhere in the tree to discharge it against.

## Why this is the scoping answer and not a repair

§3 lines up with the model side exactly.  `Theory/SetModel/RecPropSingleton.lean`'s
`eq_singleton_of_recProp` and `Theory/SetModel/RecTypePeel.lean` §8's
`eq_singleton_of_mem_interp_mkPi3` validate **zero-field** surjective pairing, and validate it as
*forced* rather than chosen.  Zero fields is precisely the case where §3 says the reduction rule
is a fixed point and no orientation question arises.  The positive-field case is where both the
model validation and the rule's orientation are open, and §1–§2 say the reduction relation as
written is not usable there.

This does not refute `ParRedSE`: an expansion relation can still be confluent, and `NormalEqSE`
is symmetric so the conversion side is indifferent to orientation.  What it refutes is the
*method* — every confluence argument in this tree (`ParRed.triangle`'s measure,
`KDiamondJoin.joins_normal_iff`, `parRedSES_rigid`, `CParRed`'s neutrality test) is stated in
terms of `ParRed`-normal forms, and §1–§2 say `ParRedSE` has none at a positive-field structure.
So `ParRedSE.structEta` has to be **oriented as a contraction** (`η e ≫ e`) before any of that
machinery can be ported, and then it is `NormalEqSE`'s `structEtaL`/`structEtaR` that must be
re-derived rather than the other way round.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

/-! ## §1 The site re-fires on its own output -/

/-- **The structure-eta site is closed under its own expansion**, given only the expansion's
typing.  A `structure` update: the nine other fields of `VEnv.StructEtaSite` do not mention `e`.

This is what makes `ParRedSE.structEta` a non-terminating expansion rather than a rewrite. -/
theorem StructEtaSite.iterate {env : VEnv} {univs : Nat} {Γ : List VExpr} {S : Lean.Name}
    {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
    {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (ht : env.IsDefEqSE univs Γ (D.etaExpansionG T C us ps j e)
      (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps)) :
    StructEtaSite env univs Γ S D j T C us ps (D.etaExpansionG T C us ps j e) :=
  { h with typed := ht }

/-! ## §2 Hence no rigidity, hence no normality argument -/

section
variable [Params]
open Params

/-- **`VEnv.parRedSES_rigid`'s hypothesis is false at a structure-eta site.**  One `structEta`
step already moves `e`, so `e` is not `ParRedSE`-normal.

`parRedSES_rigid` is the tool `not_parRedStatementSE_of_propMajor` uses, and `ParRed`-normality
is the tool `ParRed.triangle`, `CParRed.exists` and `KDiamondJoin.joins_normal_iff` are built
on.  All of them lose their footing here. -/
theorem not_parRedSE_rigid_of_structEtaSite {Γ : List VExpr} {S : Lean.Name}
    {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
    {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (hne : D.etaExpansionG T C us ps j e ≠ e) :
    ¬ (∀ o, ParRedSE Γ e o → o = e) :=
  fun hrig => hne (hrig _ (.structEta h))

end

/-! ## §3 …and the regress is positive-fields-only

At zero fields the expansion does not mention its subject, so it is a constant map and one step
is all there is.  This is exactly the case the set model's forced validation covers. -/

/-- **The zero-field expansion is its own fixed point.**  `etaExpansionG_of_no_fields` says both
sides are `(.const C.name us).mkApp ps`. -/
theorem etaExpansionG_idem_of_no_fields {D : VInductDecl'} {T : VIndType} {C : VIndCtor}
    {us : List VLevel} {ps : List VExpr} {j : Nat} {e : VExpr} (h : C.fields = []) :
    D.etaExpansionG T C us ps j (D.etaExpansionG T C us ps j e)
      = D.etaExpansionG T C us ps j e := by
  rw [VInductDecl'.etaExpansionG_of_no_fields _ _ _ _ h,
    VInductDecl'.etaExpansionG_of_no_fields _ _ _ _ h]

/-! ## §4 The regress, stated honestly

No witness of `StructEtaSite` exists anywhere in the tree, so the "every stage is typed" side
condition cannot be discharged today.  It is therefore a hypothesis, and the chain is stated
against it rather than asserted. -/

/-- The `n`-fold η-expansion. -/
def etaIterG (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (ps : List VExpr) (j : Nat) : Nat → VExpr → VExpr
  | 0, e => e
  | n + 1, e => D.etaExpansionG T C us ps j (etaIterG D T C us ps j n e)

section
variable [Params]
open Params

/-- **Every stage of the η-tower is typed** — the side condition §1 needs to iterate.  Stated as
a `Prop` rather than assumed inline, so that a future witness can be pointed at it. -/
def EtaStagesTyped (Γ : List VExpr) (S : Lean.Name) (D : VInductDecl') (j : Nat) (T : VIndType)
    (C : VIndCtor) (us : List VLevel) (ps : List VExpr) (e : VExpr) : Prop :=
  ∀ n, env.IsDefEqSE univs Γ (etaIterG D T C us ps j n e) (etaIterG D T C us ps j n e)
    ((VExpr.const S us).mkApp ps)

/-- **The site fires at every stage.** -/
theorem StructEtaSite.at_stage {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
    {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (ht : EtaStagesTyped Γ S D j T C us ps e) :
    ∀ n, StructEtaSite env univs Γ S D j T C us ps (etaIterG D T C us ps j n e)
  | 0 => h
  | n + 1 => (h.at_stage ht n).iterate (ht (n + 1))

/-- **The unbounded chain.**  `ParRedSES` reaches the `n`-th η-expansion for every `n`. -/
theorem parRedSES_etaIter {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
    {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr}
    (h : StructEtaSite env univs Γ S D j T C us ps e)
    (ht : EtaStagesTyped Γ S D j T C us ps e) :
    ∀ n, ParRedSES Γ e (etaIterG D T C us ps j n e)
  | 0 => .rfl
  | n + 1 => (parRedSES_etaIter h ht n).tail (.structEta (h.at_stage ht n))

end

end VEnv

end Lean4Lean

/-! ## §5 The axiom sweep, inline

Per `docs/handoff-crse.md`'s process rule: `#print axioms` on **every** declaration this file
adds, in the file, where the claim cannot go stale.  One round in this project had a declaration
silently elaborate to a hole because `autoImplicit` bound an out-of-scope name; only its own
axioms line caught it.  Expected: everything `sorryAx`-free. -/

#print axioms Lean4Lean.VEnv.StructEtaSite.iterate
#print axioms Lean4Lean.VEnv.not_parRedSE_rigid_of_structEtaSite
#print axioms Lean4Lean.VEnv.etaExpansionG_idem_of_no_fields
#print axioms Lean4Lean.VEnv.etaIterG
#print axioms Lean4Lean.VEnv.EtaStagesTyped
#print axioms Lean4Lean.VEnv.StructEtaSite.at_stage
#print axioms Lean4Lean.VEnv.parRedSES_etaIter
