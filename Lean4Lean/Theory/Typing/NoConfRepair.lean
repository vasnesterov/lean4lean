import Lean4Lean.Theory.Typing.StructEtaPrice
import Lean4Lean.Verify.Typing.ProjSpineInv

/-!
# Repairing const-head no-confusion against structure eta

`Theory/Typing/StructEtaPrice.lean` §6 proves that **no** relation satisfies both structure eta
and const-head no-confusion (`eta_and_constNoConf_incompatible`), and instantiates it at the
fourteen-constructor relation (`constNoConf_false_for_IsDefEqSE`).  The conclusion drawn there is
that `VEnv.IsDefEq.constApp_inv` (`Verify/Typing/ConstSpine.lean:248`) "is **false** for the
extended relation, not merely unproved", and that "every one of the 187 transitive users has to
be re-derived from a *weaker* no-confusion lemma carrying a side condition that excludes
structure constructors (or excludes unit-like types).  That side condition does not exist
anywhere in the tree today."

**This file is the scoping round for that repair.**  It does not perform it: `IsDefEq` is
untouched, `ConstSpine.lean` is untouched, nothing existing is edited.

## The three findings, in order of how much they change the estimate

### 1. What eta kills is the `¬ IsProof` guard, and the `IsType` guard survives it

`IsDefEq.constApp_inv`'s guard is `¬ IsProof` — not `IsType` — and its docstring says why: it is
what blocks `NormalEq.proofIrrel`, and it *propagates down the spine* by `IsProof.app'` where
`IsType` would not.  The refutation in §6 of `StructEtaPrice.lean` runs at exactly that guard:
`MutField.unitEnv_not_isProof_foo` is one of its inputs.

The `VEnv`-facing predicate `VEnv.ConstNoConf` (`Verify/Typing/Rigidity.lean:151`) is guarded by
`IsType` instead, and every wrapper in the family converts one to the other on the spot
(`constApp_inv_of_patWF`'s last argument is literally `IsType.not_isProof henv hΓ hty`).

**The eta witness fails the `IsType` guard**: `MutField.unitEnv_not_isType_foo` and
`unitEnv_not_isType_Amk` below.  Both `foo` and `A.mk` inhabit `A : Type`; neither *is* a type.
So the refutation does not reach the `IsType`-guarded row — it reaches only the `¬ IsProof` row,
which is a strictly stronger statement that the tree derives the `IsType` row *from*.

That is not a coincidence about this witness.  §2 below is the general fact: the left endpoint of
**every** instance of the eta rule satisfies `VEnv.StructInhab` (it inhabits a structure type by
the rule's own typing premise), and `StructInhab` is incompatible with `IsType` at a well-formed
environment.  So the guard that survives eta is available at every eta instance, not just this
one — the analogue, one universe up, of `¬ IsProof` blocking `proofIrrel`.

### 2. …but `IsType` is not an induction invariant, and `¬ StructInhab` is

The reason the repair is not free.  `IsType` cannot be threaded through `NormalEq.constApp_inv`'s
`appDF` case: a *proper sub-spine* of a type-valued spine has a **Π** type, not a sort, so
`IsType` fails there.  That is precisely why `ConstSpine.lean` states the lemma with `¬ IsProof`.

`¬ StructInhab` does thread, and better than `¬ IsProof` does: at a proper sub-spine it is not
inherited but **free**, because a Π-typed term is not an inhabitant of a structure type
(`notStructInhab_of_forallE`, §2).  So the repaired lemma carries *two* guards — `¬ IsProof`
against `proofIrrel`, `¬ StructInhab` against `structEta` — and the second costs nothing at the
sub-spines and is implied by `IsType` at the top (`notStructInhab_of_isType`).
`ConstAppInvSI` (§4) is that statement, and `ConstAppInvSI.constApp_inv_of_isType` proves it
still delivers `constApp_inv_of_wf`'s conclusion to its consumers.

### 3. Three guards that do **not** survive, so nobody re-proposes them

* `¬ IsProof` alone — refuted, in the tree (`constNoConf_false_for_IsDefEqSE`).
* "neither head is a structure constructor" — §5: refuted, and by *transitivity*, which is the
  trap.  Two distinct axiom inhabitants of one unit-like structure both η-relate to the
  constructor, hence to each other, and neither of them is a constructor.
* "the structure has at least one field" / "the structure is not a subsingleton" — §5: refuted at
  `MutField.B`, a one-field member of the same block; the eta output there is already a
  `const`-headed spine in the tree (`MutField.declEnv_etaExpansionG_eq`), so the mechanism never
  mentions the field count.

## What this file does not claim

It does **not** prove `ConstAppInvSI` for the fourteen-constructor relation.  That is the repair,
and §6 records what it needs: the whole `ParRed`/`NormalEq`/Church–Rosser chain re-run with the
new guard, whose only genuinely new steps are the two the guard is designed for.  What is proved
here is that the statement is *not refuted* — §3 exhibits a non-degenerate relation satisfying
structure eta and the guarded no-confusion at once — and that it *suffices*: §4.
-/

namespace Lean4Lean

open VExpr

namespace VEnv

/-! ## 1. The guard

`StructInhabAt` is parametric in the typing relation, for the same reason
`eta_and_constNoConf_incompatible` is parametric in `R`: the eta rule's typing premise lives in
whatever relation carries the rule, and the guard has to be statable against all of them.  The
`IsDefEq` instance is `StructInhab`; the fourteen-constructor instance is used in §2. -/

/-- **`e` inhabits a structure type** — the shape the eta rule's left endpoint has, by the rule's
own premises.  `Ty e A` is "`e` has type `A`" in whichever relation is under discussion.

This is the exact analogue of `VEnv.IsProof`: that says `e` inhabits a *proposition* and is what
blocks `proofIrrel`; this says `e` inhabits a *structure* and is what blocks `structEta`. -/
def StructInhabAt (env : VEnv) (Ty : VExpr → VExpr → Prop) (e : VExpr) : Prop :=
  ∃ (S : Lean.Name) (D : VInductDecl') (j : Nat) (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps : List VExpr),
    env.IsStructureG S D j T C ∧ T.indices = [] ∧ C.recFields = [] ∧
      Ty e ((VExpr.const S us).mkApp ps)

/-- `StructInhabAt` at the thirteen-constructor relation's own typing judgement. -/
def StructInhab (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  env.StructInhabAt (env.HasType U Γ) e

/-! ## 2. The guard blocks every eta instance, and is free where `IsType` is not -/

/-- **Every instance of the structure-eta rule has a `StructInhab` left endpoint.**

Route-independent in `StructEtaPrice.lean` §6's sense: `Ty` is arbitrary, so this covers
`VEnv.StructEtaG`'s premises (`Ty := env.HasType U Γ`), the fourteenth constructor's premises
(`Ty := fun e A => env.IsDefEqSE U Γ e e A`) and the closed-`VDefEq` alternative of §7 alike.
The hypotheses are literally the first, second, third and eighth premises of
`VEnv.StructEtaG`; the level, parameter and F17 clauses are not needed. -/
theorem structEta_lhs_structInhabAt {env : VEnv} {Ty : VExpr → VExpr → Prop} {S : Lean.Name}
    {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    {ps : List VExpr} {e : VExpr}
    (hS : env.IsStructureG S D j T C) (hidx : T.indices = []) (hrec : C.recFields = [])
    (he : Ty e ((VExpr.const S us).mkApp ps)) : env.StructInhabAt Ty e :=
  ⟨S, D, j, T, C, us, ps, hS, hidx, hrec, he⟩

/-- **A type is not a structure inhabitant.**  The top-of-spine half: this is what lets the
consumer-facing `IsType` guard discharge the induction's `¬ StructInhab` guard.

`hrf` is `RuleFreeHead` at the *structure's* name, which is what (A)-sort-disjointness needs.
`VEnv.IsStructure.ruleFreeHead` supplies it for the narrow predicate; for `IsStructureG` at a
block index `j` nothing in the tree does — see §6, gap (i). -/
theorem notStructInhab_of_isType {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    {e : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S)
    (hty : env.IsType U Γ e) : ¬ env.StructInhab U Γ e := by
  rintro ⟨S, D, j, T, C, us, ps, hS, -, -, he⟩
  obtain ⟨u, hu⟩ := hty
  obtain ⟨w, hw⟩ := WF.uniq' henv hΓ hu he
  exact const_sort_inv_of_wf henv U Γ S us ps u hΓ (hrf _ _ _ _ _ hS) (IsDefEqU.symm ⟨.sort w, hw⟩)

/-- **A Π-typed term is not a structure inhabitant.**  The sub-spine half, and the reason the new
guard is cheaper than `¬ IsProof`: `IsProof` had to be *inherited* down the spine through
`IsProof.app'`, while `StructInhab` is refuted outright at every proper sub-spine, because a
proper sub-spine of an application has a Π type. -/
theorem notStructInhab_of_forallE {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    {f A B : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S)
    (hf : env.HasType U Γ f (.forallE A B)) : ¬ env.StructInhab U Γ f := by
  rintro ⟨S, D, j, T, C, us, ps, hS, -, -, he⟩
  obtain ⟨w, hw⟩ := WF.uniq' henv hΓ hf he
  exact const_forallE_inv_of_wf henv U Γ S us ps A B hΓ (hrf _ _ _ _ _ hS)
    (IsDefEqU.symm ⟨.sort w, hw⟩)

end VEnv

/-! ## 3. The witness: the guard change is exactly what separates refuted from unrefuted

Everything here runs at `MutField.unitEnv` — the environment `StructEtaPrice.lean` §6's
refutation runs at, with a proved `VEnv.WF` (`MutField.unitEnv_wf`), a zero-field structure
member `A : Type` in a two-type mutual block, and an **axiom** inhabitant `foo : A`. -/

namespace MutField

theorem unitEnv_Amk_hasType :
    unitEnv.HasType 0 [] ((VExpr.const `MutField.A.mk []).mkApp [])
      ((VExpr.const `MutField.A []).mkApp []) :=
  .constDF unitEnv_Amk nofun nofun rfl .nil

/-- **The eta rule's left endpoint here is a structure inhabitant**, by §2 applied to the very
premises `MutField.structEtaSE_foo` supplies. -/
theorem unitEnv_structInhab_foo : unitEnv.StructInhab 0 [] ((VExpr.const `MutField.foo []).mkApp []) :=
  VEnv.structEta_lhs_structInhabAt unitEnv_IsStructureG_0 rfl rfl unitEnv_foo_hasType

/-- …and so is its right endpoint. -/
theorem unitEnv_structInhab_Amk :
    unitEnv.StructInhab 0 [] ((VExpr.const `MutField.A.mk []).mkApp []) :=
  VEnv.structEta_lhs_structInhabAt unitEnv_IsStructureG_0 rfl rfl unitEnv_Amk_hasType

/-- **`foo` is not a type.**  Proved directly rather than through
`VEnv.notStructInhab_of_isType`, whose `hrf` hypothesis quantifies over *all* structures of the
environment (§6, gap (i)); here the structure is `A` and `RuleFreeHead A` is a computation.

This is the fact `StructEtaPrice.lean` §6 needed and did not have: the refutation's left endpoint
satisfies `¬ IsProof` (`unitEnv_not_isProof_foo`) but **not** `IsType`. -/
theorem unitEnv_not_isType_foo :
    ¬ unitEnv.IsType 0 [] ((VExpr.const `MutField.foo []).mkApp []) := by
  rintro ⟨u, hu⟩
  obtain ⟨w, hw⟩ := VEnv.WF.uniq' unitEnv_wf trivial hu unitEnv_foo_hasType
  exact VEnv.const_sort_inv_of_wf unitEnv_wf 0 [] `MutField.A [] [] u trivial
    (unitEnv_ruleFreeHead (by decide) (by decide)) (VEnv.IsDefEqU.symm ⟨.sort w, hw⟩)

/-- **…and neither is `A.mk`**, so the guard excludes the pair from *both* sides: `ConstNoConf`
guards only its left spine, but there is no orientation of this pair that satisfies it. -/
theorem unitEnv_not_isType_Amk :
    ¬ unitEnv.IsType 0 [] ((VExpr.const `MutField.A.mk []).mkApp []) := by
  rintro ⟨u, hu⟩
  obtain ⟨w, hw⟩ := VEnv.WF.uniq' unitEnv_wf trivial hu unitEnv_Amk_hasType
  exact VEnv.const_sort_inv_of_wf unitEnv_wf 0 [] `MutField.A [] [] u trivial
    (unitEnv_ruleFreeHead (by decide) (by decide)) (VEnv.IsDefEqU.symm ⟨.sort w, hw⟩)

/-! ### The compatibility model

`docs/vacuity-ledger.md` §0's discipline both ways.  `etaLink` is the equivalence closure of the
one eta pair: it satisfies structure eta at `unitEnv`'s zero-field member **and** the
`¬ StructInhab`-guarded no-confusion, so §6 of `StructEtaPrice.lean` — "*no* relation whatever can
satisfy structure eta and const-head no-confusion at the same time" — does not extend to the
guarded row.  And it is non-degenerate: it is reflexive on all of `VExpr` (so it relates
something, unlike the empty relation, which would satisfy everything) and it relates two
syntactically distinct closed constants. -/

/-- The equivalence closure of `MutField.structEtaSE_foo`'s pair. -/
def etaLink (a b : VExpr) : Prop :=
  a = b ∨ (a = .const `MutField.foo [] ∧ b = .const `MutField.A.mk []) ∨
          (a = .const `MutField.A.mk [] ∧ b = .const `MutField.foo [])

theorem etaLink_refl (e : VExpr) : etaLink e e := .inl rfl

theorem etaLink_symm {a b : VExpr} (h : etaLink a b) : etaLink b a := by
  rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl rfl
  · exact .inr (.inr ⟨rfl, rfl⟩)
  · exact .inr (.inl ⟨rfl, rfl⟩)

theorem etaLink_trans {a b c : VExpr} (h₁ : etaLink a b) (h₂ : etaLink b c) : etaLink a c := by
  rcases h₁ with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨h, -⟩ | ⟨-, rfl⟩
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · exact absurd h (by simp)
    · exact .inl rfl
  · rcases h₂ with rfl | ⟨-, rfl⟩ | ⟨h, -⟩
    · exact .inr (.inr ⟨rfl, rfl⟩)
    · exact .inl rfl
    · exact absurd h (by simp)

/-- **`etaLink` contains the eta instance** — the same pair `MutField.structEtaSE_foo` produces
and `eta_and_constNoConf_incompatible` consumes. -/
theorem etaLink_eta :
    etaLink ((VExpr.const `MutField.foo []).mkApp []) ((VExpr.const `MutField.A.mk []).mkApp []) :=
  .inr (.inl ⟨rfl, rfl⟩)

/-- Non-degeneracy, the second half: the pair it relates is a pair of *distinct* terms, so
`etaLink` is not equality in disguise. -/
theorem etaLink_nontrivial :
    (VExpr.const `MutField.foo [] : VExpr) ≠ .const `MutField.A.mk [] := by simp

/-- **`etaLink` satisfies the `¬ StructInhab`-guarded no-confusion at `unitEnv`.**

Together with `etaLink_eta` this is the compatibility statement: a relation satisfying structure
eta *and* guarded const-head no-confusion exists, so the guarded row is not refuted by
`StructEtaPrice.lean` §6's argument. -/
theorem etaLink_guarded_noConf {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr}
    (hg : ¬ unitEnv.StructInhab 0 [] ((VExpr.const c ls).mkApp as))
    (h : etaLink ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')) : c = c' := by
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact (VExpr.constApp_inj h).1
  · obtain ⟨rfl, heq⟩ := VExpr.mkApp_eq_of_not_app as _ _ h nofun
    injection heq with hc hl; subst hc; subst hl
    exact absurd unitEnv_structInhab_foo hg
  · obtain ⟨rfl, heq⟩ := VExpr.mkApp_eq_of_not_app as _ _ h nofun
    injection heq with hc hl; subst hc; subst hl
    exact absurd unitEnv_structInhab_Amk hg

/-- **…and it does *not* satisfy the `¬ IsProof`-guarded no-confusion.**  One relation, two
guards, opposite answers: this is the sharpest form of "what eta kills is the `¬ IsProof` row".

Tainted exactly as `StructEtaPrice.lean` §6 is, and through the same single hole: the only input
is `MutField.unitEnv_not_isProof_foo`. -/
theorem etaLink_not_notIsProof_guarded :
    ¬ ∀ {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      ¬ unitEnv.IsProof 0 [] ((VExpr.const c ls).mkApp as) →
      etaLink ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as') → c = c' := fun H =>
  absurd (H (c := `MutField.foo) (c' := `MutField.A.mk) (ls := []) (ls' := [])
    (as := []) (as' := []) unitEnv_not_isProof_foo etaLink_eta) (by decide)

end MutField

/-! ## 4. The repaired statement, and that it still serves the 156

`ConstAppInvSI` is `VEnv.IsDefEq.constApp_inv`'s statement with **one guard added** and nothing
else changed: `¬ IsProof` stays (it blocks `proofIrrel`), `¬ StructInhab` joins it (it blocks
`structEta`).  `ConstAppInvSI.of_isType` is then `VEnv.constApp_inv_of_wf`'s type, character for
character, derived from it — so every consumer that supplies `IsType`, which is every consumer in
the tree, is served unchanged.

Measured this round (`scripts/users.lean` and a reverse-graph cut, 2026-09-03 17:39–17:46 UTC):
`IsDefEq.constApp_inv` has 4 direct / 187 transitive users, and **cutting the single lemma
`VEnv.IsStructure.spine_inv` (`Verify/Typing/ProjSpineInv.lean:57`) leaves 31**.  So 156 of the
187 reach no-confusion only through that one lemma, whose own no-confusion argument is
`constApp_inv_of_wf` applied to `ht₁.isType henv hΓ` — an `IsType`.  `spine_inv_of_si` below
re-derives it from `ConstAppInvSI`, which is the whole re-basing cost for those 156. -/

namespace VEnv

/-- **The repaired Params-level statement.**  `VEnv.IsDefEq.constApp_inv`'s conclusion — (B)
injectivity *and* (D) no-confusion — under one extra guard. -/
def ConstAppInvSI (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c c' : Lean.Name) (ls ls' : List VLevel) (as as' : List VExpr),
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → env.RuleFreeHead c' →
    ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as) →
    ¬ env.StructInhab U Γ ((VExpr.const c ls).mkApp as) →
    env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'

/-- **The repaired statement delivers `constApp_inv_of_wf`'s conclusion.**  Type identical to
`VEnv.constApp_inv_of_wf`'s (`Verify/Typing/ConstSpineWF.lean:61`) apart from the two extra
hypotheses `HSI` and `hrf`; the `IsType` guard discharges *both* new-style guards, `¬ IsProof` by
`IsType.not_isProof` (as today) and `¬ StructInhab` by §2. -/
theorem ConstAppInvSI.of_isType {env : VEnv} {U : Nat} (H : env.ConstAppInvSI U) (henv : env.WF)
    (hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) {c c' : Lean.Name} {ls ls' : List VLevel}
    {as as' : List VExpr} (hc : env.RuleFreeHead c) (hc' : env.RuleFreeHead c')
    (hty : env.IsType U Γ ((VExpr.const c ls).mkApp as))
    (h : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')) :
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' :=
  H Γ c c' ls ls' as as' hΓ hc hc' (IsType.not_isProof henv hΓ hty)
    (notStructInhab_of_isType henv hΓ hrf hty) h

/-- …and hence `VEnv.ConstNoConf` (`Verify/Typing/Rigidity.lean:151`) itself, unchanged. -/
theorem ConstAppInvSI.constNoConf {env : VEnv} {U : Nat} (H : env.ConstAppInvSI U)
    (henv : env.WF) (hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S) :
    env.ConstNoConf U :=
  fun _ _ _ _ _ _ _ hΓ hc hc' hty h => (H.of_isType henv hrf hΓ hc hc' hty h).1

end VEnv

/-- **The one load-bearing consumer, re-derived.**  `VEnv.IsStructure.spine_inv`'s type verbatim
(`Verify/Typing/ProjSpineInv.lean:57`), its proof with `constApp_inv_of_wf` replaced by
`ConstAppInvSI`.  156 of the 187 transitive users of `IsDefEq.constApp_inv` reach it only through
this lemma, so this line is what says they survive the repair. -/
theorem VEnv.IsStructure.spine_inv_of_si {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S₁ S₂ : Lean.Name} {D₁ D₂ : VInductDecl'} {T₁ T₂ : VIndType} {C₁ C₂ : VIndCtor}
    {us₁ us₂ : List VLevel} {as₁ as₂ : List VExpr} {e₁ e₂ : VExpr}
    (henv : env.WF) (hrf : ∀ S D j T C, env.IsStructureG S D j T C → env.RuleFreeHead S)
    (HSI : env.ConstAppInvSI U) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsStructure S₁ D₁ T₁ C₁) (h₂ : env.IsStructure S₂ D₂ T₂ C₂)
    (ht₁ : env.HasType U Γ e₁ ((VExpr.const S₁ us₁).mkApp as₁))
    (ht₂ : env.HasType U Γ e₂ ((VExpr.const S₂ us₂).mkApp as₂))
    (H : env.IsDefEqU U Γ e₁ e₂) :
    S₁ = S₂ ∧ List.Forall₂ (· ≈ ·) us₁ us₂ ∧ List.Forall₂ (env.IsDefEqU U Γ) as₁ as₂ :=
  HSI.of_isType henv hrf hΓ (h₁.ruleFreeHead henv) (h₂.ruleFreeHead henv)
    (ht₁.isType henv hΓ) ((H.of_l henv hΓ ht₁).uniqU henv hΓ ht₂)


/-! ## 5. Two guards that do not survive, refuted at a well-formed environment

`MutField.unitEnv` has exactly one non-constructor inhabitant of its zero-field member, and no
constant inhabitant at all of its one-field member `B`.  Both refutations below need one more
inhabitant, so `bigEnv` is `unitEnv` plus two `axiom` steps — `foo2 : A` and `bar : B` — with
`VEnv.WF` proved from `VEnv.empty` by the same four-step chain `MutField.unitEnv_wf` uses.

Nothing about the two new axioms is special: they are the *cheapest* legal inhabitants, exactly as
`fooC` is. -/

namespace MutField

/-- A second axiom inhabitant of the zero-field member. -/
def foo2C : VConstVal where
  uvars := 0
  type := .const `MutField.A []
  name := `MutField.foo2

/-- An axiom inhabitant of the **one-field** member. -/
def barC : VConstVal where
  uvars := 0
  type := .const `MutField.B []
  name := `MutField.bar

theorem twoEnv_eq : ∃ e,
    ((VEnv.empty.addInduct' decl).bind
      (fun env => env.addConst fooC.name fooC.toVConstant)).bind
      (fun env => env.addConst foo2C.name foo2C.toVConstant) = some e := ⟨_, rfl⟩

noncomputable def twoEnv : VEnv := twoEnv_eq.choose

theorem unitEnv_addConst_foo2 :
    unitEnv.addConst foo2C.name foo2C.toVConstant = some twoEnv :=
  (congrArg (fun o : Option VEnv =>
      o.bind fun env => env.addConst foo2C.name foo2C.toVConstant)
    unitEnv_eq.choose_spec.symm).trans twoEnv_eq.choose_spec

theorem bigEnv_eq : ∃ e,
    (((VEnv.empty.addInduct' decl).bind
      (fun env => env.addConst fooC.name fooC.toVConstant)).bind
      (fun env => env.addConst foo2C.name foo2C.toVConstant)).bind
      (fun env => env.addConst barC.name barC.toVConstant) = some e := ⟨_, rfl⟩

/-- **`unitEnv` plus `foo2 : A` plus `bar : B`.** -/
noncomputable def bigEnv : VEnv := bigEnv_eq.choose

theorem twoEnv_addConst_bar :
    twoEnv.addConst barC.name barC.toVConstant = some bigEnv :=
  (congrArg (fun o : Option VEnv =>
      o.bind fun env => env.addConst barC.name barC.toVConstant)
    twoEnv_eq.choose_spec.symm).trans bigEnv_eq.choose_spec

theorem unitEnv_le_twoEnv : unitEnv ≤ twoEnv := VEnv.addConst_le unitEnv_addConst_foo2
theorem twoEnv_le_bigEnv : twoEnv ≤ bigEnv := VEnv.addConst_le twoEnv_addConst_bar
theorem unitEnv_le_bigEnv : unitEnv ≤ bigEnv :=
  VEnv.LE.trans unitEnv_le_twoEnv twoEnv_le_bigEnv
theorem declEnv_le_bigEnv : declEnv ≤ bigEnv :=
  VEnv.LE.trans declEnv_le_unitEnv unitEnv_le_bigEnv

theorem unitEnv_A_isType : unitEnv.IsType 0 [] (.const `MutField.A []) := ⟨_, unitEnv_A_hasType⟩

theorem unitEnv_B_hasType :
    unitEnv.HasType 0 [] (VExpr.const `MutField.B []) (.sort (.succ .zero)) :=
  .constDF (declEnv_le_unitEnv.constants declEnv_B) nofun nofun rfl .nil

theorem twoEnv_B_isType : twoEnv.IsType 0 [] (.const `MutField.B []) :=
  ⟨_, unitEnv_B_hasType.mono unitEnv_le_twoEnv⟩

/-- **`bigEnv` is well formed** — four declaration steps from `VEnv.empty`, one `.induct` and
three `.axiom`.  So §5's refutations are refutations at a legitimate environment. -/
theorem bigEnv_wf : VEnv.WF bigEnv :=
  ⟨[.axiom barC, .axiom foo2C, .axiom fooC, .induct decl],
    .decl (.axiom twoEnv_B_isType twoEnv_addConst_bar)
      (.decl (.axiom unitEnv_A_isType unitEnv_addConst_foo2)
        (.decl (.axiom declEnv_A_isType declEnv_addConst)
          (.decl (.induct decl_WF declEnv_eq.choose_spec) .empty)))⟩

theorem twoEnv_foo2 : twoEnv.constants `MutField.foo2 = some ⟨0, .const `MutField.A []⟩ := by
  rw [VEnv.addConst_constants_eq unitEnv_addConst_foo2]; simp [foo2C]

theorem bigEnv_foo2 : bigEnv.constants `MutField.foo2 = some ⟨0, .const `MutField.A []⟩ :=
  twoEnv_le_bigEnv.constants twoEnv_foo2

theorem bigEnv_bar : bigEnv.constants `MutField.bar = some ⟨0, .const `MutField.B []⟩ := by
  rw [VEnv.addConst_constants_eq twoEnv_addConst_bar]; simp [barC]

theorem bigEnv_foo_hasType :
    bigEnv.HasType 0 [] ((VExpr.const `MutField.foo []).mkApp [])
      ((VExpr.const `MutField.A []).mkApp []) :=
  unitEnv_foo_hasType.mono unitEnv_le_bigEnv

theorem bigEnv_foo2_hasType :
    bigEnv.HasType 0 [] ((VExpr.const `MutField.foo2 []).mkApp [])
      ((VExpr.const `MutField.A []).mkApp []) :=
  .constDF bigEnv_foo2 nofun nofun rfl .nil

theorem bigEnv_bar_hasType :
    bigEnv.HasType 0 [] ((VExpr.const `MutField.bar []).mkApp [])
      ((VExpr.const `MutField.B []).mkApp []) :=
  .constDF bigEnv_bar nofun nofun rfl .nil

theorem bigEnv_A_hasType :
    bigEnv.HasType 0 [] (VExpr.const `MutField.A []) (.sort (.succ .zero)) :=
  unitEnv_A_hasType.mono unitEnv_le_bigEnv

theorem bigEnv_B_hasType :
    bigEnv.HasType 0 [] (VExpr.const `MutField.B []) (.sort (.succ .zero)) :=
  unitEnv_B_hasType.mono unitEnv_le_bigEnv

theorem bigEnv_defeqs {df : VDefEq} (h : bigEnv.defeqs df) : unitEnv.defeqs df := by
  rwa [VEnv.addConst_defeqs twoEnv_addConst_bar,
    VEnv.addConst_defeqs unitEnv_addConst_foo2] at h

theorem bigEnv_ruleFreeHead {c : Lean.Name}
    (h1 : c ≠ `MutField.A.rec) (h2 : c ≠ `MutField.B.rec) : bigEnv.RuleFreeHead c :=
  fun df hdf => unitEnv_ruleFreeHead h1 h2 df (bigEnv_defeqs hdf)

theorem bigEnv_IsStructureG_A : bigEnv.IsStructureG `MutField.A decl 0 aTy aCtor :=
  unitEnv_IsStructureG_0.mono unitEnv_le_bigEnv

theorem bigEnv_IsStructureG_B : bigEnv.IsStructureG `MutField.B decl 1 bTy bCtor :=
  declEnv_IsStructureG.mono declEnv_le_bigEnv

/-! ### The three firings

Two at the zero-field member with distinct axiom inhabitants, one at the **one-field** member.
All three are instances of `VEnv.structEtaGSE`, i.e. of the fourteenth constructor. -/

theorem bigEnv_structEtaSE_foo :
    bigEnv.IsDefEqSE 0 [] (.const `MutField.foo []) (.const `MutField.A.mk [])
      (.const `MutField.A []) := by
  have h := VEnv.structEtaGSE bigEnv (U := 0) (Γ := []) (us := []) (ps := [])
    bigEnv_IsStructureG_A rfl rfl rfl nofun rfl .nil bigEnv_foo_hasType (.inr (by simp [aCtor]))
  rwa [decl.etaExpansionG_of_no_fields aTy aCtor [] rfl] at h

theorem bigEnv_structEtaSE_foo2 :
    bigEnv.IsDefEqSE 0 [] (.const `MutField.foo2 []) (.const `MutField.A.mk [])
      (.const `MutField.A []) := by
  have h := VEnv.structEtaGSE bigEnv (U := 0) (Γ := []) (us := []) (ps := [])
    bigEnv_IsStructureG_A rfl rfl rfl nofun rfl .nil bigEnv_foo2_hasType (.inr (by simp [aCtor]))
  rwa [decl.etaExpansionG_of_no_fields aTy aCtor [] rfl] at h

/-- **The one-field firing, at a constant inhabitant.**  `MutField.structEtaSE_B` fires the same
rule at a *free variable*, which cannot carry a head-confusion; this fires it at an axiom, and the
right-hand side is a `const`-headed spine with head `B.mk` and one genuine `projTermG` argument
(`MutField.declEnv_etaExpansionG_eq` is the same computation in the tree). -/
theorem bigEnv_structEtaSE_bar :
    bigEnv.IsDefEqSE 0 [] ((VExpr.const `MutField.bar []).mkApp [])
      ((VExpr.const `MutField.B.mk []).mkApp
        [decl.projTermG bTy bCtor [] [] [] 0 1 (.const `MutField.bar [])])
      ((VExpr.const `MutField.B []).mkApp []) :=
  VEnv.structEtaGSE bigEnv (U := 0) (Γ := []) (us := []) (ps := [])
    bigEnv_IsStructureG_B rfl rfl rfl nofun rfl .nil bigEnv_bar_hasType (.inr bCtor_field_prop)

end MutField

/-! ### Refutation 1: no guard on the *head* can work, because of transitivity

This is the trap in "exempt structure constructors".  `guard_rejects_an_axiom` is stated for an
arbitrary guard predicate `G` on head names, and concludes that `G` must **reject one of the two
axioms** — neither of which is a constructor.  So a side condition that only exempts constructor
heads cannot repair no-confusion, and neither can any other condition on the head alone that is
satisfied by plain axioms. -/

/-- **Any head-guard that repairs no-confusion must reject an axiom inhabitant.**

`R` is arbitrary apart from `symm` and `trans`, which the relation must have (`VEnv.IsDefEq` and
`VEnv.IsDefEqSE` both have them as constructors), and the two eta instances, which
`MutField.bigEnv_structEtaSE_foo` and `_foo2` supply.  `RuleFreeHead` and `¬ IsProof` are carried
inside `G`'s two instantiations below, so this covers the real statement's guards too. -/
theorem guard_rejects_an_axiom (R : VExpr → VExpr → Prop) (G : Lean.Name → Prop)
    (hsymm : ∀ {a b : VExpr}, R a b → R b a)
    (htrans : ∀ {a b c : VExpr}, R a b → R b c → R a c)
    (hEta1 : R (.const `MutField.foo []) (.const `MutField.A.mk []))
    (hEta2 : R (.const `MutField.foo2 []) (.const `MutField.A.mk []))
    (hNC : ∀ {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      G c → G c' → R ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as') → c = c') :
    ¬ G `MutField.foo ∨ ¬ G `MutField.foo2 := by
  by_contra h
  simp only [not_or, not_not] at h
  exact absurd (hNC (ls := []) (ls' := []) (as := []) (as' := []) h.1 h.2
    (htrans hEta1 (hsymm hEta2))) (by decide)

/-- **"Exempt the structure constructor" is refuted for the fourteen-constructor relation.**

The guard is `c ≠ A.mk`, which both axioms satisfy by computation; the pair that violates
no-confusion is `foo ≡ foo2`, obtained from the two eta instances by `symm` and `trans` — so the
constructor never appears in the violating pair at all.  `RuleFreeHead` is in the guard and
discharged; the environment is `MutField.bigEnv`, whose `VEnv.WF` is proved. -/
theorem exemptingCtorNoConf_false_for_IsDefEqSE :
    ¬ ∀ {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      MutField.bigEnv.RuleFreeHead c → MutField.bigEnv.RuleFreeHead c' →
      c ≠ `MutField.A.mk → c' ≠ `MutField.A.mk →
      MutField.bigEnv.IsDefEqSE 0 [] ((VExpr.const c ls).mkApp as)
        ((VExpr.const c' ls').mkApp as') (.const `MutField.A []) → c = c' := by
  intro H
  rcases guard_rejects_an_axiom
      (fun a b => MutField.bigEnv.IsDefEqSE 0 [] a b (.const `MutField.A []))
      (fun c => c ≠ `MutField.A.mk ∧ ¬ c = `MutField.A.rec ∧ ¬ c = `MutField.B.rec)
      (fun h => h.symm) (fun h h' => h.trans h')
      MutField.bigEnv_structEtaSE_foo MutField.bigEnv_structEtaSE_foo2
      (fun hg hg' h => H (MutField.bigEnv_ruleFreeHead hg.2.1 hg.2.2)
        (MutField.bigEnv_ruleFreeHead hg'.2.1 hg'.2.2) hg.1 hg'.1 h) with h | h
  · exact h ⟨by decide, by decide, by decide⟩
  · exact h ⟨by decide, by decide, by decide⟩

/-! ### Refutation 2: the field count is irrelevant

`StructEtaPrice.lean` §6's witness is a zero-field structure, which invites the guess that
unit-like types are the whole problem.  They are not: the same confusion happens at
`MutField.B`, whose constructor has one field (`MutField.bCtor_fields_length`), because the eta
output there is *also* a `const`-headed spine — headed by `B.mk`, with the projection as its
argument. -/

/-- **"Exempt only zero-field constructors" is refuted**, at a one-field structure in the same
mutual block, and without transitivity: one eta instance does it. -/
theorem zeroFieldOnlyNoConf_false_for_IsDefEqSE :
    ¬ ∀ {c c' : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr},
      MutField.bigEnv.RuleFreeHead c → MutField.bigEnv.RuleFreeHead c' →
      c ≠ `MutField.A.mk → c' ≠ `MutField.A.mk →
      MutField.bigEnv.IsDefEqSE 0 [] ((VExpr.const c ls).mkApp as)
        ((VExpr.const c' ls').mkApp as') ((VExpr.const `MutField.B []).mkApp []) → c = c' :=
  fun H => absurd
    (H (c := `MutField.bar) (c' := `MutField.B.mk) (ls := []) (ls' := [])
      (as := [])
      (as' := [MutField.decl.projTermG MutField.bTy MutField.bCtor [] [] [] 0 1
        (.const `MutField.bar [])])
      (MutField.bigEnv_ruleFreeHead (by decide) (by decide))
      (MutField.bigEnv_ruleFreeHead (by decide) (by decide)) (by decide) (by decide)
      MutField.bigEnv_structEtaSE_bar)
    (by decide)

/-- The field count at the second witness, so "positive field" is not a paraphrase. -/
theorem MutField.bCtor_has_a_field : MutField.bCtor.fields.length = 1 := rfl


/-! ## 6. What the repair still owes, and what it costs

### The residual

`ConstAppInvSI` is **not proved here for any relation with structure eta.**  Proving it is the
repair, and it is the whole Church–Rosser chain re-run with the new guard.  Two steps are new; the
rest is the existing proof unchanged.

1. `ParRed.constApp_inv` (`Verify/Typing/ConstSpine.lean:115`) gains an eta case.  A top-level eta
   step on a `const`-headed spine changes the head, so the case must be closed by the guard: the
   redex is a structure inhabitant, and `¬ StructInhab` excludes it.  Eta *inside an argument* is
   already covered — the conclusion only asserts pointwise reduction of the arguments.
2. `NormalEq.constApp_inv` (`ConstSpine.lean:186`) gains an eta case, at the top only.  Its
   `appDF` case must now thread `¬ StructInhab` as well as `¬ IsProof`; §2's
   `notStructInhab_of_forallE` is that step, and unlike `IsProof.app'` it does not *inherit* the
   guard from the larger spine — it re-establishes it from the sub-spine's Π type.  So the
   threading is strictly easier than the one already written.

`IsDefEq.constApp_inv`'s own proof body then goes through verbatim with the extra guard
transported across the reduction (`hnp'` in the existing proof does exactly this for `¬ IsProof`,
via `IsProof.defeqU`; the analogue is `StructInhab` transport along `IsDefEqU`, which is
`HasType.defeqU_l'` and nothing more).

### Three named gaps, measured this round

(i) **`IsStructureG.ruleFreeHead` does not exist.**  `VEnv.IsStructure.ruleFreeHead`
(`Theory/Typing/StructureRuleFree.lean:128`) proves `RuleFreeHead S` from `VEnv.WF` and the
*narrow* predicate; nothing in the tree concludes anything mentioning both `VEnv.IsStructureG` and
`VEnv.RuleFreeHead` (`scripts/shape.lean`, 2026-09-03: 0 hits, heads resolved).  Both §2 lemmas
therefore carry `hrf` as a hypothesis.  At a concrete environment it is a computation
(`MutField.unitEnv_ruleFreeHead`, `MutField.bigEnv_ruleFreeHead`), which is why §3's concrete
results do not carry it.  The general version needs `IsStructure.ruleFreeHead`'s proof with
`henv.iotaTypeNotKey D 0 0` replaced by `henv.iotaTypeNotKey D j 0` — the block index is already a
parameter of that lemma.

(ii) **`StructInhab` transport along `IsDefEqU`** is not stated.  It is `HasType.defeqU_l'`
applied inside the existential, i.e. three lines; it is listed because step 1's guard transport
needs it by name.

(iii) **The `¬ IsProof` guard does not go away.**  `Verify/Typing/NoConfGuard.lean`'s
`not_constNoConfUG_ncPropEnv` refutes no-confusion with the guards deleted, by `proofIrrel`, at a
`VEnv.WF` environment with no rules at all.  So the repaired statement carries *both* guards, and
anyone reading §3's `etaLink_not_notIsProof_guarded` as "drop `¬ IsProof`, keep `¬ StructInhab`"
has it backwards: `etaLink` satisfies the guarded row because its *only* non-reflexive pair is
excluded, and a relation containing `ncPropEnv`'s `proofIrrel` pair would not.

### The re-basing cost, measured 2026-09-03 17:39–17:46 UTC

`scripts/users.lean` plus a reverse-dependency cut over the same 427-module population:

| target | direct | transitive |
|---|---|---|
| `VEnv.IsDefEq.constApp_inv` | 4 | 187 |
| …with `VEnv.IsStructure.spine_inv` cut out of the graph | — | **31** |

All four direct users are *re-wrappers* of the same statement
(`constNoConfNP_of_patWF`, `constApp_inv_np_of_patWF`, `constApp_inv_of_patWF`,
`constNoConf_of_notIsProof`), so the direct count measures nothing about need.  The 31 that survive
the cut live in six modules, all of which are *about* no-confusion rather than consumers of it:
`NoConfGuard` 12, `EtaUnitRefute` 5, `EtaUnitClose` 4, `ConstSpineWF` 4, `Rigidity` 3,
`ConstSpine` 3.  The other **156 reach no-confusion only through `VEnv.IsStructure.spine_inv`**,
which supplies `IsType` and is re-derived above (`spine_inv_of_si`).

Both `addAxiom.WF` and `addDecl.WF` are transitive users, and their paths land on the same lemma:

    addAxiom.WF ← checkConstantVal.WF ← checkConstantValCore.WF ← TypeChecker.checkType.WF
      ← RecM.WF.run ← Methods.withFuel.WF ← Inner.isDefEqCore'.WF ← TrExprS.uniq ← TrProj.uniq
      ← TrProj.uniq_of_projTermCongr ← IsStructure.spine_inv ← constApp_inv_of_wf
      ← constApp_inv_of_patWF ← IsDefEq.constApp_inv

`Theory/Typing/DescendConstSpineK.lean:16` records this chain as
`addAxiom.WF ← … ← constApp_inv_of_patWF ← IsDefEq.constApp_inv ← IsDefEq.church_rosser`; the
measurement above fills in the `…`, and the answer to "what does `addAxiom.WF` actually need" is:
**`IsStructure.spine_inv`, and nothing else from this family.**  `spine_inv` applies no-confusion
to the *types* of two terms — `(const S₁ us₁).mkApp as₁` and `(const S₂ us₂).mkApp as₂` — and its
guard argument is literally `ht₁.isType henv hΓ`.  Those spines are type formers applied to
parameters; the terms eta confuses are *inhabitants*.  So `addAxiom.WF` needs only the
`IsType`-guarded row, which is the row that survives, and `spine_inv_of_si` is the one lemma that
has to be rewritten for it.

`Lean4Lean.kernel_sound` is **not** a transitive user of `IsDefEq.constApp_inv` today (measured,
same run) — it reaches `addDecl.WF` through a different path or not yet at all, so no claim about
`kernel_sound` follows from this family's fate except through `addDecl.WF`, which *is* a user.

### Vacuity, both ways

*The exhibited relation is non-degenerate.*  A relation that relates nothing satisfies every
no-confusion statement and proves nothing.  `MutField.etaLink` is reflexive on all of `VExpr`
(`etaLink_refl`) and relates two *syntactically distinct* closed constants
(`etaLink_eta` with `etaLink_nontrivial`), so neither escape is available to it.

*The proposed guard is non-trivial.*  A guard satisfied by no real environment is not a repair.
`¬ StructInhab` is (a) genuinely restrictive — it is **false** at the two terms eta confuses
(`unitEnv_structInhab_foo`, `unitEnv_structInhab_Amk`, both hole-free), which is what makes it a
guard rather than decoration; and (b) genuinely available — it is implied by `IsType`
(`notStructInhab_of_isType`), which is the hypothesis every consumer site in the tree actually
supplies, and `spine_inv_of_si` is that discharge run at the one site the other 156 users go
through.  What is *not* proved here is the unconditional "every type-valued spine of every
well-formed environment satisfies the guard": that is gap (i) and nothing more.

*The refutations are at a real environment.*  `MutField.bigEnv` is `VEnv.WF` from `VEnv.empty`
(`bigEnv_wf`), holds a genuine two-type mutual inductive block in `Type` with a zero-field and a
one-field member, and all three eta instances §5 uses are firings of the fourteenth constructor at
it — not hypotheses.

### Axiom bar

`after ⊆ before`.  `before` is the four census holes `IsDefEq.constApp_inv`'s cone already reaches:
`IsDefEqU.weakN_iff`, `IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`,
`NormalEq.descend`.

The `#print axioms` block below is the measurement of *whether* `sorryAx` is reached.  **Everything
in §5 — the environment, its `VEnv.WF`, all three eta firings, `guard_rejects_an_axiom` and both
refutations — is `sorryAx`-free**, which makes those two refutations *stronger* than
`StructEtaPrice.lean` §6's, which is tainted.  So are `structEta_lhs_structInhabAt`, both
`unitEnv_structInhab_*`, and every `etaLink` lemma except the last.

Cones and hole sets, measured by `scripts/exists.lean` after building this module (429-module
population, 2026-09-03 18:06 UTC):

| declaration | cone | holes |
|---|---|---|
| `StructInhab`, `structEta_lhs_structInhabAt` | 84 | none |
| `ConstAppInvSI` | 633 | none |
| `guard_rejects_an_axiom` | 382 | none |
| `MutField.bigEnv_wf` | 3910 | none |
| `MutField.bigEnv_structEtaSE_bar` | 3944 | none |
| `MutField.etaLink_guarded_noConf` | 3904 | none |
| `zeroFieldOnlyNoConf_false_for_IsDefEqSE` | 3979 | none |
| `exemptingCtorNoConf_false_for_IsDefEqSE` | 4282 | none |
| `notStructInhab_of_isType` | 7479 | the four |
| `notStructInhab_of_forallE`, `ConstAppInvSI.of_isType` | 7481 | the four |
| `IsStructure.spine_inv_of_si` | 7528 | the four |
| `MutField.unitEnv_not_isType_foo` | 7535 | the four |

`after ⊆ before` on every line, and the load-bearing one is *smaller* than what it replaces: the
tree's `VEnv.IsStructure.spine_inv` has cone 7538 at the same four holes, `spine_inv_of_si` 7528.

No root import edit was needed: `lakefile.toml` globs `Lean4Lean.Theory.*`.

A correction to that file's §9 while it is in view: it says `MutField.structEtaSE_foo` "inherits
`sorryAx` … through the same four census holes".  Measured (`scripts/exists.lean`, this round)
`structEtaSE_foo`'s cone does **not** reach `sorryAx` at all, and
`eta_and_constNoConf_incompatible`'s reaches exactly **one** hole, `forallE_inv_stratified`, not
four. -/

section Audit
#print axioms Lean4Lean.VEnv.structEta_lhs_structInhabAt
#print axioms Lean4Lean.VEnv.notStructInhab_of_isType
#print axioms Lean4Lean.VEnv.notStructInhab_of_forallE
#print axioms Lean4Lean.MutField.unitEnv_structInhab_foo
#print axioms Lean4Lean.MutField.unitEnv_structInhab_Amk
#print axioms Lean4Lean.MutField.unitEnv_not_isType_foo
#print axioms Lean4Lean.MutField.unitEnv_not_isType_Amk
#print axioms Lean4Lean.MutField.etaLink_eta
#print axioms Lean4Lean.MutField.etaLink_trans
#print axioms Lean4Lean.MutField.etaLink_guarded_noConf
#print axioms Lean4Lean.MutField.etaLink_not_notIsProof_guarded
#print axioms Lean4Lean.VEnv.ConstAppInvSI.of_isType
#print axioms Lean4Lean.VEnv.ConstAppInvSI.constNoConf
#print axioms Lean4Lean.VEnv.IsStructure.spine_inv_of_si
#print axioms Lean4Lean.MutField.bigEnv_wf
#print axioms Lean4Lean.MutField.bigEnv_structEtaSE_foo
#print axioms Lean4Lean.MutField.bigEnv_structEtaSE_foo2
#print axioms Lean4Lean.MutField.bigEnv_structEtaSE_bar
#print axioms Lean4Lean.guard_rejects_an_axiom
#print axioms Lean4Lean.exemptingCtorNoConf_false_for_IsDefEqSE
#print axioms Lean4Lean.zeroFieldOnlyNoConf_false_for_IsDefEqSE
end Audit

end Lean4Lean
