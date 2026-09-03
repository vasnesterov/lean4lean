import Lean4Lean.Theory.Typing.EtaGuardLand

/-!
# `ConstAppInvSIFromWF`, proved — and why that does **not** close the structure-eta repair

`Theory/Typing/EtaGuardLand.lean` §3 names

    ConstAppInvSIFromWF : Prop := ∀ (env : VEnv) (U : Nat), env.WF → env.ConstAppInvSI U

as "the one remaining premise" of the structure-eta repair, and `spineInvStmt_of_repair`
inhabits `SpineInvStmt` from it.  This file **proves** `ConstAppInvSIFromWF` (§1) and then shows,
with machine-checked statements rather than prose, that the proof buys **no eta coverage at all**
(§2–§3).  The reason is a relation mismatch, and it is worth stating precisely because
`NoConfRepair.lean` §6's own prose is right about the obligation while the *named `Prop`* is not:

* `NoConfRepair.lean` §6 says "`ConstAppInvSI` is **not proved here for any relation with
  structure eta**", and that is the real debt.
* But `VEnv.ConstAppInvSI` (`NoConfRepair.lean:292`) is stated over `env.IsDefEqU`, i.e. over
  `VEnv.IsDefEq` — the **thirteen**-constructor relation, which has **no** `structEta`
  constructor.  The fourteenth constructor lives in a *different* relation,
  `VEnv.IsDefEqSE` (`StructEtaPrice.lean:183`), and `ConstAppInvSI` never mentions it.

So `ConstAppInvSIFromWF` quantifies the pre-repair relation.  §1 discharges it from
`VEnv.IsDefEq.constApp_inv` — the Params-level lemma that already carries the `¬ IsProof` guard
and **no** `IsType` guard — composed with `VEnv.patWF_of_wf`.  The new `¬ StructInhab` guard is
never used; §2 proves that by proving the guard-free statement as well, and by an `↔` between the
two.

## Where the work actually is, and it is *not* where the brief said

The brief handed to this round located the work in "the two eta cases of `ConstSpine.lean`'s
no-confusion argument".  Read them (`Verify/Typing/ConstSpine.lean:220-221`):

    | etaL => rintro - - ls ls' as as' he₁ -; exact absurd he₁.symm VExpr.constApp_ne_lam
    | etaR => rintro - - ls ls' as as' - he₂; exact absurd he₂.symm VExpr.constApp_ne_lam

Those are **function** eta (`VEnv.NormalEq.etaL`/`etaR`), whose λ-side endpoint is a `.lam`.  Both
are discharged *by shape*, in one line each, by `VExpr.constApp_ne_lam`: a constant-headed spine
is never a λ.  Nothing in them needs anything, they are already free, and they stay free after the
repair — because **structure** eta is the case where *both* endpoints are constant spines
(`MutField.foo` versus `MutField.A.mk`), so `constApp_ne_lam` does not apply to it.

`VEnv.NormalEq` and `VEnv.ParRed` are built over the thirteen-constructor relation and have **no
`structEta` case at all**.  The two cases the repair has to write therefore *do not exist yet*:
they appear only once `NormalEq`, `ParRed` and `VEnv.IsDefEq.church_rosser` are re-erected over
`VEnv.IsDefEqSE`.  §3 states the obligation that is actually left.

## §3's finding: the guard, as currently defined, cannot discharge the case it was designed for

`VEnv.StructInhab` (`NoConfRepair.lean:102`) is `StructInhabAt` at `env.HasType U Γ` — the
**thirteen**-constructor typing judgement.  The `structEta` constructor's corresponding premise is
`env.IsDefEqSE U Γ e e ((const S us).mkApp ps)`, in the **fourteen**-constructor relation.  These
are not the same predicate, and nothing in the tree transports the second to the first (that would
be the SE-relation's own uniqueness-of-types theory, which does not exist).  So the guard that
actually blocks `structEta` is `StructInhabSE` (§3.1), not `StructInhab`; §3.2 proves in one line
that it does block it, via the deliberately `Ty`-generic
`VEnv.structEta_lhs_structInhabAt`.

## Taint discipline

§1 and §2 are `sorryAx`-tainted **by inheritance, at exactly the taint `VEnv.IsStructure.spine_inv`
already carries** — the four census holes `IsDefEqU.weakN_iff`,
`IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`, `NormalEq.descend`.  This is a
re-derivation at the same taint, not a hole-free result, and is labelled as such at each
statement.

§3 is **not** uniformly hole-free, and the first draft of this docstring said it was — corrected
after measurement.  §3.1 and §3.2 (`StructInhabSE`, `structEta_lhs_structInhabSE`,
`ConstAppInvSISE`) are hole-free; §3.3's refutation inherits **one** hole,
`VEnv.IsDefEqU.forallE_inv_stratified`, from `Lean4Lean.constNoConf_false_for_IsDefEqSE`
(cone 5584, same single hole) by way of `MutField.unitEnv_not_isProof_foo`.  §4.1 *is* hole-free
throughout, and that is the part it matters for: the eta guard's restrictiveness at both structure
shapes does not lean on the tainted family.
-/

namespace Lean4Lean

/-! ## 1. The target, proved

`VEnv.constNoConf_of_notIsProof` (`Verify/TypeChecker/EtaUnitRefute.lean`) already observed that
`constApp_inv_of_patWF`'s `IsType` premise is only ever discarded into `IsType.not_isProof`, and
took the `¬ IsProof` premise instead — but kept only the head equality.  `ConstAppInvSI` wants all
three components, and the Params-level lemma supplies all three, so the target is that same
observation with nothing thrown away. -/

/-- **`Lean4Lean.ConstAppInvSIFromWF` is a theorem.**

The `¬ StructInhab` argument is bound and discarded (`_hsi`): `VEnv.IsDefEq.constApp_inv`
(`Verify/Typing/ConstSpine.lean:248`) needs only `¬ IsProof`.  §2 makes that observation a
statement rather than a naming convention.

**Tainted by inheritance at the four census holes** `IsDefEqU.weakN_iff`,
`IsDefEqU.forallE_inv_stratified`, `WF.rigidShapeUniqNS`, `NormalEq.descend` — the same four
`VEnv.IsStructure.spine_inv` carries, so this adds nothing to the cone it is meant to serve. -/
theorem constAppInvSIFromWF : ConstAppInvSIFromWF :=
  fun env U henv Γ c c' ls ls' as as' hΓ hc hc' hnp _hsi H =>
    let hwf : env.PatWF U := VEnv.patWF_of_wf henv U
    let _inst := VEnv.paramsOfWF henv U hwf
    @VEnv.IsDefEq.constApp_inv _inst Γ c c' ls ls' as as' H.choose hΓ
      (hc.patFreeHead henv hwf) (hc'.patFreeHead henv hwf) hnp H.choose_spec

/-- The immediate corollary the 156 were said to need, spelled out so it can be compared with
`Lean4Lean.spineInvStmt_today` (which proves the same `Prop` **unconditionally**, and already did
before this round). -/
theorem spineInvStmt_of_constAppInvSIFromWF : SpineInvStmt :=
  spineInvStmt_of_repair constAppInvSIFromWF

/-! ## 2. The `¬ StructInhab` guard is not load-bearing in the target

This is the machine-checked form of "§1 buys no eta coverage": the *guard-free* statement is
provable by the same proof, so the target does not test the guard at all. -/

/-- `VEnv.ConstAppInvSI` with the `¬ StructInhab` premise **deleted** and nothing else changed.
This is `VEnv.constNoConf_of_notIsProof`'s hypothesis set with the full triple as conclusion. -/
def VEnv.ConstAppInvNoSI (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c c' : Lean.Name) (ls ls' : List VLevel) (as as' : List VExpr),
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → env.RuleFreeHead c' →
    ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as) →
    env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as'

/-- `ConstAppInvSIFromWF` with the guard deleted. -/
def ConstAppInvNoSIFromWF : Prop := ∀ (env : VEnv) (U : Nat), env.WF → env.ConstAppInvNoSI U

/-- **The guard-free statement is provable too**, by the identical proof — so `ConstAppInvSI`'s
extra premise is dead weight over `env.IsDefEqU`.

Tainted at the same four census holes as §1, for the same reason. -/
theorem constAppInvNoSIFromWF : ConstAppInvNoSIFromWF :=
  fun env U henv Γ c c' ls ls' as as' hΓ hc hc' hnp H =>
    let hwf : env.PatWF U := VEnv.patWF_of_wf henv U
    let _inst := VEnv.paramsOfWF henv U hwf
    @VEnv.IsDefEq.constApp_inv _inst Γ c c' ls ls' as as' H.choose hΓ
      (hc.patFreeHead henv hwf) (hc'.patFreeHead henv hwf) hnp H.choose_spec

/-- Premise-dropping, at an arbitrary environment and with no well-formedness: the guard-free
statement is genuinely *stronger*.  This direction is hole-free and unconditional; it is the half
that shows §2's theorem is not weaker than §1's. -/
theorem VEnv.ConstAppInvNoSI.constAppInvSI {env : VEnv} {U : Nat} (H : env.ConstAppInvNoSI U) :
    env.ConstAppInvSI U :=
  fun Γ c c' ls ls' as as' hΓ hc hc' hnp _ h => H Γ c c' ls ls' as as' hΓ hc hc' hnp h

/-- **The `↔` asked for, with its information content stated at the statement so it is not
oversold.**  Both sides are theorems (§1, §2), so the equivalence carries no information *beyond*
that fact; the informative half is `constAppInvNoSIFromWF`, i.e. that the guard can be deleted.
The forward direction is recorded as `⟨_, constAppInvNoSIFromWF⟩` rather than as a derivation
*from* `ConstAppInvSIFromWF` precisely because no such derivation exists — one cannot recover the
unguarded statement from the guarded one, and §3.3 is the reason that matters.

Tainted at the same four census holes. -/
theorem constAppInvSIFromWF_iff_unguarded : ConstAppInvSIFromWF ↔ ConstAppInvNoSIFromWF :=
  ⟨fun _ => constAppInvNoSIFromWF,
   fun H env U henv => (H env U henv).constAppInvSI⟩

/-! ## 3. The obligation that is actually left, stated over the fourteen-constructor relation

§3.1 and §3.2 are hole-free; §3.3 carries one inherited hole, stated at its two theorems. -/

/-- `VEnv.IsDefEqU` for the fourteen-constructor relation. -/
def VEnv.IsDefEqUSE (env : VEnv) (U : Nat) (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  ∃ A, env.IsDefEqSE U Γ e₁ e₂ A

/-! ### §3.1 The guard the `structEta` case can actually use -/

/-- **`VEnv.StructInhab` transposed to the fourteenth constructor's own relation.**

`VEnv.StructInhab` is `StructInhabAt` at `env.HasType U Γ`, i.e. at `VEnv.IsDefEq`.  The
`structEta` constructor's eighth premise is `env.IsDefEqSE U Γ e e ((const S us).mkApp ps)`.
`VEnv.structEta_lhs_structInhabAt` was deliberately stated with an arbitrary `Ty` so that both
instantiations are available; this is the second one. -/
def VEnv.StructInhabSE (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  env.StructInhabAt (fun e A => env.IsDefEqSE U Γ e e A) e

/-- **The `structEta` case *is* blocked — by `¬ StructInhabSE`.**  One line, hole-free, and it
consumes exactly the first, second, third and eighth premises of the constructor.  This is the
positive half of §3: the guard's *design* is correct, it is its *definition* that is at the wrong
relation. -/
theorem VEnv.structEta_lhs_structInhabSE {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Lean.Name}
    {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    {ps : List VExpr} {e : VExpr}
    (hS : env.IsStructureG S D j T C) (hidx : T.indices = []) (hrec : C.recFields = [])
    (he : env.IsDefEqSE U Γ e e ((VExpr.const S us).mkApp ps)) : env.StructInhabSE U Γ e :=
  structEta_lhs_structInhabAt hS hidx hrec he

/-! ### §3.2 The statement the repair actually owes -/

/-- **`VEnv.ConstAppInvSI` at the fourteen-constructor relation**, with the guard likewise moved
(§3.1).  Every other premise and the conclusion's shape are `ConstAppInvSI`'s verbatim, with
`IsDefEqU` replaced by `IsDefEqUSE` and `StructInhab` by `StructInhabSE`.

This — not `Lean4Lean.ConstAppInvSIFromWF` — is what "the eta repair" reduces to. -/
def VEnv.ConstAppInvSISE (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c c' : Lean.Name) (ls ls' : List VLevel) (as as' : List VExpr),
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → env.RuleFreeHead c' →
    ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as) →
    ¬ env.StructInhabSE U Γ ((VExpr.const c ls).mkApp as) →
    env.IsDefEqUSE U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqUSE U Γ) as as'

/-- The `WF`-level form, to be compared with `Lean4Lean.ConstAppInvSIFromWF`. -/
def ConstAppInvSISEFromWF : Prop := ∀ (env : VEnv) (U : Nat), env.WF → env.ConstAppInvSISE U

/-- `ConstAppInvSISE` with the eta guard deleted — the SE analogue of §2's `ConstAppInvNoSI`. -/
def VEnv.ConstAppInvNoSISE (env : VEnv) (U : Nat) : Prop :=
  ∀ (Γ : List VExpr) (c c' : Lean.Name) (ls ls' : List VLevel) (as as' : List VExpr),
    OnCtx Γ (env.IsType U) → env.RuleFreeHead c → env.RuleFreeHead c' →
    ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as) →
    env.IsDefEqUSE U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqUSE U Γ) as as'

/-! ### §3.3 The separation: §2 is true, its SE twin is FALSE

This pair is the whole content of the round's negative finding.  The *same* premise set —
`RuleFreeHead`, `RuleFreeHead`, `¬ IsProof`, no eta guard — is a **theorem** at every well-formed
environment over `IsDefEqU` (§2) and is **refuted** at a well-formed environment over
`IsDefEqSE`.  Hence no amount of work on §1's statement can bear on the repair: the two statements
have opposite truth values. -/

/-- **The guard-free SE statement is false at `MutField.unitEnv`.**  Reduction to
`Lean4Lean.constNoConf_false_for_IsDefEqSE`, whose witness is `MutField.structEtaSE_foo`.

**Tainted at one hole**, `VEnv.IsDefEqU.forallE_inv_stratified` — inherited, not incurred: it is
`constNoConf_false_for_IsDefEqSE`'s own single hole (cone 5584), which reaches it through
`MutField.unitEnv_not_isProof_foo`'s universe-uniqueness step.  Recorded at the statement because
the weaker claim "hole-free" was written here before it was measured, and was wrong. -/
theorem VEnv.constAppInvNoSISE_false_unitEnv :
    ¬ MutField.unitEnv.ConstAppInvNoSISE 0 := fun H =>
  constNoConf_false_for_IsDefEqSE
    fun h1 h2 h3 h4 => (H [] _ _ _ _ _ _ trivial h1 h2 h3 h4).1

/-- **The separation in one statement.**  Left: §2 at `unitEnv`, which `constAppInvNoSIFromWF`
supplies (tainted at the four census holes).  Right: §3.3, itself tainted at
`VEnv.IsDefEqU.forallE_inv_stratified`.  So `ConstAppInvNoSI` and
`ConstAppInvNoSISE` are not variants of one statement — they disagree at a single environment.

Tainted at the four census holes, via the left conjunct only. -/
theorem MutField.unitEnv_noSI_true_but_SE_false :
    MutField.unitEnv.ConstAppInvNoSI 0 ∧ ¬ MutField.unitEnv.ConstAppInvNoSISE 0 :=
  ⟨constAppInvNoSIFromWF _ 0 unitEnv_wf, VEnv.constAppInvNoSISE_false_unitEnv⟩

/-! ## 4. Vacuity of the eta guard, both ways, at both structure shapes

`docs/vacuity-ledger.md` §0's discipline.  Two failure modes: a guard no real environment
satisfies is not a repair; a guard every term satisfies is not a guard.  The brief additionally
requires a **positive-field** structure, because `Lean4Lean.zeroFieldOnlyNoConf_false_for_IsDefEqSE`
shows the failure is not zero-field-only. -/

namespace MutField

/-! ### §4.1 The SE guard is restrictive — it fails exactly at the eta endpoints

Each of these is `structEta_lhs_structInhabSE` (§3.1) applied to a `HasType`, pushed into the
fourteen-constructor relation by `VEnv.IsDefEq.toSE`.  All hole-free. -/

/-- **Zero-field shape.**  `foo` is an axiom inhabitant of `MutField.A`, whose constructor has no
fields; the `structEta` instance at it is `MutField.structEtaSE_foo`, and the guard excludes it. -/
theorem unitEnv_structInhabSE_foo :
    unitEnv.StructInhabSE 0 [] ((VExpr.const `MutField.foo []).mkApp []) :=
  VEnv.structEta_lhs_structInhabSE (us := []) (ps := [])
    unitEnv_IsStructureG_0 rfl rfl unitEnv_foo_hasType.toSE

/-- **Positive-field shape** — the case the brief requires.  `bar` is an axiom inhabitant of
`MutField.B`, whose constructor has one field (`Lean4Lean.MutField.bCtor_has_a_field`); the
`structEta` instance at it is `MutField.bigEnv_structEtaSE_bar`, whose right-hand side is a
`const`-headed spine with a genuine `projTermG` argument.  So the SE guard excludes an eta
instance at a structure that is **not** unit-like. -/
theorem bigEnv_structInhabSE_bar :
    bigEnv.StructInhabSE 0 [] ((VExpr.const `MutField.bar []).mkApp []) :=
  VEnv.structEta_lhs_structInhabSE (us := []) (ps := [])
    bigEnv_IsStructureG_B rfl rfl bigEnv_bar_hasType.toSE

/-- The second zero-field inhabitant, so the transitivity attack of
`Lean4Lean.guard_rejects_an_axiom` (`foo ≡ foo₂` with the constructor absent from the pair) is
excluded at **both** of its endpoints and not merely at one. -/
theorem bigEnv_structInhabSE_foo2 :
    bigEnv.StructInhabSE 0 [] ((VExpr.const `MutField.foo2 []).mkApp []) :=
  VEnv.structEta_lhs_structInhabSE (us := []) (ps := [])
    bigEnv_IsStructureG_A rfl rfl bigEnv_foo2_hasType.toSE

/-- **`guard_rejects_an_axiom`'s verdict, discharged rather than dodged.**  That theorem proves any
head-name guard must reject one of the two axioms.  `¬ StructInhabSE` is not a head-name guard, and
here is the direct check: it rejects **both**, which is exactly why transitivity cannot manufacture
a violating pair from the two eta instances. -/
theorem bigEnv_guard_rejects_both_axioms :
    bigEnv.StructInhabSE 0 [] ((VExpr.const `MutField.foo []).mkApp []) ∧
      bigEnv.StructInhabSE 0 [] ((VExpr.const `MutField.foo2 []).mkApp []) :=
  ⟨VEnv.structEta_lhs_structInhabSE (us := []) (ps := [])
      bigEnv_IsStructureG_A rfl rfl bigEnv_foo_hasType.toSE,
   bigEnv_structInhabSE_foo2⟩

end MutField

/-! ### §4.2 The SE guard is non-trivial — but its non-triviality is **not** available where a
structure exists, and that is a further named gap

For the thirteen-constructor guard, non-triviality is a theorem at both shapes and is already in
the tree: `MutField.bigEnv_not_structInhab_A` (zero-field member's type) and
`MutField.bigEnv_not_structInhab_B` (positive-field member's type), both from
`VEnv.notStructInhab_of_isType_of_wf`, both tainted at the four census holes.  §4.2.1 re-fires
those two so the round's vacuity claim is measured here rather than by reference.

For the **SE** guard there is no such route, and the reason is structural:
`notStructInhab_of_isType` is a universe-uniqueness argument (`VEnv.WF.uniq'` plus
`const_sort_inv_of_wf`) *about the thirteen-constructor relation*.  Neither has an `IsDefEqSE`
analogue in the tree.  So §4.2.2 gives the strongest non-triviality that **is** hole-free —
refutability of the guard at a `VEnv.WF` environment with no inductive block — and §4.2.3 names
the missing obligation instead of papering over it. -/

namespace MutField

/-- **§4.2.1, thirteen-constructor guard, both shapes.**  Re-fired here rather than cited: the
guard holds at the *types* and fails at their *inhabitants*, at one well-formed environment, at
both a zero-field and a positive-field member.

Tainted at the four census holes via `notStructInhab_of_isType_of_wf`. -/
theorem bigEnv_guard_separates_both_shapes :
    (¬ bigEnv.StructInhab 0 [] (VExpr.const `MutField.A []) ∧
      bigEnv.StructInhab 0 [] ((VExpr.const `MutField.foo2 []).mkApp [])) ∧
    (¬ bigEnv.StructInhab 0 [] (VExpr.const `MutField.B []) ∧
      bigEnv.StructInhab 0 [] ((VExpr.const `MutField.bar []).mkApp [])) :=
  ⟨⟨bigEnv_not_structInhab_A, bigEnv_structInhab_foo2⟩,
   ⟨bigEnv_not_structInhab_B, bigEnv_structInhab_bar⟩⟩

end MutField

/-- **§4.2.2 The SE guard is refutable**, hence not "everything satisfies it": at `VEnv.ncPropEnv`
(three axioms, `defeqs = False`, `VEnv.WF`) no term is a structure inhabitant in *either* relation,
because `IsStructureG` needs the block's ι-rules in `defeqs`.

Hole-free; `VEnv.not_structInhabAt_of_no_defeqs` is `Ty`-generic, so this is the same one-line
route `VEnv.not_structInhab_ncPropEnv` takes for the thirteen-constructor guard. -/
theorem VEnv.not_structInhabSE_ncPropEnv {U : Nat} {Γ : List VExpr} {e : VExpr} :
    ¬ VEnv.ncPropEnv.StructInhabSE U Γ e :=
  VEnv.not_structInhabAt_of_no_defeqs (fun _ h => h)

/-- **§4.2.3 The remaining vacuity obligation, named.**

This is `VEnv.notStructInhab_of_isType`'s conclusion with `StructInhab` replaced by
`StructInhabSE`.  It is what makes the SE guard *free at every type*, which is what every consumer
of `ConstAppInvSISE` will need (`VEnv.IsStructure.spine_inv_of_si` applies the guard only ever to
an `IsType`, via `ht₁.isType`).  Nothing in the tree proves it, and the thirteen-constructor proof
does not transport: it runs through `VEnv.WF.uniq'` and `VEnv.const_sort_inv_of_wf`, both of which
are statements about `VEnv.IsDefEq`.

Stated, not proved, and deliberately left as a `def` so that it appears in no cone as a theorem.
-/
def NotStructInhabSEOfIsTypeStmt : Prop :=
  ∀ (env : VEnv), env.WF → ∀ (U : Nat) (Γ : List VExpr) (e : VExpr),
    OnCtx Γ (env.IsType U) → env.IsType U Γ e → ¬ env.StructInhabSE U Γ e

/-- Not vacuous as an obligation: it is exactly what closes the guarded SE statement's top-of-spine
case, and `§4.2.2` shows its conclusion is satisfiable, so it is not asking for a false thing on the
strength of its shape alone. -/
theorem notStructInhabSEOfIsTypeStmt_conclusion_satisfiable :
    ∀ (U : Nat) (Γ : List VExpr) (e : VExpr), ¬ VEnv.ncPropEnv.StructInhabSE U Γ e :=
  fun _ _ _ => VEnv.not_structInhabSE_ncPropEnv

/-! ## 5. Verdict

* `Lean4Lean.constAppInvSIFromWF` — **proved**, tainted at the four census holes
  `VEnv.IsDefEqU.weakN_iff`, `VEnv.IsDefEqU.forallE_inv_stratified`, `VEnv.WF.rigidShapeUniqNS`,
  `VEnv.NormalEq.descend`.  Same taint as `VEnv.IsStructure.spine_inv`, so nothing is added to the
  cone.
* It does **not** close the structure-eta repair.  `Lean4Lean.constAppInvNoSIFromWF` proves the
  same thing with the eta guard deleted, and `Lean4Lean.MutField.unitEnv_noSI_true_but_SE_false`
  shows that statement is *false* one relation over.  The named target and the actual obligation
  have opposite truth values at `MutField.unitEnv`.
* The remaining obligation is `Lean4Lean.ConstAppInvSISEFromWF` (§3.2), and it needs
  `Lean4Lean.NotStructInhabSEOfIsTypeStmt` (§4.2.3) as well as the whole Church–Rosser chain over
  `VEnv.IsDefEqSE`.
* Every taint above is inherited, never incurred: §1/§2 at the four census holes
  `VEnv.IsStructure.spine_inv` already carries, §3.3 at the single hole
  `Lean4Lean.constNoConf_false_for_IsDefEqSE` already carries.  §3.1, §3.2 and §4.1 are hole-free.
* No head-name guard is used anywhere here, so `Lean4Lean.guard_rejects_an_axiom` is respected —
  and §4.1's `bigEnv_guard_rejects_both_axioms` discharges its verdict directly.
* `¬ IsProof` is retained in every statement above, so
  `Lean4Lean.VEnv.structInhabOnlyNoConf_false` is respected: the SE guard is *added*, never a
  replacement.
-/

end Lean4Lean
