import Lean4Lean.Theory.Typing.ConstAppInvSIProof
import Lean4Lean.Theory.Typing.ConfluenceRebuildPrice

/-!
# `SEReduce` — the 14→13 collapse under "no eta-eligible structure", and `ConstAppInvSISE` as an `↔`

## What this file is for

`VEnv.IsDefEqSE` (`Theory/Typing/StructEtaPrice.lean`) is `VEnv.IsDefEq` plus a fourteenth
constructor, `structEta`.  `VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs`
(`Theory/Typing/ConfluenceRebuildPrice.lean`) collapses the fourteen back to thirteen at a
**defeq-free** environment.  That side condition is far too strong to be useful: every environment
that has an inductive declaration in it has δ/ι rules, so "no defeqs" holds at essentially no
environment anyone cares about, and in particular at neither `MutField.unitEnv` nor
`MutField.bigEnv`.

This file does two things.

**§1–§3 weaken the side condition.**  `toIsDefEq_of_no_defeqs` consumes its hypothesis `hd` in
*two* places:

```
| .extra h1 _ _ => absurd h1 (hd _)
| .structEta hS .. => absurd hS (IsStructureG.not_of_no_defeqs hd)
```

The first is waste.  `VEnv.IsDefEq.extra` (`Theory/Typing/Basic.lean:53`) has a signature
character-identical to `VEnv.IsDefEqSE.extra`, so that case maps across as `.extra h1 h2 h3` and
needs no side condition whatsoever.  Only the `structEta` case genuinely needs anything, and what
it needs is not "no defeqs" but the negation of `structEta`'s own *environment-local* premise
block.  `VEnv.NoEtaEligible` is that negation, and `VEnv.IsDefEqSE.toIsDefEq_of_noEta` is the
collapse under it.  `VEnv.noEtaEligible_of_no_defeqs` shows the old side condition implies the new
one, so `toIsDefEq_of_no_defeqs` comes back as a **corollary** (§3) — that is the test that the
weakening is real rather than a reshuffle.

**§5–§6 reduce `VEnv.ConstAppInvSISE` to an `↔`.**  `VEnv.ConstAppInvSI` and
`VEnv.ConstAppInvSISE` (`Theory/Typing/NoConfRepair.lean:292`,
`Theory/Typing/ConstAppInvSIProof.lean:192`) differ in exactly two places: `StructInhab` against
`StructInhabSE`, and `IsDefEqU` against `IsDefEqUSE`.  Under `NoEtaEligible` both differences
close (§4), so the two statements are inter-derivable and `ConstAppInvSISE` is a **theorem** there
(`VEnv.constAppInvSISE_of_noEta`).  Hence the general obligation is equivalent to its restriction
to environments where eta *can* fire (`constAppInvSISEFromWF_iff_etaOnly`, §6), and that residue is
the whole of what is left.

### What the residue is, and what it is not

The residue is **ordinary open work, not one of the thirteen census holes.**  It reduces to
SE-Church–Rosser, and `church_rosserSE` *does not exist as a declaration at all* — verified absent
by `scripts/exists.lean` in the previous round — so it cannot be a census entry; the census counts
`sorry`-carrying declarations.  Worse than merely missing: the two standard routes to it are
**refuted**, by `Lean4Lean.descendSE_uniq_sortUniq_not_all` and
`Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor` (`ConfluenceRebuildPrice.lean:604,628`).  So a
successor should not re-attack `ConstAppInvSISE` by re-erecting `ParRedStatement`; §6 is here
precisely so that the reduction does not hand the problem back unchanged.

### Two constraints this file respects, both measured

* **Never guard on head names.**  `Lean4Lean.guard_rejects_an_axiom`
  (`Theory/Typing/NoConfRepair.lean`, cone 382) proves any head-name-based condition must reject an
  axiom inhabitant, because `trans` manufactures a violating pair from which the constructor is
  absent.  `NoEtaEligible` quantifies over `IsStructureG` witnesses and level data only; it never
  mentions a head name.  §7.3 records the check.
* **`¬ IsProof` cannot be dropped.**  `Lean4Lean.VEnv.structInhabOnlyNoConf_false`
  (`Theory/Typing/EtaGuardLand.lean`, cone 3815) refutes keeping only the new guard at a witness
  where the new guard genuinely holds; and `VEnv.ConstAppInvNoSISE` (guard deleted) is refuted in
  `ConstAppInvSIProof.lean` §3.3.  Every statement below carries `¬ IsProof` *and* the eta guard
  exactly as `ConstAppInvSISE` states them.  Nothing here weakens either.

### Cleanliness, per name rather than per file

§1–§4 and §7 are **hole-free** — they only induct over `IsDefEqSE` and use `IsDefEq.toSE`.
§5's `constAppInvSISE_of_noEta` and §6's `↔` mention the thirteen-constructor side, so anything
*applied* to `constAppInvSIFromWF` inherits that side's four census holes
(`VEnv.IsDefEqU.weakN_iff`, `VEnv.IsDefEqU.forallE_inv_stratified`, `VEnv.WF.rigidShapeUniqNS`,
`VEnv.NormalEq.descend`) and the two watched declarations `VEnv.IsDefEq.uniq`, `VEnv.IsDefEq.uniqU`.
The `↔` itself is stated conditionally on `ConstAppInvSIFromWF`, so it is hole-free as a statement;
the taint arrives only when it is discharged.  Labelled at each declaration.

### A duplicate, flagged and untouched

`VEnv.IsDefEqUSE` (`ConstAppInvSIProof.lean:158`) and `VEnv.IsDefEqSEU`
(`ConfluenceRebuildPrice.lean:294`) are the **same definition** under two names in two files, both
arity 5, both cone 7.  This file uses `IsDefEqUSE`, the one `ConstAppInvSISE` is stated with, and
provides `VEnv.isDefEqUSE_iff_isDefEqSEU` (§7.4) so the duplication is at least bridged.  Neither
file is mine to edit, so neither declaration is deleted.
-/

namespace Lean4Lean
namespace VEnv

/-! ## §1 The weakened side condition

`structEta`'s premises split in two.  Five are **environment-local** — they mention only `env`,
the structure data `S D j T C`, and the universe list `us`:

* `env.IsStructureG S D j T C`
* `T.indices = []`
* `C.recFields = []`
* `us.length = D.uvars` and `∀ l ∈ us, l.WF uvars`
* the F17 small-eliminating clause `D.isLE = true ∨ ∀ k < C.fields.length, …`

Four are **derivation-local** — they mention the context `Γ`, the parameter spine `ps` and the
subject `e`: `ps.length = D.np`, `HasArgsSE …`, and `IsDefEqSE Γ e e ((const S us).mkApp ps)`.

A side condition on the *environment* can only negate the first block, and negating it is enough
to kill the rule.  So `NoEtaEligible` is exactly that: **no structure in `env` is eta-eligible at
any universe instantiation.**  Nothing weaker can be stated environment-locally, and nothing
stronger is needed. -/

/-- **No eta-eligible structure.**  The negation of `structEta`'s environment-local premise block:
for no structure of `env`, at no universe instantiation, are all five local premises jointly
satisfiable.

Strictly weaker than `∀ df, ¬ env.defeqs df` in three independent ways — it permits environments
with δ-rules and ι-rules outright, it permits structures with indices or recursive fields, and it
permits large-eliminating structures with a large field.  `noEtaEligible_of_no_defeqs` (§3) is the
implication that makes the old side condition a special case.

Note what is *not* here: no head name.  `Lean4Lean.guard_rejects_an_axiom` (cone 382) shows a
head-name guard must reject an axiom inhabitant, so this condition is deliberately phrased over
`IsStructureG` witnesses and level data only. -/
def NoEtaEligible (env : VEnv) (U : Nat) : Prop :=
  ∀ {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
    {us : List VLevel},
    env.IsStructureG S D j T C → T.indices = [] → C.recFields = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF U) →
    (D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ VLevel.zero) →
    False

/-! ## §2 The collapse, under the weakened condition

Thirteen cases map across one-for-one — `extra` **included**, which is the correction to
`toIsDefEq_of_no_defeqs` — and `structEta` dies on the side condition, consuming precisely its
five environment-local premises and ignoring its four derivation-local ones. -/

mutual

/-- **The fourteenth constructor is dead wherever no structure is eta-eligible.**

Compare `VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs`, which needs `∀ df, ¬ env.defeqs df`.  The only
difference in the proof is the `extra` case — here it is the constructor, there it is `absurd` —
and the `structEta` case, which here uses the five local premises rather than discarding the
whole environment.

Hole-free. -/
theorem IsDefEqSE.toIsDefEq_of_noEta {env : VEnv} {U : Nat} (hne : env.NoEtaEligible U)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : env.IsDefEqSE U Γ e₁ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ A :=
  match H with
  | .bvar h => .bvar h
  | .symm h => .symm (h.toIsDefEq_of_noEta hne)
  | .trans h₁ h₂ => .trans (h₁.toIsDefEq_of_noEta hne) (h₂.toIsDefEq_of_noEta hne)
  | .sortDF h1 h2 h3 => .sortDF h1 h2 h3
  | .constDF h1 h2 h3 h4 h5 => .constDF h1 h2 h3 h4 h5
  | .appDF h₁ h₂ => .appDF (h₁.toIsDefEq_of_noEta hne) (h₂.toIsDefEq_of_noEta hne)
  | .lamDF h₁ h₂ => .lamDF (h₁.toIsDefEq_of_noEta hne) (h₂.toIsDefEq_of_noEta hne)
  | .forallEDF h₁ h₂ => .forallEDF (h₁.toIsDefEq_of_noEta hne) (h₂.toIsDefEq_of_noEta hne)
  | .defeqDF h₁ h₂ => .defeqDF (h₁.toIsDefEq_of_noEta hne) (h₂.toIsDefEq_of_noEta hne)
  | .beta h₁ h₂ => .beta (h₁.toIsDefEq_of_noEta hne) (h₂.toIsDefEq_of_noEta hne)
  | .eta h => .eta (h.toIsDefEq_of_noEta hne)
  | .proofIrrel h₁ h₂ h₃ =>
    .proofIrrel (h₁.toIsDefEq_of_noEta hne) (h₂.toIsDefEq_of_noEta hne)
      (h₃.toIsDefEq_of_noEta hne)
  | .extra h1 h2 h3 => .extra h1 h2 h3
  | .structEta hS hidx hrec hlen hwf _ _ _ hsmall =>
    (hne hS hidx hrec hlen hwf hsmall).elim

/-- The parameter-spine companion; `HasArgsSE` and `IsDefEqSE` are mutually inductive. -/
theorem HasArgsSE.toHasArgs_of_noEta {env : VEnv} {U : Nat} (hne : env.NoEtaEligible U)
    {Γ As as : List VExpr} (H : env.HasArgsSE U Γ As as) : env.HasArgs U Γ As as :=
  match H with
  | .nil => .nil
  | .cons h t => .cons (h.toIsDefEq_of_noEta hne) (t.toHasArgs_of_noEta hne)

end

/-! ## §3 The old side condition is a special case

This is the test that §1 is a genuine weakening and not a restatement: the previous round's
theorem falls out of §2 with a one-line premise conversion. -/

/-- **`∀ df, ¬ env.defeqs df` implies `NoEtaEligible`**, via
`VEnv.IsStructureG.not_of_no_defeqs` — which needs only the *first* of the five local premises,
so four of them are slack.  That slack is the weakening. -/
theorem noEtaEligible_of_no_defeqs {env : VEnv} {U : Nat} (hd : ∀ df, ¬ env.defeqs df) :
    env.NoEtaEligible U :=
  fun hS _ _ _ _ _ => IsStructureG.not_of_no_defeqs hd hS

/-- **`VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs`, recovered as a corollary of §2.**  Stated here under
a fresh name (the original is not mine to edit) so that the recovery is machine-checked rather than
asserted. -/
theorem IsDefEqSE.toIsDefEq_of_no_defeqs' {env : VEnv} {U : Nat} (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : env.IsDefEqSE U Γ e₁ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ A :=
  H.toIsDefEq_of_noEta (noEtaEligible_of_no_defeqs hd)

/-! ## §4 Both differences between the two relations close

`ConstAppInvSI` and `ConstAppInvSISE` differ only at `IsDefEqU`/`IsDefEqUSE` and
`StructInhab`/`StructInhabSE`.  §4.1 closes the first, §4.2 the second. -/

/-- The typed collapse as an `Iff`; `IsDefEq.toSE` is the inclusion the other way. -/
theorem isDefEqSE_iff_of_noEta {env : VEnv} {U : Nat} (hne : env.NoEtaEligible U)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} :
    env.IsDefEqSE U Γ e₁ e₂ A ↔ env.IsDefEq U Γ e₁ e₂ A :=
  ⟨fun h => h.toIsDefEq_of_noEta hne, IsDefEq.toSE⟩

/-- …and the untyped one, at `IsDefEqUSE` (the name `ConstAppInvSISE` is stated with). -/
theorem isDefEqUSE_iff_of_noEta {env : VEnv} {U : Nat} (hne : env.NoEtaEligible U)
    {Γ : List VExpr} {e₁ e₂ : VExpr} :
    env.IsDefEqUSE U Γ e₁ e₂ ↔ env.IsDefEqU U Γ e₁ e₂ :=
  exists_congr fun _ => isDefEqSE_iff_of_noEta hne

/-- **`StructInhabAt` is monotone in its typing relation** — `Ty` occurs positively and exactly once
in the definition, so this needs no hypothesis at all.  Recorded separately because it is the
direction that holds *unconditionally* and is what makes `¬ StructInhabSE → ¬ StructInhab` free. -/
theorem StructInhabAt.mono' {env : VEnv} {Ty Ty' : VExpr → VExpr → Prop}
    (h : ∀ e A, Ty e A → Ty' e A) {e : VExpr} (H : env.StructInhabAt Ty e) :
    env.StructInhabAt Ty' e :=
  let ⟨S, D, j, T, C, us, ps, h1, h2, h3, h4⟩ := H
  ⟨S, D, j, T, C, us, ps, h1, h2, h3, h _ _ h4⟩

/-- **`StructInhab → StructInhabSE`, unconditionally.**  The thirteen embed in the fourteen
(`IsDefEq.toSE`), so the guard at the extended relation is the *weaker* requirement to negate. -/
theorem StructInhab.toSE {env : VEnv} {U : Nat} {Γ : List VExpr} {e : VExpr}
    (H : env.StructInhab U Γ e) : env.StructInhabSE U Γ e :=
  H.mono' fun _ _ h => IsDefEq.toSE h

/-- Hence the contrapositive, which is the form §5 consumes: the SE guard implies the old one. -/
theorem not_structInhab_of_not_structInhabSE {env : VEnv} {U : Nat} {Γ : List VExpr} {e : VExpr}
    (H : ¬ env.StructInhabSE U Γ e) : ¬ env.StructInhab U Γ e :=
  fun h => H h.toSE

/-- And under the side condition the two guards **coincide**. -/
theorem structInhabSE_iff_of_noEta {env : VEnv} {U : Nat} (hne : env.NoEtaEligible U)
    {Γ : List VExpr} {e : VExpr} : env.StructInhabSE U Γ e ↔ env.StructInhab U Γ e :=
  ⟨fun H => H.mono' fun _ _ h => h.toIsDefEq_of_noEta hne, StructInhab.toSE⟩

/-! ## §5 `ConstAppInvSISE` is a theorem wherever eta cannot fire

This is the load-bearing consequence: the extended relation **agrees with the current one wherever
eta cannot fire**, which is where every existing proof lives. -/

/-- **The two statements are inter-derivable under the side condition.**

Hole-free as a statement and as a proof; it is *conditional on* `env.ConstAppInvSI U`, so it does
not import that side's holes. -/
theorem constAppInvSISE_iff_of_noEta {env : VEnv} {U : Nat} (hne : env.NoEtaEligible U) :
    env.ConstAppInvSISE U ↔ env.ConstAppInvSI U := by
  constructor
  · intro H Γ c c' ls ls' as as' hΓ hc hc' hnp hSI h
    have ⟨h1, h2, h3⟩ := H Γ c c' ls ls' as as' hΓ hc hc' hnp
      (fun hse => hSI ((structInhabSE_iff_of_noEta hne).1 hse))
      ((isDefEqUSE_iff_of_noEta hne).2 h)
    exact ⟨h1, h2, h3.imp fun _ _ hh => (isDefEqUSE_iff_of_noEta hne).1 hh⟩
  · intro H Γ c c' ls ls' as as' hΓ hc hc' hnp hSI h
    have ⟨h1, h2, h3⟩ := H Γ c c' ls ls' as as' hΓ hc hc' hnp
      (not_structInhab_of_not_structInhabSE hSI)
      ((isDefEqUSE_iff_of_noEta hne).1 h)
    exact ⟨h1, h2, h3.imp fun _ _ hh => (isDefEqUSE_iff_of_noEta hne).2 hh⟩

/-- **`ConstAppInvSISE` outright, wherever eta cannot fire.**

Tainted exactly as `Lean4Lean.constAppInvSIFromWF` is: four census holes
(`VEnv.IsDefEqU.weakN_iff`, `VEnv.IsDefEqU.forallE_inv_stratified`, `VEnv.WF.rigidShapeUniqNS`,
`VEnv.NormalEq.descend`) and the two watched declarations `VEnv.IsDefEq.uniq`,
`VEnv.IsDefEq.uniqU`.  The taint is entirely in the hypothesis `H`; nothing in §1–§4 adds to it. -/
theorem constAppInvSISE_of_noEta {env : VEnv} {U : Nat} (H : env.ConstAppInvSI U)
    (hne : env.NoEtaEligible U) : env.ConstAppInvSISE U :=
  (constAppInvSISE_iff_of_noEta hne).2 H

end VEnv

/-! ## §6 The reduction: the residue is exactly the eta-eligible case

`ConstAppInvSISEFromWF` quantifies over all well-formed environments.  §5 discharges every one at
which no structure is eta-eligible.  So the whole obligation is **equivalent** to its restriction
to the environments where eta *can* fire — which is a reduction rather than a restatement, because
the forward direction throws away a class of environments that §5 has actually settled. -/

/-- The residue: `ConstAppInvSISE` at well-formed environments where **some** structure *is*
eta-eligible.  Note `¬ NoEtaEligible`, not a head-name condition and not a shape condition. -/
def ConstAppInvSISEFromWFEtaOnly : Prop :=
  ∀ (env : VEnv) (U : Nat), env.WF → ¬ env.NoEtaEligible U → env.ConstAppInvSISE U

/-- **The `↔`, against the smallest sufficient premise.**

Unlike `Lean4Lean.constAppInvSISEFromWF_iff_unguarded` — whose own docstring disclaims information
content, both sides being theorems — this `↔` is *informative*: the right-hand side is strictly
smaller than the left, because §5 settles the complementary class of environments outright.

The premise `ConstAppInvSIFromWF` is carried rather than discharged, so this theorem is
**hole-free as a statement**; discharging it with `Lean4Lean.constAppInvSIFromWF` imports that
declaration's four census holes and two watched declarations.

**Classification of the residue: ordinary open work, not a census hole.**  It reduces to
SE-Church–Rosser; `church_rosserSE` does not exist as a declaration (verified absent), so it is not
among the thirteen `sorry`-carrying census entries.  And it is worse than absent: the two standard
routes are refuted by `Lean4Lean.descendSE_uniq_sortUniq_not_all` and
`Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor`.  A successor must find a route that is not
`ParRedStatement`, or refute `ConstAppInvSISE` at an eta-eligible environment. -/
theorem constAppInvSISEFromWF_iff_etaOnly (H13 : ConstAppInvSIFromWF) :
    ConstAppInvSISEFromWF ↔ ConstAppInvSISEFromWFEtaOnly := by
  constructor
  · intro H env U henv _; exact H env U henv
  · intro H env U henv
    by_cases hne : env.NoEtaEligible U
    · exact VEnv.constAppInvSISE_of_noEta (H13 env U henv) hne
    · exact H env U henv hne


/-! ## §7 Vacuity, both ways, at both structure shapes

A side condition earns the name only if it is **satisfiable** at real environments and
**restrictive** enough to exclude the eta case.  Both halves are checked, and the restrictive half
is checked at *two* environments at *two* field arities, because
`Lean4Lean.zeroFieldOnlyNoConf_false_for_IsDefEqSE` says the failure is **not** zero-field-only and
a repair that only excluded zero-field structures would be worthless. -/

namespace VEnv

/-! ### §7.1 Satisfiable — at well-formed environments

`ncPropEnv` is the important one: `Lean4Lean.VEnv.wf_ncPropEnv` makes it a genuinely well-formed
environment, so `NoEtaEligible` is not a condition that only holds at junk. -/

/-- **Satisfiable at a well-formed environment.**  `ncPropEnv` (`Verify/Typing/NoConfGuard.lean:86`)
is `VEnv.WF` by `wf_ncPropEnv` and defeq-free by computation.  Hole-free. -/
theorem ncPropEnv_noEtaEligible {U : Nat} : ncPropEnv.NoEtaEligible U :=
  noEtaEligible_of_no_defeqs fun _ h => h

/-- Hence the collapse actually *fires* somewhere: at `ncPropEnv` the fourteen-constructor relation
is pointwise the thirteen-constructor one. -/
theorem ncPropEnv_isDefEqSE_iff' {U : Nat} {Γ : List VExpr} {e₁ e₂ A : VExpr} :
    ncPropEnv.IsDefEqSE U Γ e₁ e₂ A ↔ ncPropEnv.IsDefEq U Γ e₁ e₂ A :=
  isDefEqSE_iff_of_noEta ncPropEnv_noEtaEligible

/-- …and so is `ConstAppInvSISE` there, given the thirteen-constructor statement.  This is §5 with
every hypothesis discharged except the one that carries the taint. -/
theorem ncPropEnv_constAppInvSISE {U : Nat} (H : ncPropEnv.ConstAppInvSI U) :
    ncPropEnv.ConstAppInvSISE U :=
  constAppInvSISE_of_noEta H ncPropEnv_noEtaEligible

end VEnv

/-- **Satisfiable at the reference environment too.**  `Lean4Lean.refEnv_no_defeqs` is the
defeq-freeness `ConfluenceRebuildPrice.lean` §5 runs on. -/
theorem refEnv_noEtaEligible {U : Nat} : refEnv.NoEtaEligible U :=
  VEnv.noEtaEligible_of_no_defeqs fun _ => refEnv_no_defeqs

/-! ### §7.2 Restrictive — refuted at both environments, at both field arities

Each refutation is a single application of the side condition to the **first five** arguments of an
already-established `structEta` firing.  That is the sharpest possible demonstration that the
condition is the right one: the same premise tuple that fires the rule refutes the condition, with
the four derivation-local premises left over. -/

namespace MutField

/-- **Refuted at `MutField.unitEnv`, zero-field shape** (block 0, `MutField.A`, whose constructor
has no fields).  Premises are `MutField.structEtaSE_foo`'s first five. -/
theorem unitEnv_not_noEtaEligible_zeroField : ¬ unitEnv.NoEtaEligible 0 :=
  fun hne => hne (us := []) unitEnv_IsStructureG_0 rfl rfl rfl nofun (.inr (by simp [aCtor]))

/-- **Refuted at `MutField.unitEnv`, positive-field shape** (block 1, `MutField.B`, whose
constructor has a field — `MutField.bCtor_has_a_field`).  `MutField.declEnv_IsStructureG` transported
along `MutField.declEnv_le_unitEnv` by `VEnv.IsStructureG.mono`, so this is the *same* block's other
member: one constructor, two arities.  **This is the case that matters**, since
`Lean4Lean.zeroFieldOnlyNoConf_false_for_IsDefEqSE` says the failure is not zero-field-only. -/
theorem unitEnv_not_noEtaEligible_posField : ¬ unitEnv.NoEtaEligible 0 :=
  fun hne =>
    hne (us := []) (declEnv_IsStructureG.mono declEnv_le_unitEnv) rfl rfl rfl nofun (.inr bCtor_field_prop)

/-- **Refuted at `MutField.bigEnv`, zero-field shape.**  `bigEnv` is `unitEnv` plus two more axiom
inhabitants and is well formed by `MutField.bigEnv_wf`, so this is a refutation at a legitimate
environment rather than at a hand-built one.  Premises are `MutField.bigEnv_structEtaSE_foo`'s
first five. -/
theorem bigEnv_not_noEtaEligible_zeroField : ¬ bigEnv.NoEtaEligible 0 :=
  fun hne => hne (us := []) bigEnv_IsStructureG_A rfl rfl rfl nofun (.inr (by simp [aCtor]))

/-- **Refuted at `MutField.bigEnv`, positive-field shape** — the fourth and last corner.  Premises
are `MutField.bigEnv_structEtaSE_bar`'s first five; `MutField.bar` is an axiom inhabitant of
`MutField.B`, so the eta instance this excludes is one with a genuine `projTermG` on the right. -/
theorem bigEnv_not_noEtaEligible_posField : ¬ bigEnv.NoEtaEligible 0 :=
  fun hne => hne (us := []) bigEnv_IsStructureG_B rfl rfl rfl nofun (.inr bCtor_field_prop)

end MutField

/-! ### §7.3 The two hard constraints, checked rather than asserted

**Never guard on head names.**  `Lean4Lean.guard_rejects_an_axiom` (cone 382) shows any head-name
condition must reject an axiom inhabitant.  `VEnv.NoEtaEligible` is stated over `IsStructureG`
witnesses, `T.indices`, `C.recFields`, `us` and `C.fields`' levels — the `example` below is the
machine check that it never sees a head name: it is invariant under changing every name in the
environment, in the only sense expressible here, namely that it mentions no `Lean.Name` literal and
takes the structure name as a *bound* variable.

**`¬ IsProof` cannot be dropped.**  `Lean4Lean.VEnv.structInhabOnlyNoConf_false` (cone 3815) refutes
keeping only the new guard.  Every statement in §5 and §6 carries `¬ IsProof` and `¬ StructInhabSE`
exactly as `VEnv.ConstAppInvSISE` states them; the `example` below pins that by exhibiting the
premise list unchanged. -/

/-- The head-name check: `NoEtaEligible` at `S` bound, so no head name can be read off it. -/
example (env : VEnv) (U : Nat) :
    env.NoEtaEligible U ↔
    ∀ {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType} {C : VIndCtor}
      {us : List VLevel},
      env.IsStructureG S D j T C → T.indices = [] → C.recFields = [] →
      us.length = D.uvars → (∀ l ∈ us, l.WF U) →
      (D.isLE = true ∨ ∀ k, k < C.fields.length →
        (C.fields.getD k default).lvl.inst us ≈ VLevel.zero) →
      False := Iff.rfl

/-- The guard-retention check: §5's conclusion really is `ConstAppInvSISE`, `¬ IsProof` and
`¬ StructInhabSE` included, not a weakened cousin. -/
example {env : VEnv} {U : Nat} (H : env.ConstAppInvSI U) (hne : env.NoEtaEligible U)
    (Γ : List VExpr) (c c' : Lean.Name) (ls ls' : List VLevel) (as as' : List VExpr)
    (hΓ : OnCtx Γ (env.IsType U)) (hc : env.RuleFreeHead c) (hc' : env.RuleFreeHead c')
    (hnp : ¬ env.IsProof U Γ ((VExpr.const c ls).mkApp as))
    (hSI : ¬ env.StructInhabSE U Γ ((VExpr.const c ls).mkApp as))
    (h : env.IsDefEqUSE U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c' ls').mkApp as')) :
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqUSE U Γ) as as' :=
  VEnv.constAppInvSISE_of_noEta H hne Γ c c' ls ls' as as' hΓ hc hc' hnp hSI h

/-! ### §7.4 The flagged duplicate, bridged

`VEnv.IsDefEqUSE` (`ConstAppInvSIProof.lean:158`) and `VEnv.IsDefEqSEU`
(`ConfluenceRebuildPrice.lean:294`) are the same definition under two names, in two files, both
arity 5 and both cone 7.  Neither file is mine to edit, so the duplication stands; this bridges it
so that a successor at least need not choose. -/

theorem VEnv.isDefEqUSE_iff_isDefEqSEU {env : VEnv} {U : Nat} {Γ : List VExpr} {e₁ e₂ : VExpr} :
    env.IsDefEqUSE U Γ e₁ e₂ ↔ env.IsDefEqSEU U Γ e₁ e₂ := Iff.rfl

/-! ## §8 The weakening is *strict*: an environment with defeqs that still satisfies the condition

§3 shows `no defeqs → NoEtaEligible`.  Without a separating environment that implication could be
an equivalence, and then §1 would be a restatement rather than a weakening.  This section supplies
the separation, so that the docstring's claim in §1 is machine-checked rather than asserted —
`docs/audit-doc-claims.md` exists because unchecked docstring claims in this repo have been wrong.

The lever is that `VEnv.IsStructureG` forces the structure's *type constant* to be present
(`decl` gives `env₀.addInduct' D = some env₁ ≤ env`, and `VEnv.addInduct'_types` puts `T.name` into
`env₁`), so an environment with **no constants at all** satisfies `NoEtaEligible` no matter how many
δ-rules it carries.  This is a second sufficient condition, independent of §3. -/

namespace VEnv

/-- **No constants ⇒ no eta-eligible structure.**  Independent of defeq-freeness: `IsStructureG`
needs `env.constants T.name = some ⟨D.uvars, T.type⟩`, by the same route as
`Lean4Lean.VEnv.empty_structEtaG`.  Hole-free. -/
theorem noEtaEligible_of_no_constants {env : VEnv} {U : Nat}
    (hc : ∀ n, env.constants n = none) : env.NoEtaEligible U := by
  intro S D j T C us hS _ _ _ _ _
  obtain ⟨env₀, env₁, _, hadd, hle⟩ := hS.decl
  have h := hle.constants (VEnv.addInduct'_types (T := T) hadd
    (List.getElem?_eq_some_iff.1 hS.types |>.2 ▸ (by exact List.getElem_mem _)))
  rw [hc T.name] at h
  simp at h

end VEnv

/-- **The separating environment.**  `VEnv.empty.addDefEq df` has a defeq (next theorem) and no
constants, so it satisfies `NoEtaEligible` while failing `∀ df, ¬ env.defeqs df`. -/
theorem addDefEq_empty_noEtaEligible {U : Nat} (df : VDefEq) :
    (VEnv.empty.addDefEq df).NoEtaEligible U :=
  VEnv.noEtaEligible_of_no_constants fun _ => rfl

/-- …and it really does have a defeq, so the old side condition genuinely fails there. -/
theorem addDefEq_empty_has_defeq (df : VDefEq) :
    ¬ ∀ df', ¬ (VEnv.empty.addDefEq df).defeqs df' :=
  fun h => h df (.inl rfl)

/-- **The separation, as one statement.**  `NoEtaEligible` is *strictly* weaker than
`∀ df, ¬ env.defeqs df`: the implication of §3 holds, and its converse fails at
`VEnv.empty.addDefEq df`.  Hole-free. -/
theorem noEtaEligible_strictly_weaker_than_no_defeqs (df : VDefEq) :
    (∀ (env : VEnv) (U : Nat), (∀ df, ¬ env.defeqs df) → env.NoEtaEligible U) ∧
    ∃ (env : VEnv) (U : Nat), env.NoEtaEligible U ∧ ¬ ∀ df, ¬ env.defeqs df :=
  ⟨fun _ _ hd => VEnv.noEtaEligible_of_no_defeqs hd,
   VEnv.empty.addDefEq df, 0,
     addDefEq_empty_noEtaEligible df, addDefEq_empty_has_defeq df⟩

/-! ## §9 The `↔` discharged — the reduction, unconditionally

§6 carries `ConstAppInvSIFromWF` as a hypothesis, which keeps it `sorryAx`-free but leaves a reader
to do the last step.  `Lean4Lean.constAppInvSIFromWF` is a theorem, so the `↔` holds outright; it is
recorded here separately **because discharging it is exactly where the taint enters**, and a single
declaration carrying both the clean and the tainted form would hide that.

Tainted at four census holes — `VEnv.IsDefEqU.weakN_iff`, `VEnv.IsDefEqU.forallE_inv_stratified`,
`VEnv.WF.rigidShapeUniqNS`, `VEnv.NormalEq.descend` — and at the two watched declarations
`VEnv.IsDefEq.uniq`, `VEnv.IsDefEq.uniqU`, all of them inherited from `constAppInvSIFromWF` and none
of them introduced here. -/

/-- **The reduction, unconditionally**: proving `ConstAppInvSISE` at every well-formed environment is
*equivalent* to proving it only at those where some structure is eta-eligible.  Everything else is
settled by §5.

This is what a successor should attack, and §6's docstring says why it must not be attacked by
re-erecting `ParRedStatement`. -/
theorem constAppInvSISEFromWF_iff_etaOnly' :
    ConstAppInvSISEFromWF ↔ ConstAppInvSISEFromWFEtaOnly :=
  constAppInvSISEFromWF_iff_etaOnly constAppInvSIFromWF

end Lean4Lean
