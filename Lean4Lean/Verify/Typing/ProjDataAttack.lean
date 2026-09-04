import Lean4Lean.Verify.Typing.ProjExistClose
import Lean4Lean.Verify.Typing.ProjInhab

/-!
# Attacking `VEnv.ProjDataStrengthen` — and the instrument the earlier rounds walked past

Round of 2026-09-04, stream `projdata`.  Ledger: `docs/handoff-projdata.md`.

## What the target actually is

`docs/audit-hole-producers.md` §M9 promotes `VEnv.ProjDataStrengthen`
(`Verify/Typing/ProjExistClose.lean`) to "#1's residual" on the strength of
`VEnv.projStrengthen_iff`.  Measured here, the chain is

    TrProj.weak'_inv  ⟺  ∀ env, env.WF → ∀ U, env.ProjStrengthen U
                      ⟺  ∀ env, env.WF → ∀ U, env.ProjDataStrengthen U

with both `iff` steps holding pointwise and *without* `VEnv.WF`
(`VEnv.ProjStrengthen.projDataStrengthen`, `VEnv.ProjDataStrengthen.projStrengthen`).  So
`ProjDataStrengthen` is **not a weakening of hole #1; it is hole #1 written at the field level**,
and the same verdict §M9 correctly passes on `TrProj.weak'_inv_of_projStrengthen` ("a
repackaging, not a producer") applies verbatim to `weak'_inv_of_projDataStrengthen`.  The
comparison "cone 717 hole-free versus 3698 with three holes" is therefore not like-for-like: 3698
is `TrProj.weak'_inv_of_strengthen`, which discharges the hole from the *strictly stronger*
`VEnv.ConstAppTypeStrengthen`, while 717 discharges it from an *equivalent* hypothesis — where a
hole-free reduction is free by construction, because no mathematics crosses.

What §1 of `ProjExistClose.lean` did buy is real but different: the ten fields are now visible
individually, which is what makes the attack below possible.

## What this file adds

`ProjWeakInv.lean`'s Round 2 ran the standard strengthening move — *a lift over an inhabited
binder is undone by instantiation* — at the level of `VEnv.ConstAppTypeStrengthen`, i.e. on the
major premise's **type only** (`hasType_const_mkApp_of_inhabLift`,
`constAppTypeStrengthen_of_skipUninhab`).  Getting from there back to `TrProj` costs
`VEnv.HasArgs.of_mkApp` — the two `HasArgs` fields were discarded and have to be rebuilt — and
that is where `rigidShapeUniqNS`, `forallE_inv_stratified`, `IsDefEq.uniq` and `IsDefEq.uniqU`
enter.  `VEnv.ConstAppTypeStrengthen.projDataStrengthen` pays exactly that bill: cone 3702, three
holes, three watched names.

**`TrProj.instN` (`Verify/Typing/Lemmas.lean:2141`, cone 2340, hole-free) already substitutes a
whole `TrProj` derivation**, fields and all, and no file in the projection family cites it.
Running the same two moves through it instead:

* `TrProj.strengthen_inhabLift` — the strengthening holds across every `Ctx.InhabLift`, at every
  depth, **hole-free**;
* `VEnv.AllTypesInhabited.projStrengthen` — hence hole #1 holds outright, hole-free, at every
  environment with no uninhabited type;
* `VEnv.ProjSkipUninhab` + `projStrengthen_of_skipUninhab` — hole #1 reduced, **hole-free**, to
  **one binder that may be assumed uninhabited in its own prefix**, with no `VEnv.WF`, no
  `OnCtx`, and no appeal to `HasArgs.of_mkApp`, `OnCtx.weak'_inv`, Church–Rosser or
  `IsDefEqU.weakN_iff`.

Net effect on the hole's price: the previously best route to `TrProj.weak'_inv` from a
one-uninhabited-binder residual was `constAppTypeStrengthen_of_skipUninhab` composed with
`TrProj.weak'_inv_of_strengthen`, carrying `{weakN_iff, forallE_inv_stratified,
rigidShapeUniqNS}` plus three watched names.  `TrProj.weak'_inv_of_skipUninhab` below carries
none of the six.

Nothing here discharges a `sorry`: the census does not move.  What resists is stated in §4 and,
where it can be, proved.
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat}

/-! ## 1. The inhabited region, at the level of `TrProj` itself

Mirror of `hasType_const_mkApp_of_inhabLift` with `HasType.instN` replaced by `TrProj.instN`.
Because the *whole derivation* is substituted, no field is discarded and none has to be rebuilt:
`TrProj.instN` discharges `VEnv.HasArgs.instN`, `VExpr.instTele_eq_self` and
`VInductDecl'.projTerm_instN` internally, all hole-free. -/

/-- **The strengthening holds across every inhabited lift, at every depth.**  Hypotheses: `env`
ordered, and an inhabitant for each inserted binder.  Not needed: `VEnv.WF`, `OnCtx Γ'`,
`IsStructure` inversion, `HasArgs.of_mkApp`. -/
theorem TrProj.strengthen_inhabLift (henv : env.Ordered) {s : Lean.Name} {i : Nat} :
    ∀ {l : Lift} {Γ Γ' : List VExpr}, Ctx.InhabLift env U l Γ Γ' →
      ∀ {e e' : VExpr}, TrProj env U Γ' s i (e.lift' l) e' →
      ∃ e'', TrProj env U Γ s i e e'' := by
  intro l Γ Γ' W
  induction W with
  | refl => intro e e' H; exact ⟨_, by simpa using H⟩
  | step _ _ ht WI ih =>
    intro e e' H
    rw [VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
    have H2 := H.instN henv WI ht
    rw [VExpr.inst_liftN] at H2
    exact ih H2

/-- The same, packaged as `VEnv.ProjStrengthen`'s conclusion, so it can be read against the
hole directly. -/
theorem TrProj.weak'_inv_of_inhabLift (henv : env.Ordered) {s : Lean.Name} {i : Nat}
    {l : Lift} {Γ Γ' : List VExpr} {e e' : VExpr} (W : Ctx.InhabLift env U l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.strengthen_inhabLift henv W H

/-- **The bound is not vacuous, and reaches every depth.**  `Ctx.InhabLift.sorts` supplies an
inhabited lift of depth `n` in *every* environment (a `Sort 1` binder is inhabited by `Sort 0`),
so §1 strictly extends `constAppTypeStrengthen_depth_zero`'s region at the `TrProj` level. -/
theorem TrProj.strengthen_sorts (henv : env.Ordered) {s : Lean.Name} {i : Nat} (n : Nat)
    {Γ : List VExpr} {e e' : VExpr}
    (H : TrProj env U (List.replicate n (VExpr.sort (.succ .zero)) ++ Γ) s i
      (e.lift' (.skipN .refl n)) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.strengthen_inhabLift henv (Ctx.InhabLift.sorts n) H

/-- …fired at depth one on the tree's only `TrProj` witness (`prjEnv_trProj`,
`Verify/Typing/ProjExistClose.lean` §2), so §1 is exercised rather than merely stated. -/
theorem trProj_strengthen_inhabLift_fires :
    ∃ e'', TrProj prjEnv 0 prjCtx `Prj 0 (.bvar 0) e'' :=
  TrProj.strengthen_inhabLift prjEnv_ordered
    (Ctx.InhabLift.refl.skip (A := VExpr.sort (.succ .zero)) (t := .sort .zero)
      (VEnv.HasType.sort trivial))
    (prjEnv_trProj.weakN prjEnv_ordered (Γ' := VExpr.sort (.succ .zero) :: prjCtx) .one)

/-! ## 2. No uninhabited type ⟹ hole #1, hole-free

`VEnv.AllTypesInhabited.constAppTypeStrengthen` (`ProjInhab.lean`) is this statement for the
*type-only* residual; composing it to the hole goes through
`TrProj.weak'_inv_of_strengthen` and so costs three holes.  Run through `TrProj.instN`, the same
hypothesis reaches the hole with nothing owed. -/

theorem projStrengthen_of_allTypesInhabited_aux (henv : env.Ordered)
    (hinh : env.AllTypesInhabited U) {s : Lean.Name} {i : Nat} :
    ∀ (n : Nat) {l : Lift} {Γ Γ' : List VExpr} {e e' : VExpr},
      l.depth = n → Ctx.Lift' l Γ Γ' → OnCtx Γ' (env.IsType U) →
      TrProj env U Γ' s i (e.lift' l) e' → ∃ e'', TrProj env U Γ s i e e'' := by
  intro n
  induction n with
  | zero =>
    intro l Γ Γ' e e' hd W _ H
    cases W.depth_zero hd
    rw [VExpr.lift'_depth_zero hd] at H
    exact ⟨_, H⟩
  | succ n ih =>
    intro l Γ Γ' e e' hd W hΓ' H
    obtain ⟨l, k, hdl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
    obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W2.exists_instN_typed hΓ'
    obtain ⟨e₀, h₀⟩ := hinh hΓ₀ hA₀
    have H2 := H.instN henv (hI e₀) h₀
    rw [VExpr.inst_liftN] at H2
    exact ih (by simpa using hdl) W1 (Ctx.InstN.wf henv (hI e₀) h₀ hΓ').2 H2

/-- **Every environment in which each type is inhabited satisfies hole #1's statement**, and the
proof is hole-free. -/
theorem VEnv.AllTypesInhabited.projStrengthen (henv : env.Ordered)
    (hinh : env.AllTypesInhabited U) : env.ProjStrengthen U := fun hΓ' W H =>
  projStrengthen_of_allTypesInhabited_aux henv hinh _ rfl W hΓ' H

theorem VEnv.AllTypesInhabited.projDataStrengthen (henv : env.Ordered)
    (hinh : env.AllTypesInhabited U) : env.ProjDataStrengthen U :=
  VEnv.ProjStrengthen.projDataStrengthen (VEnv.AllTypesInhabited.projStrengthen henv hinh)

/-! ## 3. The residual: one binder, and it may be assumed uninhabited

`VEnv.ConstAppSkipUninhab` is the same restriction for the type-only residual.  The point of
restating it at the `TrProj` level is the taint: `constAppTypeStrengthen_of_skipUninhab` is
hole-free, but its composite with `TrProj.weak'_inv_of_strengthen` is not, and the composite is
what the hole needs. -/

/-- **The residual of hole #1, reduced.**  One inserted binder, no `VEnv.WF`, no `OnCtx`, and
the binder may be assumed to have no inhabitant in the context below the cut. -/
def VEnv.ProjSkipUninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
    Ctx.LiftN 1 k Γ Γ' →
    (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀) →
    TrProj env U Γ' s i (e.liftN 1 k) e' →
    ∃ e'', TrProj env U Γ s i e e''

theorem projStrengthen_of_skipUninhab_aux (henv : env.Ordered) (hres : env.ProjSkipUninhab U)
    {s : Lean.Name} {i : Nat} :
    ∀ (n : Nat) {l : Lift} {Γ Γ' : List VExpr} {e e' : VExpr},
      l.depth = n → Ctx.Lift' l Γ Γ' → TrProj env U Γ' s i (e.lift' l) e' →
      ∃ e'', TrProj env U Γ s i e e'' := by
  intro n
  induction n with
  | zero =>
    intro l Γ Γ' e e' hd W H
    cases W.depth_zero hd
    rw [VExpr.lift'_depth_zero hd] at H
    exact ⟨_, H⟩
  | succ n ih =>
    intro l Γ Γ' e e' hd W H
    obtain ⟨l, k, hdl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
    have step : ∃ e₂, TrProj env U Γ₂ s i (e.lift' (Lift.consN l k)) e₂ := by
      by_cases hin : ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ₂ ∧ env.HasType U Γ₀ e₀ A₀
      · obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hin
        have H2 := H.instN henv hI h₀
        rw [VExpr.inst_liftN] at H2
        exact ⟨_, H2⟩
      · exact hres W2 (fun Γ₀ A₀ e₀ hI h₀ => hin ⟨Γ₀, A₀, e₀, hI, h₀⟩) H
    obtain ⟨e₂, H₂⟩ := step
    exact ih (by simpa using hdl) W1 H₂

/-- **The reduction.**  `ProjSkipUninhab` — one binder, uninhabited — gives the whole of
`VEnv.ProjStrengthen`, hole-free, and does not even consume its `OnCtx Γ'` premise. -/
theorem VEnv.ProjSkipUninhab.projStrengthen (henv : env.Ordered)
    (hres : env.ProjSkipUninhab U) : env.ProjStrengthen U := fun _ W H =>
  projStrengthen_of_skipUninhab_aux henv hres _ rfl W H

/-- …hence the field-level residual of `ProjExistClose.lean` §1, hole-free. -/
theorem VEnv.ProjSkipUninhab.projDataStrengthen (henv : env.Ordered)
    (hres : env.ProjSkipUninhab U) : env.ProjDataStrengthen U :=
  VEnv.ProjStrengthen.projDataStrengthen (hres.projStrengthen henv)

/-- **Hole #1's exact statement, from the reduced residual, hole-free.**  Compare
`TrProj.weak'_inv_of_strengthen` (cone 3698, holes `{weakN_iff, forallE_inv_stratified,
rigidShapeUniqNS}`, watched `{HasArgs.of_mkApp, IsDefEq.uniq, IsDefEq.uniqU}`) and
`VEnv.ConstAppTypeStrengthen.projDataStrengthen` (cone 3702, the same six). -/
theorem TrProj.weak'_inv_of_skipUninhab {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name}
    {i : Nat} {e e' : VExpr} (hres : env.ProjSkipUninhab U) (henv : VEnv.WF env)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.weak'_inv_of_projStrengthen (hres.projStrengthen henv.ordered) henv hΓ' W H

/-- **Nothing is given away beyond the `OnCtx Γ'` premise**: the one-binder form is an instance
of `ProjStrengthen`, so the reduction above is tight (the sandwich of §4.1).  Mirror of
`VEnv.ConstAppTypeStrengthen.skip_step`. -/
theorem VEnv.ProjStrengthen.skip_step (h : env.ProjStrengthen U) {k : Nat}
    {Γ Γ' : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr}
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN 1 k Γ Γ')
    (H : TrProj env U Γ' s i (e.liftN 1 k) e') :
    ∃ e'', TrProj env U Γ s i e e'' := by
  have H' : TrProj env U Γ' s i (e.lift' (Lift.consN (Lift.skipN .refl 1) k)) e' := by
    rw [VExpr.lift'_consN_skipN]; exact H
  exact h hΓ' (Ctx.liftN_iff_lift'.1 W) H'

/-! ## 4. The limits of the above, proved where they can be

### 4.1 The reduction is tight
`VEnv.ProjSkipUninhab.projStrengthen` and `VEnv.ProjStrengthen.skip_step` sandwich the residual
between the hole and itself, modulo exactly one premise (`OnCtx Γ'`, which the residual does not
carry and the reduction does not use).  So no content was thrown away in the reduction; what is
open is open.

### 4.2 The residual's hypotheses are satisfiable — and here the witness is *genuinely
uninhabited*
Every anti-vacuity witness in this family so far (`constAppTypeStrengthen_fires`,
`constAppTypeStrengthen_inhab_fires`, `trProj_weak'_inv_fires`, `projDataStrengthen_fires`) has
an *inhabited* inserted binder, and each says so: they "witness satisfiability and nothing about
the obstruction".  `projSkipUninhab_fires` below has an inserted binder with **no inhabitant at
all**, proved rather than assumed.

**Scope, stated rather than implied.**  It is uninhabited for a cheap reason — the binder is an
*open* expression (`.bvar Γ.length`), so `IsDefEq.closedN'` forbids anything from being typed at
it — and therefore `OnCtx Γ'` fails at this witness.  That is legitimate here, because
`ProjSkipUninhab` (like `VEnv.ConstAppSkipUninhab`) carries no `OnCtx` premise; it is *not* a
witness for the well-formed uninhabited region, which is `VEnv.Consistent`-flavoured and remains
unexhibited anywhere in this tree.  §4.3 records what that costs. -/

/-- No term is typed at an open type: `.bvar Γ.length` is uninhabited in `Γ`. -/
theorem hasType_bvar_length_absurd (henv : env.Ordered) {Γ : List VExpr} (hΓ : CtxClosed Γ)
    {e : VExpr} : ¬ env.HasType U Γ e (.bvar Γ.length) := by
  intro h
  have := (h.closedN' henv.closed hΓ).2.2
  simp [VExpr.ClosedN] at this

theorem ctxClosed_prjCtx : CtxClosed prjCtx := ⟨trivial, by simp [VExpr.ClosedN]⟩

/-- **The reduced residual is not vacuous, with an uninhabited inserted binder.**  At `prjEnv`,
inserting the open binder `.bvar 1` above `prjCtx`: the lift holds, the binder has no inhabitant
in `prjCtx`, the premise `TrProj` holds at the larger context (by `TrProj.weakN` from
`prjEnv_trProj`), and the conclusion holds at the smaller one. -/
theorem projSkipUninhab_fires :
    Ctx.LiftN 1 0 prjCtx (VExpr.bvar 1 :: prjCtx) ∧
      (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ 0 (VExpr.bvar 1 :: prjCtx) prjCtx →
        ¬ prjEnv.HasType 0 Γ₀ e₀ A₀) ∧
      (∃ e', TrProj prjEnv 0 (VExpr.bvar 1 :: prjCtx) `Prj 0 ((VExpr.bvar 0).liftN 1 0) e') ∧
      (∃ e'', TrProj prjEnv 0 prjCtx `Prj 0 (.bvar 0) e'') := by
  refine ⟨.one, ?_, ⟨_, prjEnv_trProj.weakN prjEnv_ordered .one⟩, _, prjEnv_trProj⟩
  intro Γ₀ A₀ e₀ hI h
  cases hI with
  | zero => exact hasType_bvar_length_absurd prjEnv_ordered ctxClosed_prjCtx h

/-! ### 4.3 What resists, and why — the honest verdict

After §1–§3 the *entire* remaining content of hole #1 is:

> one binder `A₀`, with no inhabitant in the context `Γ₀` below the cut, and a `TrProj`
> derivation at `Γ'` whose subject is `e.liftN 1 k`; produce a `TrProj` at `Γ`.

Nine of `TrProj.mk`'s ten fields are free in that situation: `hS`, the three lengths, `hi`, `hlv`
and `hF17` mention no context at all, and the two `HasArgs` fields travel with the major premise
under `TrProj.instN` whenever the major premise does.  The one that does not travel is `hty`,
    `env.HasType U Γ' (e.lift' l) ((VExpr.const S us).mkApp (ps ++ ιs))`,
because `ps`/`ιs` may mention the stripped variable, so the *type* must be re-chosen — which is
why `ProjDataStrengthen` existentially requantifies `D'`, `T'`, `C'`, `us'`, `ps'`, `ιs'` rather
than reusing the input block.  That is a **typing-strengthening** obligation, i.e. the content
`ProjWeakInvSplit.lean` isolates as `VEnv.TypingStrengthening` +
`VEnv.ConstAppDefeqStrengthen`, and it is the census's own `IsDefEqU.weakN_iff` neighbourhood.

**Unproved, not false.**  Two facts here bound the failure modes, and neither leaves room for a
counterexample of the usual kind:

* the region where it could fail is exactly the *uninhabited* one (§1 and §2: everywhere else
  it is a theorem, hole-free), and
* exhibiting an uninhabited type over a `VEnv.WF` environment is itself equivalent to
  `env.Consistent` (`ProjInhab.lean` §1), which nothing in this tree proves.

So a refutation would have to produce, at a `VEnv.WF` environment, a *consistency witness*
together with a projection that strengthens nowhere — strictly more than a refutation of the
statement, and strictly more than any refutation in this tree has ever needed.  Conversely a
proof cannot come from instantiation alone: `projSkipUninhab_fires` shows the hypotheses are
satisfiable, and §4.2's scope note shows the cheap witness dies as soon as `OnCtx Γ'` is
demanded.  This is the sharpest statement of the obstruction I can make without either
`VEnv.Consistent` or `VEnv.TypingStrengthening`.

### 4.4 Citability
Everything above is downstream of `Verify/Typing/Lemmas.lean` (this file imports
`ProjExistClose.lean` → `ProjWeakInv.lean` → `Lemmas.lean`), so **none of it can discharge the
`sorry` in place**.  The one exception worth naming is the instrument, not the result:
`TrProj.instN` is *already* in `Lemmas.lean`, 1200 lines below the hole, so §1–§3 could be
moved into that file verbatim with no new imports.  `docs/handoff-projdata.md` §3 states that
migration exactly; this stream does not make it, because `Verify/Typing/Lemmas.lean` is not
its file.
-/

end Lean4Lean
