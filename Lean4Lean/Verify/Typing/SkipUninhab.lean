import Lean4Lean.Verify.Typing.ProjDataAttack
import Lean4Lean.Theory.Typing.Strengthen

/-!
# `VEnv.ProjSkipUninhab` — the decoration is free, and `OnCtx Γ'` can be got back

Round of 2026-09-05, stream `skipuninhab`.  Ledger: `docs/handoff-skipuninhab.md`.

`Verify/Typing/ProjDataAttack.lean` §3 reduces hole #1 (`TrProj.weak'_inv`,
`Verify/Typing/Lemmas.lean`:926) to `VEnv.ProjSkipUninhab` — *one inserted binder, which may be
assumed uninhabited in its own prefix* — hole-free, at cone 3412 against the previous best route's
3698 with three holes.  Two defects of that residual are on the record and both are repaired here.

## What was on the record

* `ProjInhab.lean` §3, and `docs/handoff-projdata.md` §5.2: the one-binder form carries **no
  `OnCtx Γ'`**, so it is *strictly stronger* than the hole, its uninhabitedness premise is
  satisfiable by junk binders that the hole's `OnCtx Γ'` excludes, and *"it cannot be repaired by
  adding `OnCtx Γ'` without re-importing the gate"*.  **That last claim is literally correct and
  this file confirms it** — §3 route B is exactly the re-import, measured.  What it does not say,
  and what §2 shows, is that the *goal* of the localisation is reachable without either: give up
  "one binder" instead of giving up `OnCtx Γ'`.
* `docs/handoff-projdata.md` §6: no refutation of `ProjSkipUninhab` was attempted.

## What this file establishes, all hole-free

**§1.  At one binder the uninhabitedness decoration is *free*.**  `ProjSkipUninhab` is
**equivalent**, over any `Ordered` environment, to the same statement with the uninhabitedness
premise deleted (`VEnv.ProjSkipOne`).  So "may be assumed uninhabited" buys nothing at the
one-binder level: any argument that hoped to *use* the missing inhabitant has, by this
equivalence, no more to work with than the unrestricted one-binder statement.  The decoration
earns its keep only when it is attached to the *whole* lift, which is §2.

**§2.  `OnCtx Γ'` can be kept, and keeping it needs no gate.**  `VEnv.ProjStrengthenUninhab` — the hole's own
statement (arbitrary `Ctx.Lift'`, `OnCtx Γ'` **retained**) restricted to lifts at least one of
whose inserted binders is uninhabited — is **equivalent** to `VEnv.ProjStrengthen`, i.e. to the
hole, over any `Ordered` environment.  Both directions are hole-free and neither mentions
`OnCtx.weak'_inv`, `IsDefEqU.weakN_iff`, Church–Rosser or `HasArgs.of_mkApp`.  The move the
earlier rounds missed: do not reduce to *one* binder.  Peel binders as before, and at the first
uninhabited one hand the residual the **whole remaining lift** rather than a single step — then
`OnCtx Γ'` never has to be transported across an uninhabited binder, because it is used only
where it was given.  This is a strict improvement on `ProjSkipUninhab`: that statement is `⟹`
the hole and might be false while the hole is true; this one is `⟺` the hole.

**§3.  The sharpest one-binder form, and the whole of what it borrows.**
`VEnv.ProjSkip1Uninhab` — one binder, uninhabited, carrying `OnCtx Γ` **and** `OnCtx Γ'` — gives
the hole given only `VEnv.OnCtxSkip1`: *`OnCtx` descends across one inserted binder*.  That is
strictly smaller than hole #2 (no conversion statement appears in it) and it is available two
ways.  **Route A**: `VEnv.Strengthening1Uninhab` (`Theory/Typing/Strengthen.lean` §12, hole #2's
own residual, already `iff` with hole #2's target) supplies it hole-free through
`Strengthening1.onCtx_inv` — the single step at which `IsDefEqU.weakN_iff` enters
`TrProj.weak'_inv` (`Lemmas.lean`:882-884).  So the two live holes are **ordered**: paying #2 buys
back both well-formedness premises here.  **Route B**: `VEnv.WF` alone supplies it, through the
standing theorem `OnCtx.weakN_inv`, at holes `{weakN_iff, forallE_inv_stratified}` and watched
`{IsDefEq.uniq, IsDefEq.uniqU}` — already two names fewer than the previously best route to
hole #1, from a strictly weaker residual.  `ProjSkip1Uninhab` is also an *instance* of the hole
(`VEnv.ProjStrengthen.skip1Uninhab`), so the two sandwich and nothing is conceded.

**§4.  Limits, proved.**  The new residuals are vacuous wherever no type is uninhabited
(`VEnv.AllTypesInhabited.projSkip1Uninhab`) and their premises are satisfiable exactly at a
well-formed context with an uninhabited entry (`projSkip1Uninhab_premises`) — so their
non-vacuity is `VEnv.Consistent`-flavoured, exactly as `Strengthening1Uninhab`'s is, and the
tree's only uninhabited-binder witness (`projSkipUninhab_fires`) does **not** satisfy them:
`onCtx_projSkipUninhab_fires_false` proves its context is ill-formed.  That is the price of the
repair, stated rather than implied: `ProjSkipUninhab` is non-vacuous and possibly false;
§2's and §3's residuals are of unknown vacuity and true iff the hole is.

## Verdict on the question asked

`ProjSkipUninhab` is **neither proved nor refuted** here, and §1–§3 show its truth is **not
needed**: §2's residual is equivalent to the hole and §3's is the sharpest one-binder form, so no
future round need carry a residual that is strictly stronger than what it is trying to prove.
The census does not move; nothing here is citable from `Lemmas.lean` (this file is downstream),
and the §2/§3 statements would have to be migrated there, exactly as
`docs/handoff-projdata.md` §3 describes for `TrProj.instN`.
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat}

/-! ## 1. At one binder, the uninhabitedness decoration is free -/

/-- `VEnv.ProjSkipUninhab` with the uninhabitedness premise **deleted**: strengthening of a
`TrProj` derivation across a single inserted binder, at contexts that need not be well formed. -/
def VEnv.ProjSkipOne (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
    Ctx.LiftN 1 k Γ Γ' →
    TrProj env U Γ' s i (e.liftN 1 k) e' →
    ∃ e'', TrProj env U Γ s i e e''

theorem VEnv.ProjSkipOne.skipUninhab (H : env.ProjSkipOne U) : env.ProjSkipUninhab U :=
  fun W _ H2 => H W H2

/-- **The decoration is free.**  Classical case split on the inserted binder: if it has an
inhabitant, `TrProj.instN` closes the goal outright.  Mirror of
`VEnv.Strengthening1Uninhab.strengthening1`, at `TrProj`. -/
theorem VEnv.ProjSkipUninhab.projSkipOne (henv : env.Ordered) (H : env.ProjSkipUninhab U) :
    env.ProjSkipOne U := by
  intro k Γ Γ' s i e e' W H2
  by_cases hin : ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ ∧ env.HasType U Γ₀ e₀ A₀
  · obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hin
    have H3 := H2.instN henv hI h₀
    rw [VExpr.inst_liftN] at H3
    exact ⟨_, H3⟩
  · exact H W (fun Γ₀ A₀ e₀ hI h₀ => hin ⟨Γ₀, A₀, e₀, hI, h₀⟩) H2

/-- **§1's statement.**  `ProjSkipUninhab` says no more and no less than the undecorated
one-binder statement. -/
theorem VEnv.projSkipUninhab_iff_projSkipOne (henv : env.Ordered) :
    env.ProjSkipUninhab U ↔ env.ProjSkipOne U :=
  ⟨fun H => H.projSkipOne henv, fun H => H.skipUninhab⟩

/-! ## 2. The repair: `OnCtx Γ'` retained, and the residual becomes *equivalent* to the hole -/

/-- **`l` inserts, at position `k`, a binder with no inhabitant below it.**  Stated at the exact
decomposition `Lift.depth_succ` produces, so the induction of §2 can supply it and nothing
weaker is asked of the residual. -/
def VEnv.LiftUninhabAt (env : VEnv) (U : Nat) (l : Lift) (Γ' : List VExpr) : Prop :=
  ∃ (l₀ : Lift) (k : Nat) (Γ₂ : List VExpr),
    l = Lift.consN (Lift.skip l₀) k ∧ Ctx.LiftN 1 k Γ₂ Γ' ∧
      ∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ₂ → ¬ env.HasType U Γ₀ e₀ A₀

/-- **The repaired residual.**  `VEnv.ProjStrengthen` — the hole, `OnCtx Γ'` and all — restricted
to lifts one of whose inserted binders is uninhabited.  Unlike `VEnv.ProjSkipUninhab` this is an
*instance* of the hole, so it cannot be false unless the hole is. -/
def VEnv.ProjStrengthenUninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name} {i : Nat} {e e' : VExpr},
    OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' → env.LiftUninhabAt U l Γ' →
    TrProj env U Γ' s i (e.lift' l) e' → ∃ e'', TrProj env U Γ s i e e''

theorem VEnv.ProjStrengthen.uninhab (H : env.ProjStrengthen U) : env.ProjStrengthenUninhab U :=
  fun hΓ' W _ H2 => H hΓ' W H2

theorem projStrengthen_of_strengthenUninhab_aux (henv : env.Ordered)
    (hres : env.ProjStrengthenUninhab U) {s : Lean.Name} {i : Nat} :
    ∀ (n : Nat) {l : Lift} {Γ Γ' : List VExpr} {e e' : VExpr},
      l.depth = n → OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
      TrProj env U Γ' s i (e.lift' l) e' → ∃ e'', TrProj env U Γ s i e e'' := by
  intro n
  induction n with
  | zero =>
    intro l Γ Γ' e e' hd _ W H
    cases W.depth_zero hd
    rw [VExpr.lift'_depth_zero hd] at H
    exact ⟨_, H⟩
  | succ n ih =>
    intro l Γ Γ' e e' hd hΓ' W H
    obtain ⟨l₀, k, hdl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W1, W2⟩ := W.of_cons_skip
    by_cases hin : ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ₂ ∧ env.HasType U Γ₀ e₀ A₀
    · obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hin
      rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
      have H2 := H.instN henv hI h₀
      rw [VExpr.inst_liftN] at H2
      exact ih (by simpa using hdl) (Ctx.InstN.wf henv hI h₀ hΓ').2 W1 H2
    · exact hres hΓ' W ⟨l₀, k, Γ₂, rfl, W2, fun Γ₀ A₀ e₀ hI h₀ => hin ⟨Γ₀, A₀, e₀, hI, h₀⟩⟩ H

/-- **The repair.**  The uninhabited-lift restriction of the hole gives the whole hole, with
`OnCtx Γ'` never transported across an uninhabited binder — so no `OnCtx.weak'_inv`, hence no
`IsDefEqU.weakN_iff`.  Note precisely what this does and does not contradict: `ProjInhab.lean` §3
says `OnCtx Γ'` cannot be added *to the one-binder form* for free, and that is true (§3 route B
pays for it).  Here the lift is not reduced to one binder at all, and then it is free. -/
theorem VEnv.ProjStrengthenUninhab.projStrengthen (henv : env.Ordered)
    (hres : env.ProjStrengthenUninhab U) : env.ProjStrengthen U := fun hΓ' W H =>
  projStrengthen_of_strengthenUninhab_aux henv hres _ rfl hΓ' W H

/-- **§2's statement**: the restriction to uninhabited lifts is not a weakening at all. -/
theorem VEnv.projStrengthenUninhab_iff (henv : env.Ordered) :
    env.ProjStrengthenUninhab U ↔ env.ProjStrengthen U :=
  ⟨fun H => H.projStrengthen henv, fun H => H.uninhab⟩

/-- Hole #1's exact statement from §2's residual, hole-free. -/
theorem TrProj.weak'_inv_of_strengthenUninhab {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name}
    {i : Nat} {e e' : VExpr} (hres : env.ProjStrengthenUninhab U) (henv : VEnv.WF env)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.weak'_inv_of_projStrengthen (hres.projStrengthen henv.ordered) henv hΓ' W H

/-- The chain of §1 into §2: `ProjSkipUninhab` still implies the hole, now through the repaired
residual, so §2 supersedes it rather than competing with it. -/
theorem VEnv.ProjSkipUninhab.projStrengthenUninhab (henv : env.Ordered)
    (H : env.ProjSkipUninhab U) : env.ProjStrengthenUninhab U :=
  VEnv.ProjStrengthen.uninhab (H.projStrengthen henv)

/-! ## 3. One binder *and* both well-formedness premises

The borrowed ingredient is isolated first, because it turns out to be strictly smaller than
hole #2: all §3 needs is **`OnCtx` strengthening across a single binder**, with no conversion
statement anywhere.  That statement is a *theorem in the tree today* (`OnCtx.weakN_inv`,
`Theory/Typing/UniqueTyping.lean`:250) at a measured price of two holes and two watched names —
already less than the previously best route to hole #1 — and it is *also* supplied hole-free by
hole #2's own residual.  So §3 gives two routes with different bills, and both are recorded. -/

/-- **The whole of what §3 borrows**: `OnCtx` descends across one inserted binder.  `n = 1`
instance of `OnCtx.weakN_inv`; no `IsDefEqU`, no `TrProj`. -/
def VEnv.OnCtxSkip1 (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr}, Ctx.LiftN 1 k Γ Γ' →
    OnCtx Γ' (env.IsType U) → OnCtx Γ (env.IsType U)

/-- Hole #2's residual supplies it, hole-free — through `Strengthening1.onCtx_inv`, which is
exactly the single step at which `IsDefEqU.weakN_iff` enters `TrProj.weak'_inv`. -/
theorem VEnv.Strengthening1Uninhab.onCtxSkip1 (henv : VEnv.WF env)
    (hS : VEnv.Strengthening1Uninhab env U) : env.OnCtxSkip1 U :=
  fun W hΓ' => VEnv.Strengthening1.onCtx_inv henv (hS.strengthening1 henv.ordered) W hΓ'

/-- And so does `VEnv.WF` on its own — at the price the tree already pays for
`OnCtx.weakN_inv`: holes `{weakN_iff, forallE_inv_stratified}`, watched `{uniq, uniqU}`.  Kept
separate from everything else in this file so the taint is visible in one place. -/
theorem VEnv.onCtxSkip1_of_wf (henv : VEnv.WF env) : env.OnCtxSkip1 U :=
  fun W hΓ' => OnCtx.weakN_inv henv W hΓ'

/-- **The sharpest one-binder form**: one inserted binder, assumed uninhabited in its own prefix,
with `OnCtx` for **both** contexts.  Exactly `VEnv.Strengthening1Uninhab`'s shape
(`Theory/Typing/Strengthen.lean` §12) with `IsDefEqU` replaced by `TrProj`. -/
def VEnv.ProjSkip1Uninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {s : Lean.Name} {i : Nat} {e e' : VExpr},
    Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → ¬ env.HasType U Γ₀ e₀ A₀) →
    TrProj env U Γ' s i (e.liftN 1 k) e' →
    ∃ e'', TrProj env U Γ s i e e''

/-- **The converse half of §3's sandwich**: the sharpest form is an *instance* of the hole, so §3
concedes nothing beyond `Strengthening1Uninhab`. -/
theorem VEnv.ProjStrengthen.skip1Uninhab (H : env.ProjStrengthen U) : env.ProjSkip1Uninhab U :=
  fun W _ hΓ' _ H2 => H.skip_step hΓ' W H2

theorem projStrengthen_of_skip1Uninhab_aux (henv : env.Ordered)
    (hO : env.OnCtxSkip1 U) (hres : env.ProjSkip1Uninhab U)
    {s : Lean.Name} {i : Nat} :
    ∀ (n : Nat) {l : Lift} {Γ Γ' : List VExpr} {e e' : VExpr},
      l.depth = n → OnCtx Γ' (env.IsType U) → Ctx.Lift' l Γ Γ' →
      TrProj env U Γ' s i (e.lift' l) e' → ∃ e'', TrProj env U Γ s i e e'' := by
  intro n
  induction n with
  | zero =>
    intro l Γ Γ' e e' hd _ W H
    cases W.depth_zero hd
    rw [VExpr.lift'_depth_zero hd] at H
    exact ⟨_, H⟩
  | succ n ih =>
    intro l Γ Γ' e e' hd hΓ' W H
    obtain ⟨l₀, k, hdl, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W1, W2⟩ := W.of_cons_skip
    have hΓ₂ : OnCtx Γ₂ (env.IsType U) := hO W2 hΓ'
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, ← Lift.skipN_one, VExpr.lift'_consN_skipN] at H
    have step : ∃ e₂, TrProj env U Γ₂ s i (e.lift' (Lift.consN l₀ k)) e₂ := by
      by_cases hin : ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ₂ ∧ env.HasType U Γ₀ e₀ A₀
      · obtain ⟨Γ₀, A₀, e₀, hI, h₀⟩ := hin
        have H2 := H.instN henv hI h₀
        rw [VExpr.inst_liftN] at H2
        exact ⟨_, H2⟩
      · exact hres W2 hΓ₂ hΓ' (fun Γ₀ A₀ e₀ hI h₀ => hin ⟨Γ₀, A₀, e₀, hI, h₀⟩) H
    obtain ⟨e₂, H₂⟩ := step
    exact ih (by simpa using hdl) hΓ₂ W1 H₂

/-- **Hole #1 from the sharpest one-binder form plus one-binder `OnCtx` strengthening.**
Everything else is `TrProj.instN`. -/
theorem VEnv.ProjSkip1Uninhab.projStrengthen (henv : env.Ordered) (hO : env.OnCtxSkip1 U)
    (hres : env.ProjSkip1Uninhab U) : env.ProjStrengthen U := fun hΓ' W H =>
  projStrengthen_of_skip1Uninhab_aux henv hO hres _ rfl hΓ' W H

/-- Route A: hole #2's residual pays for `OnCtxSkip1`, so this reduction is hole-free. -/
theorem VEnv.ProjSkip1Uninhab.projStrengthen_of_strengthening (henv : VEnv.WF env)
    (hS : VEnv.Strengthening1Uninhab env U) (hres : env.ProjSkip1Uninhab U) :
    env.ProjStrengthen U :=
  hres.projStrengthen henv.ordered (hS.onCtxSkip1 henv)

/-- Route B: `VEnv.WF` alone pays for it, at the tree's standing price for `OnCtx.weakN_inv`.
This is the row to compare with `TrProj.weak'_inv_of_strengthen` (3698, three holes, three
watched): the same conclusion from a *strictly weaker* residual, and two of the six names gone. -/
theorem VEnv.ProjSkip1Uninhab.projStrengthen_of_wf (henv : VEnv.WF env)
    (hres : env.ProjSkip1Uninhab U) : env.ProjStrengthen U :=
  hres.projStrengthen henv.ordered (VEnv.onCtxSkip1_of_wf henv)

/-- **§3's statement, as an iff.**  Modulo one-binder `OnCtx` strengthening, the sharpest
one-binder form *is* hole #1. -/
theorem VEnv.projSkip1Uninhab_iff (henv : env.Ordered) (hO : env.OnCtxSkip1 U) :
    env.ProjSkip1Uninhab U ↔ env.ProjStrengthen U :=
  ⟨fun H => H.projStrengthen henv hO, fun H => H.skip1Uninhab⟩

/-- Hole #1's exact statement from §3 route A, hole-free. -/
theorem TrProj.weak'_inv_of_skip1Uninhab {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name}
    {i : Nat} {e e' : VExpr} (hS : VEnv.Strengthening1Uninhab env U)
    (hres : env.ProjSkip1Uninhab U) (henv : VEnv.WF env)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.weak'_inv_of_projStrengthen (hres.projStrengthen_of_strengthening henv hS) henv hΓ' W H

/-- Hole #1's exact statement from §3 route B: from `ProjSkip1Uninhab` **alone**, at a
`VEnv.WF` environment. -/
theorem TrProj.weak'_inv_of_skip1Uninhab_wf {Γ Γ' : List VExpr} {l : Lift} {s : Lean.Name}
    {i : Nat} {e e' : VExpr} (hres : env.ProjSkip1Uninhab U) (henv : VEnv.WF env)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' l Γ Γ')
    (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' :=
  TrProj.weak'_inv_of_projStrengthen (hres.projStrengthen_of_wf henv) henv hΓ' W H

/-! ## 4. The limits of §1–§3, proved where they can be

### 4.1 Vacuity, in both directions -/

/-- **The vacuity dual.**  Wherever every type of every well-formed context is inhabited, §3's
residual has unsatisfiable premises — so it carries content exactly to the extent that
uninhabited types over well-formed contexts exist.  Mirror of
`strengtheningTarget_of_allInhabited`. -/
theorem VEnv.AllTypesInhabited.projSkip1Uninhab
    (hinh : env.AllTypesInhabited U) : env.ProjSkip1Uninhab U := by
  intro k Γ Γ' s i e e' W _ hΓ' hun _
  obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W.exists_instN_typed hΓ'
  obtain ⟨e₀, h₀⟩ := hinh hΓ₀ hA₀
  exact absurd h₀ (hun Γ₀ A₀ e₀ (hI e₀))

/-- **Premise satisfiability for §3's residual**, at the innermost position, where the
uninhabitedness hypothesis is literally "`A` has no inhabitant in `Γ`".  Mirror of
`VEnv.onCtx_uninhab_premises`. -/
theorem projSkip1Uninhab_premises {Γ : List VExpr} {A : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hA : env.IsType U Γ A)
    (hemp : ∀ e₀, ¬ env.HasType U Γ e₀ A) :
    Ctx.LiftN 1 0 Γ (A :: Γ) ∧ OnCtx Γ (env.IsType U) ∧ OnCtx (A :: Γ) (env.IsType U) ∧
      ∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ 0 (A :: Γ) Γ → ¬ env.HasType U Γ₀ e₀ A₀ :=
  VEnv.onCtx_uninhab_premises hΓ hA hemp

/-! ### 4.2 The one uninhabited-binder witness in the tree does **not** satisfy them

`projSkipUninhab_fires` (`ProjDataAttack.lean` §4.2) is the family's only witness with a
genuinely uninhabited inserted binder, and it is uninhabited because the binder is an *open*
expression.  That is exactly what `OnCtx Γ'` forbids, and here it is proved rather than
asserted: so §2's and §3's residuals are of **unknown** vacuity, while `ProjSkipUninhab` is
known non-vacuous.  This is the price of the repair. -/

/-- No term of an ill-indexed variable is typed: `.bvar j` with `Γ.length ≤ j` has no type in `Γ`. -/
theorem hasType_bvar_ge_length_absurd (henv : env.Ordered) {Γ : List VExpr} (hΓ : CtxClosed Γ)
    {j : Nat} (hj : Γ.length ≤ j) {A : VExpr} : ¬ env.HasType U Γ (.bvar j) A := by
  intro h
  have := (h.closedN' henv.closed hΓ).2.1
  simp [VExpr.ClosedN] at this
  omega

/-- **The inserted binder of `projSkipUninhab_fires` is not a type**, so its context is
ill-formed and the witness is outside §2's and §3's premises. -/
theorem onCtx_projSkipUninhab_fires_false :
    ¬ OnCtx (VExpr.bvar 1 :: prjCtx) (prjEnv.IsType 0) := by
  intro ⟨_, u, hA⟩
  exact hasType_bvar_ge_length_absurd prjEnv_ordered ctxClosed_prjCtx (by simp [prjCtx]) hA

/-! ### 4.3 What is still open, stated exactly

After §1–§3 the remaining content of hole #1 is, in the sharpest available form:

> a context `Γ'` well formed in a `VEnv.WF` environment, one of whose entries `A₀` has **no
> inhabitant** in its own prefix; a `TrProj` derivation at `Γ'` whose subject skips that entry;
> produce a `TrProj` derivation at the context with the entry removed — whose well-formedness
> may itself be assumed (§3) or which may be reached in one step from `Γ'` (§2).

Three facts bound the failure modes, and none leaves room for a counterexample of the usual kind.
`VEnv.AllTypesInhabited.projStrengthen` (`ProjDataAttack.lean` §2) makes hole #1 a theorem
wherever no type is uninhabited; §4.1 makes §3's residual *vacuous* there; and `ProjInhab.lean`
§1 pins the existence of an uninhabited type over a well-formed context to `env.Consistent` by an
iff.  So a refutation would have to produce a consistency witness **plus** a projection that
strengthens nowhere — strictly more than any refutation in this tree has needed.

**Unproved, not false**, and — the new part — **no longer requiring a residual stronger than the
hole**.  What §1 additionally rules out is one specific hope: that the *uninhabitedness* of the
binder is a resource a proof could consume.  At one binder it is provably free (§1), so any proof
of §3's residual must come from `OnCtx Γ`, `OnCtx Γ'` and the `TrProj` derivation alone, exactly
as `Strengthening1Uninhab`'s must.
-/

end Lean4Lean
