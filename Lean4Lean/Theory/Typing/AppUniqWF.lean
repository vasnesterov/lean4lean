import Lean4Lean.Theory.Typing.SortDisjPiLvl
import Lean4Lean.Theory.Typing.DeclRules

/-!
# `∀ n, AppUniqLvl` at `VEnv.WF`: `IsDeclRule.lhs_shape` cannot be the missing content

`Theory/Typing/AppUniqRefute.lean` refutes `∀ n, AppUniqLvl` at an `Ordered` environment and
observes that the witness is **not** `VEnv.WF` (`piLvlEnv_not_wf`, via
`VDefEq.IsDeclRule.lhs_ne_forallE`).  `docs/handoff-sortinv-route.md` §13.4 item 1 and
`docs/vacuity-ledger.md` row 144b draw the conclusion that

> any proof must consume `IsDeclRule.lhs_shape`, and none can run on `Ordered` alone,

and §21 item 2 then re-ranks that attack **above** `SortDisjInvN piLvlEnv 0 1` on the ground
that it "does *not* sit behind the index-1 wall".

**That last claim is false, and this file refutes it.**  The whole `app`-case family is
**antitone in the environment**, and `∅` is `VEnv.WF`.  So

* `∀ n, AppUniqLvl preludeEnv 0 n → ∀ n, AppUniqLvl ∅ 0 n` — and likewise from *any*
  environment whatever, `WF` or not;
* the `VEnv.WF`-quantified target implies the same;
* and **no hypothesis implied by `VEnv.WF` can avoid that**, because every such hypothesis
  holds at `∅` (`wf_hypothesis_holds_at_empty`).  `IsDeclRule.lhs_shape` is a hypothesis about
  `env.defeqs`; at `∅` there are no rules at all, so it is available in a *strictly stronger*
  form than at any other environment and still leaves the whole target to prove.

So the `VEnv.WF` route sits behind an empty-environment index-1 clause exactly as item (c)
does, and `lhs_shape`'s job is only to exclude the `Ordered` counterexample — it supplies
none of the positive content.

Grading, up front (this corner's rule): **the bound is one-way.**  Refuting
`AppUniqLvl ∅ 0 1` refutes the target at every environment; *proving* it proves nothing about
`preludeEnv`.  So this is a **necessary condition, possibly strictly weaker** than the target —
not a reduction, and not a collapse.  Nothing here discharges anything.
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## 1. `∅` is at the bottom, and it is well-formed

Both facts are one line each; the point is that they are *both* true of the same environment,
which is what makes §3 work. -/

/-- `∅` is below every environment: it has no constants and no rules. -/
theorem emptyEnv_le {env : VEnv} : (∅ : VEnv) ≤ env := ⟨nofun, nofun⟩

/-- `∅` has no rules at all — the maximally strong form of every conclusion
`VDefEq.IsDeclRule.lhs_shape` can ever deliver. -/
theorem emptyEnv_no_defeqs {df : VDefEq} : ¬ (∅ : VEnv).defeqs df := nofun

/-- `∅` is `VEnv.WF`. -/
theorem wf_emptyEnv : VEnv.WF (∅ : VEnv) := ⟨[], .empty⟩

/-- …so `WF.defeq_isDeclRule`'s conclusion is available at `∅` for free, with no content: there
is nothing for it to classify. -/
theorem emptyEnv_isDeclRule {df : VDefEq} : (∅ : VEnv).defeqs df → df.IsDeclRule := nofun

/-! ## 2. The whole `app`-case family is antitone in the environment

`Stratified.mono_env` (`Theory/Typing/SortDisjPiLvl.lean` §1) transfers every `⊢ₙ` derivation
up an environment extension, and each of these statements has its environment **only** in its
premises: the conclusions are level equivalences.  So the *larger* environment's statement is
the *stronger* one, and the target at any environment implies the target at `∅`. -/

theorem AppData.mono_env {env env' : VEnv} (le : env ≤ env') {Γ : List VExpr}
    {f a A₀ B₀ A₁ B₁ : VExpr} (h : AppData env U n Γ f a A₀ B₀ A₁ B₁) :
    AppData env' U n Γ f a A₀ B₀ A₁ B₁ :=
  ⟨h.fn₀.mono_env le, h.arg₀.mono_env le, h.fn₁.mono_env le, h.arg₁.mono_env le⟩

theorem AppUniqLvl.mono_env {env env' : VEnv} (le : env ≤ env')
    (h : env'.AppUniqLvl U n) : env.AppUniqLvl U n :=
  fun d c₀ c₁ => h (d.mono_env le) (c₀.mono_env le) (c₁.mono_env le)

theorem PropUniqN.mono_env {env env' : VEnv} (le : env ≤ env')
    (h : env'.PropUniqN U n) : env.PropUniqN U n :=
  fun h₀ h₁ => h (h₀.mono_env le) (h₁.mono_env le)

theorem PropUniqZeroN.mono_env {env env' : VEnv} (le : env ≤ env')
    (h : PropUniqZeroN env' U n) : PropUniqZeroN env U n :=
  fun h₀ h₁ => h (h₀.mono_env le) (h₁.mono_env le)

/-- The **guarded** form is antitone too — the guard `OnCtx Γ (env.IsType U)` is monotone in the
environment (`IsType.mono`), so it transfers in the same direction as the typings and does not
block the bound.  This matters because the guard is exactly §9.3's proposed weakening. -/
theorem PropUniqNOn.mono_env {env env' : VEnv} (le : env ≤ env')
    (h : PropUniqNOn env' U n) : PropUniqNOn env U n :=
  fun hΓ h₀ h₁ => h (hΓ.mono fun ht => ht.mono le) (h₀.mono_env le) (h₁.mono_env le)

/-- `PropUniqN.AppCase`, the tree's own spelling, likewise. -/
theorem PropUniqN.AppCase.mono_env {env env' : VEnv} (le : env ≤ env')
    (h : PropUniqN.AppCase env' U n) : PropUniqN.AppCase env U n :=
  fun hf ha hc happ =>
    h (hf.mono_env le) (ha.mono_env le) (hc.mono_env le) (happ.mono_env le)

/-- Antitone in the universe count too, so the refutations the tree states at `U = 1` and the
targets it states at `U = 0` sit in one chain. -/
theorem AppUniqLvl.mono_univs {U U' : Nat} (le : U ≤ U') (h : env.AppUniqLvl U' n) :
    env.AppUniqLvl U n :=
  fun d c₀ c₁ => h ⟨d.fn₀.mono_univs le, d.arg₀.mono_univs le, d.fn₁.mono_univs le,
    d.arg₁.mono_univs le⟩ (c₀.mono_univs le) (c₁.mono_univs le)

/-! ## 3. The lower bound: the target at **any** environment implies the target at `∅`

This is the exact analogue of `sortDisjInvN_le`, and it is what §21 item 2 missed. -/

/-- **The bound.**  `∅ ≤ env` always, so `AppUniqLvl env U n` is the stronger statement. -/
theorem appUniqLvl_le (h : env.AppUniqLvl U n) : (∅ : VEnv).AppUniqLvl U n :=
  AppUniqLvl.mono_env emptyEnv_le h

theorem appUniqLvl_all_le (h : ∀ n, env.AppUniqLvl U n) : ∀ n, (∅ : VEnv).AppUniqLvl U n :=
  fun n => appUniqLvl_le (h n)

theorem propUniqN_le (h : env.PropUniqN U n) : (∅ : VEnv).PropUniqN U n :=
  PropUniqN.mono_env emptyEnv_le h

theorem propUniqZeroN_le (h : PropUniqZeroN env U n) : PropUniqZeroN (∅ : VEnv) U n :=
  PropUniqZeroN.mono_env emptyEnv_le h

theorem propUniqNOn_le (h : PropUniqNOn env U n) : PropUniqNOn (∅ : VEnv) U n :=
  PropUniqNOn.mono_env emptyEnv_le h

/-- **The `VEnv.WF`-quantified target implies the empty-environment target.**  `∅` is `WF`, so
this needs no bound at all — but the bound is what makes the *single-environment* form below
true as well, and `preludeEnv` is the environment route B actually wants. -/
theorem appUniqLvl_wf_lower (h : ∀ env : VEnv, env.WF → ∀ n, env.AppUniqLvl 0 n) :
    ∀ n, (∅ : VEnv).AppUniqLvl 0 n := h _ wf_emptyEnv

/-- The single-environment form: no matter which `WF` environment the restated route is
stated at, it entails the empty-environment clause at index 1. -/
theorem appUniqLvl_target_lower (h : ∀ n, env.AppUniqLvl 0 n) :
    (∅ : VEnv).AppUniqLvl 0 1 := appUniqLvl_le (h 1)

/-- …and the negative transfers the other way, which is the *strong* half: a refutation at `∅`
refutes the target at **every** environment, `VEnv.WF` ones included.  Contrast
`piLvlEnv_appUniqLvl_false`, which refutes the *strongest* member of the chain and therefore
leaves every weaker one — including the real target — open. -/
theorem appUniqLvl_empty_false_imp (h : ¬ (∅ : VEnv).AppUniqLvl 0 1) :
    ∀ env : VEnv, ¬ env.AppUniqLvl 0 1 := fun _ h' => h (appUniqLvl_le h')

theorem propUniqZeroN_empty_false_imp (h : ¬ PropUniqZeroN (∅ : VEnv) 0 1) :
    ∀ env : VEnv, ¬ PropUniqZeroN env 0 1 := fun _ h' => h (propUniqZeroN_le h')

/-! ## 4. …and no hypothesis implied by `VEnv.WF` can lift the target above that bound

This is the general statement, and it is what retires the route rather than one attempt at it:
`∅` is `VEnv.WF`, so **every** side condition that `VEnv.WF` implies — `Ordered`,
`WF.defeq_isDeclRule`, `IsDeclRule.lhs_shape`, `lhs_ne_forallE`, `PatternRules.WF.ruleShape`,
any future one — is *true at `∅`*.  Adding such a hypothesis therefore cannot move the goal
above `AppUniqLvl ∅ 0 1`. -/

theorem wf_hypothesis_holds_at_empty {H : VEnv → Prop} (hH : ∀ env : VEnv, env.WF → H env) :
    H (∅ : VEnv) := hH _ wf_emptyEnv

/-- **The general obstruction.**  Any proof schema of the shape "`H env → AppUniqLvl env 0 1`"
with `H` implied by `VEnv.WF` proves `AppUniqLvl ∅ 0 1` as a special case. -/
theorem no_wf_hypothesis_avoids_empty {H : VEnv → Prop} (hH : ∀ env : VEnv, env.WF → H env)
    (h : ∀ env : VEnv, H env → env.AppUniqLvl 0 1) : (∅ : VEnv).AppUniqLvl 0 1 :=
  h _ (wf_hypothesis_holds_at_empty hH)

/-- `IsDeclRule.lhs_shape` is such an `H`, spelled out. -/
theorem lhs_shape_at_wf : ∀ env : VEnv, env.WF → ∀ df : VDefEq, env.defeqs df →
    (∃ c ls, df.lhs = .const c ls) ∨ (∃ f a, df.lhs = .app f a) ∨
      ∃ A b, df.lhs = .lam A b :=
  fun _ h _ hdf => (h.defeq_isDeclRule hdf).lhs_shape

/-- **So `lhs_shape` cannot be the missing content.**  Assuming it at every environment still
leaves `AppUniqLvl ∅ 0 1` to prove. -/
theorem lhs_shape_not_enough
    (h : ∀ env : VEnv, (∀ df : VDefEq, env.defeqs df →
        (∃ c ls, df.lhs = .const c ls) ∨ (∃ f a, df.lhs = .app f a) ∨
          ∃ A b, df.lhs = .lam A b) →
      env.AppUniqLvl 0 1) : (∅ : VEnv).AppUniqLvl 0 1 :=
  h _ fun _ hdf => (emptyEnv_no_defeqs hdf).elim

/-- And neither can anything stronger that is still a constraint on the rules: **total
rule-freeness** — strictly stronger than `lhs_shape`, and false at every environment that has
any rule at all — leaves exactly the same residue. -/
theorem rule_freeness_not_enough
    (h : ∀ env : VEnv, (∀ df : VDefEq, ¬ env.defeqs df) → env.AppUniqLvl 0 1) :
    (∅ : VEnv).AppUniqLvl 0 1 := h _ fun _ => emptyEnv_no_defeqs

/-- The same for the instance route B actually consumes (`AppUniqRefute` §"the instance"). -/
theorem lhs_shape_not_enough_zero
    (h : ∀ env : VEnv, (∀ df : VDefEq, env.defeqs df →
        (∃ c ls, df.lhs = .const c ls) ∨ (∃ f a, df.lhs = .app f a) ∨
          ∃ A b, df.lhs = .lam A b) →
      PropUniqZeroN env 0 1) : PropUniqZeroN (∅ : VEnv) 0 1 :=
  h _ fun _ hdf => (emptyEnv_no_defeqs hdf).elim

/-! ## 5. What `lhs_shape` gives, and one thing it provably does **not**: `ExtraSortRed`

`lhs_shape` is *not* content-free — it is exactly what excludes the `Ordered` counterexample,
and `WF.instL_lhs_ne_sort` / `WF.instL_lhs_ne_forallE` are its two usable corollaries.  But its
reach stops at the rule's **left**-hand side: it says nothing whatever about the `rhs`, and the
one residual of the `SortRed` route that is about the environment — `ExtraSortRed` — is a
statement about *both* sides.

`ExtraSortRed` is free at `∅` (no rules) and at `piLvlEnv` (`extraSortRed_piLvlEnv`: both
sides are Π-types).  **It is not free at a `VEnv.WF` environment**, and `IsDeclRule` does not
discharge it: a δ-rule may unfold a constant *to a sort*, and `SortRed` has no δ step by
design ("no congruence below the head, no η, no δ" — `SortClauses.lean`'s own docstring).

The witness is `def P : Type 0 := Prop`, i.e. the `VDefVal` below.  Its `toDefEq` is an
`IsDeclRule` by `IsDeclRule.delta` with **no well-formedness side condition at all**, so the
refutation is of the schema "`IsDeclRule df → ExtraSortRed`-clause", which is the only form in
which `lhs_shape`'s parent could ever supply it. -/

/-- `def P : Type 0 := Prop` — a declaration whose value is a sort. -/
def sortValuedDef : VDefVal where
  uvars := 0
  type := .sort (.succ .zero)
  name := `Lean4Lean.AppUniqWF.P
  value := .sort .zero

theorem sortValuedDef_isDeclRule : sortValuedDef.toDefEq.IsDeclRule := .delta _

/-- **`IsDeclRule` does not imply the `ExtraSortRed` clause.**  So `WF env → ExtraSortRed env`
cannot be obtained through `WF.defeq_isDeclRule`, and the `SortRed` route of
`SortClauses.lean` §4 — whose fourth residual `ExtraSortRed` is free over `∅` and over
`piLvlEnv` — **does not lift to `VEnv.WF` environments** as it stands.  The repair is to give
`HeadBeta` a δ step (or to weaken `ExtraSortRed`), not to appeal to `lhs_shape`. -/
theorem isDeclRule_not_extraSortRed :
    ¬ ∀ (df : VDefEq) (ls : List VLevel) (u : VLevel), df.IsDeclRule →
      (SortRed u (df.lhs.instL ls) ↔ SortRed u (df.rhs.instL ls)) := by
  intro h
  exact SortRed.not_const
    ((h sortValuedDef.toDefEq [] .zero sortValuedDef_isDeclRule).2 (.sort rfl))

/-- Read off the same fact as a statement about environments: **if a `WF` environment has a
sort-valued δ-rule then `ExtraSortRed` fails at it**, so the `SortRed` route's environment
residual is a real obligation at `preludeEnv`, not bookkeeping. -/
theorem not_extraSortRed_of_sortValued {env : VEnv} (h : env.defeqs sortValuedDef.toDefEq) :
    ¬ ExtraSortRed env := fun H =>
  SortRed.not_const (u := .zero) ((H (ls := []) h).2 (.sort rfl))

/-! ## 6. Where the residue is, and one machine-checked constraint on any witness for it

§3–§4 leave the whole content at `AppUniqLvl ∅ 0 1`.  That statement is *not* settled here.
What is settled is a constraint that every candidate counterexample must satisfy, and it is the
constraint that kills the family of witnesses `appDF`-plus-`beta` generates over `∅`.

At index `0`, `⊢₀` types are syntactically unique (`HasTypeN.uniq_zero`) and weak-head β
reduction preserves them (`HeadBeta.hasTypeN_zero`).  Together these **pin the `SortRed` level
to the `⊢₀` type**: -/

/-- **The `⊢₀` type of a term determines the sort it weak-head reduces to.**  Reusable, and the
one-line reason the `appDF` witness family cannot separate two sorts: `appDF`'s two functions
carry *one* Π-type at `⊢₀`, so their two β-reducts inherit one `⊢₀` type. -/
theorem SortRed.type0_pin (henv : Ordered env) {Γ : List VExpr} {X : VExpr} {u v : VLevel}
    (hr : SortRed u X) : env.HasTypeN U 0 Γ X (.sort v) → ∃ w, w ≈ u ∧ v = .succ w := by
  induction hr with
  | @sort w h =>
    intro hX
    refine ⟨w, h, ?_⟩
    have he := IsDefEqN.zero_iff.1 (HasTypeN.sort_inv hX).2
    injection he with he'
    exact he'.symm
  | step hb _ ih => exact fun hX => ih (hb.hasTypeN_zero henv hX)

/-- **So two terms sharing a `⊢₀` sort type cannot weak-head reduce to sorts of different
levels** — in particular not to sorts differing on being `Prop`. -/
theorem SortRed.type0_agree (henv : Ordered env) {Γ : List VExpr} {X Y : VExpr}
    {u u' v : VLevel} (hX : env.HasTypeN U 0 Γ X (.sort v))
    (hY : env.HasTypeN U 0 Γ Y (.sort v)) (hrX : SortRed u X) (hrY : SortRed u' Y) : u ≈ u' := by
  obtain ⟨w, hw, rfl⟩ := hrX.type0_pin henv hX
  obtain ⟨w', hw', he⟩ := hrY.type0_pin henv hY
  injection he with he'
  exact hw.symm.trans (he' ▸ hw')

/-- The obligation stated over the `app` case: the two instantiated codomains share a `⊢₀` sort
type.  **Stated, not proved, and it is an added hypothesis — graded as such**: it is not a
weakening of `AppUniqLvl`, it is a side condition that the two Π-types of one term give no
reason to expect.  Its value is negative: `appCodType0_blocks` says a counterexample over `∅`
must make it fail. -/
def AppCodType0 (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr},
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    ∃ v : VLevel, env.HasTypeN U 0 Γ (B₀.inst a) (.sort v) ∧
      env.HasTypeN U 0 Γ (B₁.inst a) (.sort v)

/-- **`AppUniqLvl` at `n+1` from `SortRedInv` at `n+1` and `AppCodType0`.**  Sufficient, and
**possibly strictly stronger** than `AppUniqLvl` — no converse is claimed and none is known.
Not a reduction. -/
theorem appUniqLvl_of_sortRedInv_codType0 (henv : Ordered env)
    (hinv : SortRedInv env U (n+1)) (hct : AppCodType0 env U (n+1)) :
    env.AppUniqLvl U (n+1) := by
  intro Γ f a A₀ B₀ A₁ B₁ u v d c₀ c₁
  obtain ⟨w, h₀, h₁⟩ := hct d
  have hu : SortRed u (B₀.inst a) := (hinv c₀).2 (.sort rfl)
  have hv : SortRed v (B₁.inst a) := (hinv c₁).2 (.sort rfl)
  have : u ≈ v := SortRed.type0_agree henv h₀ h₁ hu hv
  exact ⟨fun h => this.symm.trans h, fun h => this.trans h⟩

/-- **The constraint on the witness search.**  Any refutation of `AppUniqLvl ∅ 0 (n+1)` must
refute `SortRedInv ∅ 0 (n+1)` or `AppCodType0 ∅ 0 (n+1)`.  Since a refutation of `SortRedInv`
would settle `SortInvN ∅ 0 (n+1)` — the clause §17.1 shows item (c) sits above — the *cheap*
half of the search is `AppCodType0`: the two instantiated codomains must be given **different**
`⊢₀` types, or one of them none at all. -/
theorem appUniqLvl_witness_must_break (h : ¬ (∅ : VEnv).AppUniqLvl 0 (n+1)) :
    ¬ SortRedInv (∅ : VEnv) 0 (n+1) ∨ ¬ AppCodType0 (∅ : VEnv) 0 (n+1) := by
  by_cases h1 : SortRedInv (∅ : VEnv) 0 (n+1)
  · exact .inr fun h2 => h (appUniqLvl_of_sortRedInv_codType0 .empty h1 h2)
  · exact .inl h1

/-! ### …and `AppCodType0` is **FALSE**, so the disjunction above is VOID as a constraint

Tested before being claimed, because a constraint whose second disjunct is a theorem constrains
nothing — that is this corner's fifth recorded shape of "hole-free ≠ discharged", and it would
have been the sixth here.

`Stratified` has **no regularity**: nothing forces a context entry, or the codomain of a
Π-type, to be a type at all.  So take `Γ = [K]` with `K` a **λ-term**, and `f = fun (_ : Type 0)
=> (K : the outer variable)`.  Its Π-codomain instantiates to `K`, whose `⊢₀` type is a Π-type
and (by `HasTypeN.uniq_zero`) nothing else — so it is `⊢₀`-typed at no sort whatever. -/

/-- `fun (_ : Type 0) => x` — a λ-term, hence `⊢₀`-typed at a Π and at nothing else. -/
def lamK : VExpr := .lam (.sort (.succ .zero)) (.bvar 0)

theorem lamK_lift : lamK.lift = lamK := rfl

theorem lamK_type0 {Γ : List VExpr} : (∅ : VEnv).HasTypeN 0 0 Γ lamK
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  Stratified.lam (Stratified.sort trivial) (Stratified.bvar Lookup.zero)

theorem lamK_not_sort_type0 {Γ : List VExpr} {v : VLevel} :
    ¬ (∅ : VEnv).HasTypeN 0 0 Γ lamK (.sort v) :=
  fun h => VExpr.noConfusion (HasTypeN.uniq_zero lamK_type0 h)

/-- The `AppData`: one function, one argument, the *same* Π-type twice — so not even a
two-types phenomenon is needed to break the side condition. -/
theorem lamK_appData :
    AppData (∅ : VEnv) 0 1 [lamK] (.lam (.sort (.succ .zero)) (.bvar 1)) (.sort .zero)
      (.sort (.succ .zero)) lamK.lift.lift (.sort (.succ .zero)) lamK.lift.lift :=
  have hf : (∅ : VEnv).HasTypeN 0 1 [lamK] (.lam (.sort (.succ .zero)) (.bvar 1))
      (.forallE (.sort (.succ .zero)) lamK.lift.lift) :=
    Stratified.lam (Stratified.sort trivial) (Stratified.bvar (Lookup.succ Lookup.zero))
  have ha : (∅ : VEnv).HasTypeN 0 1 [lamK] (.sort .zero) (.sort (.succ .zero)) :=
    Stratified.sort trivial
  ⟨hf, ha, hf, ha⟩

/-- **`AppCodType0` is false at `∅` at index 1** — and so, by antitonicity of its own premise,
the side condition is unavailable at every environment that this `AppData` embeds into, `WF`
ones included. -/
theorem appCodType0_one_false : ¬ AppCodType0 (∅ : VEnv) 0 1 := by
  intro h
  obtain ⟨v, h₀, -⟩ := h lamK_appData
  rw [show lamK.lift.lift.inst (.sort .zero) = lamK from by
    rw [VExpr.inst_lift, lamK_lift]] at h₀
  exact lamK_not_sort_type0 h₀

/-- **So `appUniqLvl_witness_must_break` is settled by its right disjunct and constrains
nothing.**  Recorded rather than deleted: it is the negative result, and it says exactly which
repair the side condition needs — the guard.  `AppUniqLvl` is unguarded, so the repair only
serves the *guarded* target `PropUniqNOn` (§9.3's weakening), where `OnCtx Γ (env.IsType U)`
excludes a λ-term context entry.  Whether the guarded side condition holds is **open**; it is
not proved anywhere in this file. -/
theorem appUniqLvl_witness_must_break_is_void :
    ¬ SortRedInv (∅ : VEnv) 0 1 ∨ ¬ AppCodType0 (∅ : VEnv) 0 1 := .inr appCodType0_one_false

/-! ### The refutation is robust: it is about **regularity**, not about level agreement

Two strengthenings suggest themselves and neither survives.  First, `type0_agree` does not need
a *common* type — `≈`-equal types suffice, because `.succ` is injective for `≈`.  Second, the
witness kills the weakened side condition too, for the same reason: `lamK` is `⊢₀`-typed at **no
sort at all**.  So what the residual needs is not a level fact but a *regularity* fact — that a
Π-codomain is a type — and `Stratified` has none.  That is what the `OnCtx` guard supplies, and
it is why the guarded target is the one this route can serve. -/

/-- `type0_agree` with the two types only `≈`-equal. -/
theorem SortRed.type0_agree' (henv : Ordered env) {Γ : List VExpr} {X Y : VExpr}
    {u u' v v' : VLevel} (hX : env.HasTypeN U 0 Γ X (.sort v))
    (hY : env.HasTypeN U 0 Γ Y (.sort v')) (hvv' : v ≈ v')
    (hrX : SortRed u X) (hrY : SortRed u' Y) : u ≈ u' := by
  obtain ⟨w, hw, rfl⟩ := hrX.type0_pin henv hX
  obtain ⟨w', hw', rfl⟩ := hrY.type0_pin henv hY
  exact hw.symm.trans ((VLevel.succ_congr_iff.1 hvv').trans hw')

/-- **`AppCodType0` is false at every environment**, not only at `∅`: the `AppData` transfers up
(`AppData.mono_env`) and `⊢₀` types stay unique (`HasTypeN.uniq_zero` is unconditional).  So
`appUniqLvl_of_sortRedInv_codType0` is **vacuous at `U = 0`, `n = 1` everywhere** — recorded as
such, and *not* as a route. -/
theorem appCodType0_false_everywhere (env : VEnv) : ¬ AppCodType0 env 0 1 := by
  intro h
  obtain ⟨v, h₀, -⟩ := h (lamK_appData.mono_env emptyEnv_le)
  rw [show lamK.lift.lift.inst (.sort .zero) = lamK from by
    rw [VExpr.inst_lift, lamK_lift]] at h₀
  exact VExpr.noConfusion (HasTypeN.uniq_zero (lamK_type0.mono_env emptyEnv_le) h₀)

/-! ### The repaired side condition, guarded — stated, open, and *not* discharged

`OnCtx Γ (env.IsType U)` excludes the λ-term context entry the refutation uses.  Whether the
guarded condition holds is open; nothing here proves it, and the bridge from the guarded `app`
case to `PropUniqNOn` is **not** built here either.  Both are named so the next round can price
them instead of rediscovering the unguarded version. -/

/-- The guarded side condition, with the `≈` relaxation of `type0_agree'`. -/
def AppCodType0On (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr}, OnCtx Γ (env.IsType U) →
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    ∃ v v' : VLevel, env.HasTypeN U 0 Γ (B₀.inst a) (.sort v) ∧
      env.HasTypeN U 0 Γ (B₁.inst a) (.sort v') ∧ v ≈ v'

/-- The guarded form of `AppUniqLvl`, matching `PropUniqNOn`'s guard. -/
def AppUniqLvlOn (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.IsDefEqN U n Γ (B₁.inst a) (.sort v) →
    (u ≈ (.zero : VLevel) ↔ v ≈ (.zero : VLevel))

/-- **The guarded conditional.**  Both hypotheses are open: `SortRedInv` is §17.1's residual and
`AppCodType0On` is stated here for the first time.  **Nothing is discharged**; this is a
statement of what the route costs, in the form its consumer would use. -/
theorem appUniqLvlOn_of_sortRedInv_codType0On (henv : Ordered env)
    (hinv : SortRedInv env U (n+1)) (hct : AppCodType0On env U (n+1)) :
    AppUniqLvlOn env U (n+1) := by
  intro Γ f a A₀ B₀ A₁ B₁ u v hΓ d c₀ c₁
  obtain ⟨w, w', h₀, h₁, hww'⟩ := hct hΓ d
  have := SortRed.type0_agree' henv h₀ h₁ hww' ((hinv c₀).2 (.sort rfl)) ((hinv c₁).2 (.sort rfl))
  exact ⟨fun h => this.symm.trans h, fun h => this.trans h⟩

/-- …and the guarded form is antitone in the environment too, so it sits in the same chain: the
guarded target at any environment implies the guarded target at `∅`. -/
theorem AppUniqLvlOn.mono_env {env env' : VEnv} (le : env ≤ env')
    (h : AppUniqLvlOn env' U n) : AppUniqLvlOn env U n :=
  fun hΓ d c₀ c₁ => h (hΓ.mono fun ht => ht.mono le) (d.mono_env le)
    (c₀.mono_env le) (c₁.mono_env le)

theorem appUniqLvlOn_le (h : AppUniqLvlOn env U n) : AppUniqLvlOn (∅ : VEnv) U n :=
  AppUniqLvlOn.mono_env emptyEnv_le h

/-! ## 7. Verdict

**Proved** (all `sorryAx`-free):

* the whole `app`-case family is antitone in the environment, and `∅` is `VEnv.WF`;
* so the `VEnv.WF` target — and the target at *any* environment, `preludeEnv` included —
  **implies `AppUniqLvl ∅ 0 1`**;
* and **no hypothesis implied by `VEnv.WF` can avoid that** (`no_wf_hypothesis_avoids_empty`),
  `IsDeclRule.lhs_shape` and total rule-freeness included;
* `IsDeclRule` does **not** discharge `ExtraSortRed`;
* `SortRed`'s level is pinned by the `⊢₀` type (`SortRed.type0_pin`, `type0_agree`,
  `type0_agree'`);
* and the natural side condition that would exploit that is **false at every environment**
  (`appCodType0_false_everywhere`) — for lack of *regularity*, not for a level reason.

**Not proved, and not refuted**: `AppUniqLvl ∅ 0 1` itself; `AppCodType0On`; the bridge from
`AppUniqLvlOn` to `PropUniqNOn`.

**Grade, in this corner's vocabulary.**

1. **This is a lower bound, one-way.**  Refuting `AppUniqLvl ∅ 0 1` refutes the target at every
   environment (`appUniqLvl_empty_false_imp`); *proving* it proves nothing about `preludeEnv`.
   So it is a **necessary condition, possibly strictly weaker** than the target — graded as
   such, not as a reduction, and **not** a collapse: no statement here is claimed equivalent to
   what it was derived from.
2. **Hole-free ≠ discharged**, reported separately as always.  Every declaration here is
   hole-free.  **Nothing about `AppUniqLvl` at any environment is discharged.**  Two of this
   file's own statements are instances of shapes already on record:
   `appUniqLvl_of_sortRedInv_codType0` has a hypothesis that is **false at every environment**
   (shape 2), and `appUniqLvlOn_of_sortRedInv_codType0On` has two hypotheses that are each open
   (shape 5).  Both are labelled in place rather than presented as routes.
3. **What would have been the sixth shape**, caught by testing rather than shipped:
   `appUniqLvl_witness_must_break` reads as a constraint on the witness search and is **void**,
   because `appCodType0_one_false` settles its right disjunct.  It is kept as the record of the
   refutation, marked. -/

section Audit
#print axioms Lean4Lean.VEnv.emptyEnv_le
#print axioms Lean4Lean.VEnv.emptyEnv_no_defeqs
#print axioms Lean4Lean.VEnv.wf_emptyEnv
#print axioms Lean4Lean.VEnv.emptyEnv_isDeclRule
#print axioms Lean4Lean.VEnv.AppData.mono_env
#print axioms Lean4Lean.VEnv.AppUniqLvl.mono_env
#print axioms Lean4Lean.VEnv.PropUniqN.mono_env
#print axioms Lean4Lean.VEnv.PropUniqZeroN.mono_env
#print axioms Lean4Lean.VEnv.PropUniqNOn.mono_env
#print axioms Lean4Lean.VEnv.PropUniqN.AppCase.mono_env
#print axioms Lean4Lean.VEnv.AppUniqLvl.mono_univs
#print axioms Lean4Lean.VEnv.appUniqLvl_le
#print axioms Lean4Lean.VEnv.appUniqLvl_all_le
#print axioms Lean4Lean.VEnv.propUniqN_le
#print axioms Lean4Lean.VEnv.propUniqZeroN_le
#print axioms Lean4Lean.VEnv.propUniqNOn_le
#print axioms Lean4Lean.VEnv.appUniqLvl_wf_lower
#print axioms Lean4Lean.VEnv.appUniqLvl_target_lower
#print axioms Lean4Lean.VEnv.appUniqLvl_empty_false_imp
#print axioms Lean4Lean.VEnv.propUniqZeroN_empty_false_imp
#print axioms Lean4Lean.VEnv.wf_hypothesis_holds_at_empty
#print axioms Lean4Lean.VEnv.no_wf_hypothesis_avoids_empty
#print axioms Lean4Lean.VEnv.lhs_shape_at_wf
#print axioms Lean4Lean.VEnv.lhs_shape_not_enough
#print axioms Lean4Lean.VEnv.rule_freeness_not_enough
#print axioms Lean4Lean.VEnv.lhs_shape_not_enough_zero
#print axioms Lean4Lean.VEnv.sortValuedDef
#print axioms Lean4Lean.VEnv.sortValuedDef_isDeclRule
#print axioms Lean4Lean.VEnv.isDeclRule_not_extraSortRed
#print axioms Lean4Lean.VEnv.not_extraSortRed_of_sortValued
#print axioms Lean4Lean.VEnv.SortRed.type0_pin
#print axioms Lean4Lean.VEnv.SortRed.type0_agree
#print axioms Lean4Lean.VEnv.AppCodType0
#print axioms Lean4Lean.VEnv.appUniqLvl_of_sortRedInv_codType0
#print axioms Lean4Lean.VEnv.appUniqLvl_witness_must_break
#print axioms Lean4Lean.VEnv.lamK
#print axioms Lean4Lean.VEnv.lamK_lift
#print axioms Lean4Lean.VEnv.lamK_type0
#print axioms Lean4Lean.VEnv.lamK_not_sort_type0
#print axioms Lean4Lean.VEnv.lamK_appData
#print axioms Lean4Lean.VEnv.appCodType0_one_false
#print axioms Lean4Lean.VEnv.appUniqLvl_witness_must_break_is_void
#print axioms Lean4Lean.VEnv.SortRed.type0_agree'
#print axioms Lean4Lean.VEnv.appCodType0_false_everywhere
#print axioms Lean4Lean.VEnv.AppCodType0On
#print axioms Lean4Lean.VEnv.AppUniqLvlOn
#print axioms Lean4Lean.VEnv.appUniqLvlOn_of_sortRedInv_codType0On
#print axioms Lean4Lean.VEnv.AppUniqLvlOn.mono_env
#print axioms Lean4Lean.VEnv.appUniqLvlOn_le
end Audit

end VEnv
end Lean4Lean
