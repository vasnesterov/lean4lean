import Lean4Lean.Theory.Typing.AppCodLevelWF

/-!
# The convertible-but-not-syntactic case: the conditioned side condition is **FALSE** too

`Theory/Typing/AppCodType0.lean` refutes `AppCodType0On` at every environment, every `U` and
every index `n+1`, and grades its conditioned repair `AppCodType0OnC` a *collapse* on the
sub-family where the two codomain instances are **syntactically** sorts.
`Theory/Typing/AppCodLevelWF.lean` removes the level side conditions from that grading, so the
collapse holds on the whole syntactic-sort sub-family.

`docs/handoff-sortinv-route.md` §29.5 names the one residual: the conditioned premise space is
*larger* than the syntactic-sort sub-family, because `c₀ : IsDefEqN (n+1) Γ (B₀.inst a) (.sort u)`
permits a codomain instance merely **convertible** to a sort.  It asks for an `AppData` under the
guard whose codomain instances are convertible to sorts while one of them is `⊢₀`-typeable at
nothing, and states that "if it exists, the conditioned form is refuted and the `type0_pin`
strategy is dead outright."

**It exists, and it is `AppCodType0.lean`'s own witness read one index higher.**

`Stratified.beta` concludes at `n+1` from typing premises at `n`.  The witness's codomain
instance `lhs = (fun x : Type 0 => x) (Sort (max 0 0))` is stuck at index `1` — that is
`CodType0Refute.stuck`, and it is why §7 of that file could report the witness as *outside* the
conditioned premises.  But it is stuck at index `1` **only**: the β-step's argument premise
`a : A` is available from index `1` up (`CodType0Refute.a_hasType1`), so from index `2` up the
redex fires and `lhs` is `⊢ₙ`-convertible to the sort `Sort (max 0 0)`.  Its `⊢₀`-typeability is
unchanged — `CodType0Refute.lhs_not_hasType0` is index-`0` inversion, unconditional in the
environment.  So at index `2` and above the witness satisfies the *conditioned* premises and
still refutes the conclusion.

## What is refuted, exactly

At **every** environment, **every** `U`, **every** `n`:

* `¬ AppCodType0OnC env U (n+2)` (`appCodType0OnC_false`);
* `¬ AppCodShareOn env U (n+2)` (`appCodShareOn_false`) — the weakest form of §9 of
  `AppCodType0.lean`;
* `¬ AppCodHasType0On env U (n+2)` (`appCodHasType0On_false`) — the weakest statement of this
  *shape* at all: "the first codomain instance has **some** `⊢₀` type", with no sort, no level
  relation, and no second instance.  Both of the above imply it (`AppCodType0OnC.hasType0`,
  `AppCodShareOn.hasType0`), so the refutation is of the shape, not of a phrasing.

Each of these is **antitone in the index** (`AppCodType0OnC.mono_index` and friends), so "false
at `n+2`" is "false at every index `≥ 2`", and index `1` is the *only* surviving index — where
`CodType0Refute.witness_outside_conditioned` shows this witness genuinely does not reach, and
where §4 shows an environment-uniform proof is nevertheless impossible.

At index `0` the shape is **provable** (`appCodType0OnC_zero`), which is the control: the
refutation is not "the statement was silly", it is a fact about the index.

## Consequence for the route

`appUniqLvlOn_of_sortRedInv_codType0OnC` is stated at index `n+1` for arbitrary `n`, and the
`unique.tex` induction that consumes `AppUniqLvlOn` runs through every index.  So the route is
vacuous at every index except `1`, exactly as its unguarded and unconditioned predecessors were
vacuous everywhere.  **The `type0_pin` strategy is dead**: not a collapse this time — false.
-/
namespace Lean4Lean
namespace VEnv

open VExpr

namespace CodType0Refute

variable {env : VEnv} {U : Nat}

/-! ## 1. The witness fires from index 2 up

Nothing new is built here: `a_hasTypeN` is `AppCodType0.lean`'s, and `Stratified.beta` at index
`n+2` takes its premises at `n+1`, which is exactly where `a : A` becomes available. -/

/-- The β-step, at index `n+2`.  The argument premise is `a_hasTypeN` at index `n+1`; at index
`1` (premises at `0`) it is unavailable, which is `a_not_hasType0`. -/
theorem lhs_defeq_a {Γ : List VExpr} {n : Nat} : env.IsDefEqN U (n+2) Γ lhs a :=
  .beta (Stratified.bvar Lookup.zero) a_hasTypeN

/-- **The stuck redex is convertible to a sort from index 2 up.**  Contrast
`lhs_not_defeq_sort`, which is the same statement at index `1` and is *true*. -/
theorem lhs_defeq_sort {Γ : List VExpr} {n : Nat} :
    env.IsDefEqN U (n+2) Γ lhs (.sort q) := lhs_defeq_a

/-- The first conditioning premise, in the consumer's own form. -/
theorem cond₀ {n : Nat} : env.IsDefEqN U (n+2) [P] (D.inst a) (.sort q) :=
  D_inst ▸ lhs_defeq_sort

/-- The second conditioning premise: the second codomain instance is a sort on the nose. -/
theorem cond₁ {m : Nat} : env.IsDefEqN U m [P] ((VExpr.bvar 0).inst a) (.sort q) := .rfl

end CodType0Refute

/-! ## 2. The weakest statement of the shape, and the two implications into it

`AppCodType0OnC` asks for two `⊢₀` typings at sorts with `≈`-equal levels; `AppCodShareOn` asks
for two at a shared type.  Both entail this, which asks for *one*, at *anything*. -/

/-- **The shape, at its weakest**: under the guard, a codomain instance that is `⊢ₙ`-convertible
to a sort has *some* `⊢₀` type. -/
def AppCodHasType0On (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
    AppData env U n Γ f a A₀ B₀ A₁ B₁ →
    env.IsDefEqN U n Γ (B₀.inst a) (.sort u) →
    env.IsDefEqN U n Γ (B₁.inst a) (.sort v) →
    ∃ T : VExpr, env.HasTypeN U 0 Γ (B₀.inst a) T

variable {env : VEnv} {U n : Nat}

theorem AppCodType0OnC.hasType0 (h : AppCodType0OnC env U n) : AppCodHasType0On env U n :=
  fun hΓ d c₀ c₁ => let ⟨_, _, h₀, _, _⟩ := h hΓ d c₀ c₁; ⟨_, h₀⟩

theorem AppCodShareOn.hasType0 (h : AppCodShareOn env U n) : AppCodHasType0On env U n :=
  fun hΓ d c₀ c₁ => let ⟨T, h₀, _⟩ := h hΓ d c₀ c₁; ⟨T, h₀⟩

/-! ## 3. The refutation -/

/-- **The weakest form of the shape is false at every environment, every `U`, and every index
`≥ 2`.**  The witness is `AppCodType0.lean`'s, unchanged; only the index moves. -/
theorem appCodHasType0On_false (env : VEnv) (U n : Nat) : ¬ AppCodHasType0On env U (n+2) := by
  intro h
  obtain ⟨T, hT⟩ :=
    h CodType0Refute.onCtx (CodType0Refute.witness (n := n+1))
      CodType0Refute.cond₀ CodType0Refute.cond₁
  exact CodType0Refute.lhs_not_hasType0 (CodType0Refute.D_inst ▸ hT)

/-- **`AppCodType0OnC` is false** at every environment, every `U`, and every index `≥ 2`. -/
theorem appCodType0OnC_false (env : VEnv) (U n : Nat) : ¬ AppCodType0OnC env U (n+2) :=
  fun h => appCodHasType0On_false env U n h.hasType0

/-- **`AppCodShareOn` is false** likewise — so §9 of `AppCodType0.lean`'s "weakest side condition
that feeds the pin" is not merely a collapse, it is false. -/
theorem appCodShareOn_false (env : VEnv) (U n : Nat) : ¬ AppCodShareOn env U (n+2) :=
  fun h => appCodHasType0On_false env U n h.hasType0

/-- Stated the way the consumer sees it: the conditioned conditional is vacuous from index `2`
up, so it discharges `AppUniqLvlOn` at no index but `1`. -/
theorem appUniqLvlOn_of_sortRedInv_codType0OnC_vacuous (env : VEnv) (U n : Nat) :
    ¬ AppCodType0OnC env U (n+2) := appCodType0OnC_false env U n

/-! ## 4. Antitone in the index, so index `1` is the only survivor

Both judgments are monotone in the index (`Stratified.mono`), and every one of these statements
has the index **only** in its premises — the conclusion is pinned at `0`.  So a *larger* index is
a *stronger* statement, and the refutation at `n+2` propagates upward, not downward. -/

theorem AppData.mono_index {m : Nat} (le : m ≤ n) {Γ : List VExpr} {f a A₀ B₀ A₁ B₁ : VExpr}
    (d : AppData env U m Γ f a A₀ B₀ A₁ B₁) : AppData env U n Γ f a A₀ B₀ A₁ B₁ :=
  ⟨d.fn₀.mono le, d.arg₀.mono le, d.fn₁.mono le, d.arg₁.mono le⟩

theorem AppCodHasType0On.mono_index {m : Nat} (le : m ≤ n) (h : AppCodHasType0On env U n) :
    AppCodHasType0On env U m :=
  fun hΓ d c₀ c₁ => h hΓ (d.mono_index le) (c₀.mono le) (c₁.mono le)

theorem AppCodType0OnC.mono_index {m : Nat} (le : m ≤ n) (h : AppCodType0OnC env U n) :
    AppCodType0OnC env U m :=
  fun hΓ d c₀ c₁ => h hΓ (d.mono_index le) (c₀.mono le) (c₁.mono le)

theorem AppCodShareOn.mono_index {m : Nat} (le : m ≤ n) (h : AppCodShareOn env U n) :
    AppCodShareOn env U m :=
  fun hΓ d c₀ c₁ => h hΓ (d.mono_index le) (c₀.mono le) (c₁.mono le)

/-- **False at every index `≥ 2`**, stated with the bound rather than the successor pattern. -/
theorem appCodType0OnC_false_of_two_le {m : Nat} (h2 : 2 ≤ m) (env : VEnv) (U : Nat) :
    ¬ AppCodType0OnC env U m := fun h =>
  appCodType0OnC_false env U 0 (h.mono_index h2)

theorem appCodShareOn_false_of_two_le {m : Nat} (h2 : 2 ≤ m) (env : VEnv) (U : Nat) :
    ¬ AppCodShareOn env U m := fun h =>
  appCodShareOn_false env U 0 (h.mono_index h2)

theorem appCodHasType0On_false_of_two_le {m : Nat} (h2 : 2 ≤ m) (env : VEnv) (U : Nat) :
    ¬ AppCodHasType0On env U m := fun h =>
  appCodHasType0On_false env U 0 (h.mono_index h2)

/-! ## 5. The control: at index `0` the shape is **provable**

The refutation is a fact about the index, not a sign that the statement was malformed.  At index
`0` the two Π-types of an `AppData` are *syntactically* equal (`HasTypeN.uniq_zero`), so the two
codomain instances coincide; conversion is syntactic, so each is literally a sort; and its level
is `WF` by `AppData.sort_levelWF` (`AppCodLevelWF.lean`), which is what `Stratified.sort` needs.
So the strongest form of the shape holds at index `0`, with nothing assumed but the guard. -/

theorem appCodType0OnC_zero (env : VEnv) (U : Nat) : AppCodType0OnC env U 0 := by
  intro Γ f a A₀ B₀ A₁ B₁ u v hΓ d c₀ c₁
  have e₀ : B₀.inst a = .sort u := IsDefEqN.zero_iff.1 c₀
  have e₁ : B₁.inst a = .sort v := IsDefEqN.zero_iff.1 c₁
  obtain ⟨hu, hv⟩ := d.sort_levelWF hΓ e₀ e₁
  exact ⟨.succ u, .succ v, e₀ ▸ .sort hu, e₁ ▸ .sort hv,
    have : VExpr.forallE A₀ B₀ = .forallE A₁ B₁ := HasTypeN.uniq_zero d.fn₀ d.fn₁
    by injection this with _ hB; subst hB; rw [e₀] at e₁; injection e₁ with hu; exact hu ▸ rfl⟩

theorem appCodShareOn_zero (env : VEnv) (U : Nat) : AppCodShareOn env U 0 := by
  intro Γ f a A₀ B₀ A₁ B₁ u v hΓ d c₀ c₁
  have e₀ : B₀.inst a = .sort u := IsDefEqN.zero_iff.1 c₀
  have e₁ : B₁.inst a = .sort v := IsDefEqN.zero_iff.1 c₁
  obtain ⟨hu, hv⟩ := d.sort_levelWF hΓ e₀ e₁
  have hB : VExpr.forallE A₀ B₀ = .forallE A₁ B₁ := HasTypeN.uniq_zero d.fn₀ d.fn₁
  injection hB with _ hB
  subst hB
  exact ⟨.sort (.succ u), e₀ ▸ .sort hu, e₀ ▸ .sort hu⟩

theorem appCodHasType0On_zero (env : VEnv) (U : Nat) : AppCodHasType0On env U 0 :=
  AppCodType0OnC.hasType0 (appCodType0OnC_zero env U)

/-! ## 6. Index `1`: false at an `Ordered` environment

Index `1` survives §3 for a real reason — `CodType0Refute.lhs_not_defeq_sort` says the redex is
stuck there, over `∅`.  It does **not** survive `Ordered`.  Add the β-equation as a *rule*: the
δ-step is at `n+1` for every `n`, index `1` included, and it makes the same stuck term convertible
to the same sort while leaving its `⊢₀`-typeability untouched.

The rule is `VDefEq.WF`, because the equation it states is derivable in the **unstratified**
judgment — where `Sort (max 0 0) : Type 0` needs no index — so the environment is `Ordered`.
It is not claimed `VEnv.WF`: a bare rewrite rule need not come from a declaration, and
`VDefEq.IsDeclRule` would reject this one (its `lhs` is an application, not a `const`).  What this
settles is therefore exactly the consumer's hypothesis: `appUniqLvlOn_of_sortRedInv_codType0OnC`
assumes `Ordered env` and nothing more about the rules, and at index `1` that is not enough. -/

namespace CodType0Refute

/-- The β-equation as a rewrite rule, at `0` universe parameters. -/
def betaRule : VDefEq := ⟨0, lhs, a, A⟩

theorem a_hasType {Γ : List VExpr} : env.HasType U Γ a A := by
  have h1 : env.IsDefEq U Γ (.sort (.succ q)) A (.sort (.succ (.succ q))) :=
    .sortDF q_wf trivial succ_q_equiv
  have h2 : env.HasType U Γ a (.sort (.succ q)) := .sortDF q_wf q_wf rfl
  exact .defeqDF h1 h2

theorem lam_hasType_nil : env.HasType U [] (.lam A (.bvar 0)) (.forallE A A) :=
  .lamDF A_hasType (.bvar Lookup.zero)

theorem lhs_hasType : env.HasType U [] lhs A :=
  .appDF lam_hasType_nil a_hasType

theorem betaRule_wf : betaRule.WF (∅ : VEnv) := ⟨lhs_hasType, a_hasType⟩

/-- The environment: `∅` plus the one rule. -/
def betaEnv : VEnv := (∅ : VEnv).addDefEq betaRule

theorem betaEnv_ordered : Ordered betaEnv := .defeq .empty betaRule_wf

theorem betaEnv_defeqs : betaEnv.defeqs betaRule := .inl rfl

/-- The δ-step: at **every** index `n+1`, index `1` included. -/
theorem betaEnv_lhs_defeq_sort {Γ : List VExpr} {n : Nat} :
    betaEnv.IsDefEqN U (n+1) Γ lhs (.sort q) :=
  Stratified.extra (ls := []) betaEnv_defeqs (by simp) rfl

theorem betaEnv_cond₀ {n : Nat} : betaEnv.IsDefEqN U (n+1) [P] (D.inst a) (.sort q) :=
  D_inst ▸ betaEnv_lhs_defeq_sort

end CodType0Refute

/-- **At index `1` the shape is false at an `Ordered` environment.**  So no proof of the
conditioned side condition can run on `Ordered env` alone at any index: §3 kills every index
`≥ 2` at every environment whatever, and this kills the one index §3 leaves. -/
theorem appCodHasType0On_one_false_ordered (U : Nat) :
    ¬ AppCodHasType0On CodType0Refute.betaEnv U 1 := by
  intro h
  obtain ⟨T, hT⟩ :=
    h CodType0Refute.onCtx (CodType0Refute.witness (n := 0))
      CodType0Refute.betaEnv_cond₀ CodType0Refute.cond₁
  exact CodType0Refute.lhs_not_hasType0 (CodType0Refute.D_inst ▸ hT)

theorem appCodType0OnC_one_false_ordered (U : Nat) :
    ¬ AppCodType0OnC CodType0Refute.betaEnv U 1 :=
  fun h => appCodHasType0On_one_false_ordered U h.hasType0

theorem appCodShareOn_one_false_ordered (U : Nat) :
    ¬ AppCodShareOn CodType0Refute.betaEnv U 1 :=
  fun h => appCodHasType0On_one_false_ordered U h.hasType0

/-- **The route is dead at every index.**  For every index `n+1` there is an `Ordered`
environment at which the conditioned side condition fails — for `n ≥ 1` *every* environment
does, and for `n = 0` `betaEnv` does.  `appUniqLvlOn_of_sortRedInv_codType0OnC` assumes
`Ordered env`, so it is vacuous at some `Ordered` environment at every index. -/
theorem codType0OnC_false_somewhere_ordered (U n : Nat) :
    ∃ env : VEnv, Ordered env ∧ ¬ AppCodType0OnC env U (n+1) := by
  cases n with
  | zero => exact ⟨_, CodType0Refute.betaEnv_ordered, appCodType0OnC_one_false_ordered U⟩
  | succ k => exact ⟨_, CodType0Refute.betaEnv_ordered, appCodType0OnC_false _ U k⟩

/-! ## 7. The rule is not excluded by any recorded `VEnv.WF` consequence

`Theory/Typing/DeclRules.lean` records exactly one shape constraint that `VEnv.WF` puts on a
rule: `VDefEq.IsDeclRule.lhs_shape`, "a rule's left-hand side is headed by `.const`, `.app` or
`.lam`", with `lhs_ne_sort` and `lhs_ne_forallE` as its corollaries.  `betaRule.lhs` is an
`.app`, so **it passes all three**.

This is *not* a claim that `betaEnv` is `VEnv.WF` or that `betaRule.IsDeclRule` — neither is
claimed anywhere here, and `betaRule` is plainly not a δ-rule (a δ-rule's `lhs` is a `.const`),
not `quotDefEq`, and not visibly an ι-rule.  What it says is narrower and is the part that can be
checked: the one instrument this repo has for rejecting a hand-built rule does not reject this
one, so "the index-1 witness is obviously excluded by well-formedness" is not available as an
objection without new work. -/

theorem betaRule_lhs_shape :
    (∃ c ls, CodType0Refute.betaRule.lhs = .const c ls) ∨
      (∃ f a, CodType0Refute.betaRule.lhs = .app f a) ∨
      ∃ A b, CodType0Refute.betaRule.lhs = .lam A b := .inr (.inl ⟨_, _, rfl⟩)

theorem betaRule_lhs_ne_sort (u : VLevel) : CodType0Refute.betaRule.lhs ≠ .sort u := nofun

theorem betaRule_lhs_ne_forallE (A B : VExpr) :
    CodType0Refute.betaRule.lhs ≠ .forallE A B := nofun

/-! ## 8. Verdict

**Refuted** (machine-checked, `sorryAx`-free, every declaration hole-free):

* `AppCodType0OnC env U m` for **every** `env`, **every** `U`, **every** `m ≥ 2`
  (`appCodType0OnC_false`, `appCodType0OnC_false_of_two_le`).  So the answer to
  `docs/handoff-sortinv-route.md` §29.5's residual is the third of its three options: the
  convertible-but-not-syntactic case is where the conditioned side condition **dies**, not where
  it is merely weaker.
* `AppCodShareOn env U m` likewise (`appCodShareOn_false`) — `AppCodType0.lean` §9's "weakest side
  condition that feeds the pin" is not a collapse, it is false.
* `AppCodHasType0On env U m` likewise (`appCodHasType0On_false`) — the weakest statement of the
  *shape*: one `⊢₀` typing, at anything, of one codomain instance.  The other two imply it
  (`AppCodType0OnC.hasType0`, `AppCodShareOn.hasType0`), so what is refuted is the shape.
* `AppCodType0OnC CodType0Refute.betaEnv U 1` — the one index §3 leaves, at an **`Ordered`**
  environment (`appCodType0OnC_one_false_ordered`, `CodType0Refute.betaEnv_ordered`).  So no proof
  of the side condition runs on `Ordered env` alone at *any* index
  (`codType0OnC_false_somewhere_ordered`), which is exactly what
  `appUniqLvlOn_of_sortRedInv_codType0OnC` assumes.

**Proved positively**, and it is the control that makes the above a fact about the index rather
than a malformed statement: `AppCodType0OnC env U 0` and `AppCodShareOn env U 0` hold at every
environment and every `U` (`appCodType0OnC_zero`, `appCodShareOn_zero`), from `HasTypeN.uniq_zero`
(the two Π-types coincide at index `0`, hence so do the two codomain instances),
`IsDefEqN.zero_iff` and `AppData.sort_levelWF`.  Together with antitonicity in the index
(`AppCodType0OnC.mono_index`) the picture is complete: **true at `0`, open only at `1` over `∅`,
false at every index `≥ 2` at every environment, and false at `1` over an `Ordered` environment.**

**Not settled** — the honest sliver: `AppCodType0OnC (∅ : VEnv) U 1`.  Over `∅` the index-1 redex
is genuinely stuck (`CodType0Refute.lhs_not_defeq_sort`), and the shape may well be *provable*
there; the case that blocks a quick proof is `Stratified.eta`, whose premise `Γ ⊢₀ e : .forallE A B`
does not hand back `Γ ⊢₀ A : .sort u` — that is `⊢₀` regularity, which this corner does not have.
It is a curiosity, not a route: `appUniqLvlOn_of_sortRedInv_codType0OnC` is quantified at `n+1` for
arbitrary `n`, so index `1` alone discharges nothing.

**Grade.**  Not a reduction and not a collapse — a **refutation**, so the collapse-detection rule
does not apply: no statement here is claimed equivalent to anything, and the one new definition
(`AppCodHasType0On`) exists only to be weaker than what it refutes, which is proved
(`AppCodType0OnC.hasType0`, `AppCodShareOn.hasType0`) rather than asserted.

**Hole-free ≠ discharged**, separately as always.  **Discharged: nothing.**  `AppUniqLvlOn`,
`AppUniqLvl ∅ 0 1` and `PropUniqNOn` are exactly where `AppCodLevelWF.lean` left them.  What is
settled is one side condition's truth value — negatively, at every index the route needs — and
one route's grade, which changes from *collapse* to *false*.

**Where the previous round's test was index-local.**  `AppCodType0.lean` §7 tested its conditioned
repair against its own witness and reported the witness *outside* the conditioned premises.  That
test is correct and is still correct: `CodType0Refute.witness_outside_conditioned` is stated at
index `1`, and at index `1` it is true.  The gap is that the side condition is consumed at index
`n+1` for arbitrary `n`, and one index higher the same witness walks straight in — because
`Stratified.beta` takes its premises one index down, and `a : A` becomes available at exactly
index `1`.  The lesson is not "test your side conditions" (that was done) but **"test them at
every index they are quantified over"**. -/

section Audit

/-! `#print axioms`, by namespace.  `CodType0Refute` first. -/
#print axioms Lean4Lean.VEnv.CodType0Refute.lhs_defeq_a
#print axioms Lean4Lean.VEnv.CodType0Refute.lhs_defeq_sort
#print axioms Lean4Lean.VEnv.CodType0Refute.cond₀
#print axioms Lean4Lean.VEnv.CodType0Refute.cond₁
#print axioms Lean4Lean.VEnv.CodType0Refute.betaRule
#print axioms Lean4Lean.VEnv.CodType0Refute.a_hasType
#print axioms Lean4Lean.VEnv.CodType0Refute.lam_hasType_nil
#print axioms Lean4Lean.VEnv.CodType0Refute.lhs_hasType
#print axioms Lean4Lean.VEnv.CodType0Refute.betaRule_wf
#print axioms Lean4Lean.VEnv.CodType0Refute.betaEnv
#print axioms Lean4Lean.VEnv.CodType0Refute.betaEnv_ordered
#print axioms Lean4Lean.VEnv.CodType0Refute.betaEnv_defeqs
#print axioms Lean4Lean.VEnv.CodType0Refute.betaEnv_lhs_defeq_sort
#print axioms Lean4Lean.VEnv.CodType0Refute.betaEnv_cond₀

/-! `Lean4Lean.VEnv`: the shape, the refutations, and the index-`0` control. -/
#print axioms Lean4Lean.VEnv.AppCodHasType0On
#print axioms Lean4Lean.VEnv.AppCodType0OnC.hasType0
#print axioms Lean4Lean.VEnv.AppCodShareOn.hasType0
#print axioms Lean4Lean.VEnv.appCodHasType0On_false
#print axioms Lean4Lean.VEnv.appCodType0OnC_false
#print axioms Lean4Lean.VEnv.appCodShareOn_false
#print axioms Lean4Lean.VEnv.appUniqLvlOn_of_sortRedInv_codType0OnC_vacuous
#print axioms Lean4Lean.VEnv.AppData.mono_index
#print axioms Lean4Lean.VEnv.AppCodHasType0On.mono_index
#print axioms Lean4Lean.VEnv.AppCodType0OnC.mono_index
#print axioms Lean4Lean.VEnv.AppCodShareOn.mono_index
#print axioms Lean4Lean.VEnv.appCodType0OnC_false_of_two_le
#print axioms Lean4Lean.VEnv.appCodShareOn_false_of_two_le
#print axioms Lean4Lean.VEnv.appCodHasType0On_false_of_two_le
#print axioms Lean4Lean.VEnv.appCodType0OnC_zero
#print axioms Lean4Lean.VEnv.appCodShareOn_zero
#print axioms Lean4Lean.VEnv.appCodHasType0On_zero
#print axioms Lean4Lean.VEnv.appCodHasType0On_one_false_ordered
#print axioms Lean4Lean.VEnv.appCodType0OnC_one_false_ordered
#print axioms Lean4Lean.VEnv.appCodShareOn_one_false_ordered
#print axioms Lean4Lean.VEnv.codType0OnC_false_somewhere_ordered
#print axioms Lean4Lean.VEnv.betaRule_lhs_shape
#print axioms Lean4Lean.VEnv.betaRule_lhs_ne_sort
#print axioms Lean4Lean.VEnv.betaRule_lhs_ne_forallE

end Audit

end VEnv
end Lean4Lean
