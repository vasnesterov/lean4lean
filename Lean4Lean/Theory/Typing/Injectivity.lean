import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong

/-!
# Structural inversion principles we cannot prove yet

Six statements, in two families.

## Sorts and Π-types

`sort_inv`, `forallE_inv_stratified`, `forallE_inv`, `sort_forallE_inv` — the original four.
`forallE_inv` is *derived* from the stratified form here; note that
`Experimental/Reflect/Capstone.lean` now proves it directly, relative to a `Params`
instance, **without** going through the stratified form, so when a `Params` instance lands
the arrow reverses and this derivation is replaced rather than reused.

## Constant applications — three different facts, and they are not interchangeable

`docs/design-inductive.md`'s ledger entry **I13 records only the first of these**, under the
name `const_forallE_inv`, while five consumers across two streams need the second or the
third.  Distinguishing them is the point of this section; see `docs/research-const-inv.md`
§1.

* **(A) Disjointness** — a rule-free constant application is not a Π.  `const_forallE_inv`
  below.  Consumer: `pat_major_not_pi` (ledger I14).
* **(B) Injectivity** — two applications of the *same* constant force their level and
  argument lists to agree.  `const_app_inv` below.  Consumers:
  `Verify/TypeChecker/WHNF.lean`'s `reduceRecursor.WF` quotient branch and its `Quot.ind`
  arm (both need `Quot α r ≡ Quot α' r' → α ≡ α'`), and `TrProj.uniq` / `TrProj.defeqDFC`
  (`Verify/Typing/Lemmas.lean`).
* **(C) Rigidity** — a term definitionally equal to a constant application reduces to one
  with the same head, so its components can be read back in the smaller context.  Consumer:
  `TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean`, see the route traced in its docstring).
  **Deliberately not stated here.**  Its only faithful formulation mentions weak-head
  reduction, which lives in `Theory/Typing/HeadReduction.lean` — downstream of this file and
  gated on `Params`.  Writing a reduction-free approximation is how one gets a fourth wrong
  statement; it should be stated where the reduction relation is in scope.

### Why (B) carries two side conditions

Both are load-bearing, and **both are machine-checked in
`Theory/Typing/ConstInvWitness.lean`** — as regression tests, not prose, so that dropping
either one makes that file prove `False`.

* `RuleFreeHead` — without it, a constant whose value is a constant function identifies all
  its arguments (`w1`).  This is the condition the ledger already records.
* `IsType` on the application — without it, `IsDefEq.proofIrrel` identifies *any* two
  applications that land in a proposition, **with no reduction and with no rule in the
  environment at all** (`w2`).  `RuleFreeHead` does not repair this, which is why the
  ledger's single condition is not enough.

Both consumers' sites satisfy `IsType` for free: they use the fact at the *type* of a term.

A fourth fact — no-confusion between *distinct* rule-free constants — is not stated because
no consumer has asked for it; (B) is same-head only.
-/

namespace Lean4Lean

/-- The head constant of an application spine, under any number of leading lambdas.

Spelled out here rather than reusing `PatternDecode.lean`'s `peelLams`/`spine` so that this
file keeps its two-import list; the λ-peeling matters because a rule with parameters stores
its left-hand side λ-abstracted (`Theory/Quot.lean`'s `quotDefEq`, `VInductDecl'.iotaRule`),
while a δ-rule's is the bare `.const c (VLevel.params _)`. -/
def VExpr.headConst? : VExpr → Option Lean.Name
  | .const c _ => some c
  | .app f _ => f.headConst?
  | .lam _ b => b.headConst?
  | _ => none

namespace VEnv

/-- `c` heads no definitional-equality rule of `env`.

For an environment built by declarations this holds of every inductive type former, every
constructor, and of `Quot` — the rules are δ-rules headed by a `def`'s name, ι-rules headed
by a recursor, and `quotDefEq` headed by `Quot.lift` (`Theory/Typing/PatternRules.lean`'s
`Pat`).  Deriving it from `VEnv.WF` is ledger item M2 and needs the `VEnv.Sig` invariant. -/
def RuleFreeHead (env : VEnv) (c : Lean.Name) : Prop :=
  ∀ df, env.defeqs df → VExpr.headConst? df.lhs ≠ some c

theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := sorry

theorem IsDefEqU.forallE_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry

theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
  let ⟨_, eq⟩ := h1
  let ⟨h2, h3⟩ := (eq.strong henv hΓ).hasType'
  let ⟨_, h2⟩ := h2.stratify
  let ⟨_, h3⟩ := h3.stratify
  let ⟨⟨_, a1, _⟩, _, a2, _⟩ := IsDefEqU.forallE_inv_stratified henv hΓ h1 h2 h3
  ⟨⟨_, a1⟩, _, a2⟩

theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := sorry

/-- **(B) Injectivity of a constant application.**  See the module docstring for why both
side conditions are needed, and `Theory/Typing/ConstInvWitness.lean` for the machine-checked
witness against each. -/
theorem IsDefEqU.const_app_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr}
    (hrigid : RuleFreeHead env c)
    (hty : env.IsType U Γ ((VExpr.const c ls).mkApp as))
    (h : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as')) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' := sorry

/-- **(A) Disjointness** — ledger item I13, and the only one of the three the ledger records.
Consumed by `pat_major_not_pi` (I14).  Needs no `IsType` side condition: `proofIrrel` cannot
identify a term with a Π, because a Π is a type. -/
theorem IsDefEqU.const_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    (hrigid : RuleFreeHead env c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.forallE A B) := sorry
