import Lean4Lean.Theory.Typing.PropConv
import Lean4Lean.Theory.Typing.CycleConv

/-!
# `RegPi` is false; the repair, and the `extra` case

`Theory/Typing/PropConv.lean` flags one item of its own as **not shown satisfiable**:
`RegPi`, regularity at a Π-type, the extra ingredient `propTypeAgree_appCase_of` needs beyond
`app_shadow_of`'s price.  Everything else in that file is replayed at the base index, so
`RegPi` was the single unchecked hypothesis in it.

## 1. `RegPi` is unsatisfiable

`regPi_false : ¬ env.RegPi U n`, for **every** environment, every `U` and every `n` — the
base index and the empty environment included.  The witness is one line of context:

    Γ = [.forallE (.bvar 0) (.bvar 0)]

`Lookup.zero` gives `Γ ⊢ₙ .bvar 0 : .forallE (.bvar 1) (.bvar 0)` for free, and `RegPi` would
then have to type `.bvar 1` in a context of length one, which `HasTypeN.bvar_inv` plus
`Lookup.lt` refute.

`PropConv.lean`'s docstring already says this in prose ("`Lookup` can hand back a Π-type whose
components were never typed").  What was not said is the consequence: `RegPi` is not merely
*unproved*, it is **false**, so `propTypeAgree_appCase_of` — its only consumer in the tree,
by the transitive `getUsedConstantsAsSet` cone — proves nothing.  Its conclusion,
`PropTypeAgree.AppCase`, is *not* thereby refuted; the theorem is simply void.

## 2. The repair, and it is satisfiable

`RegPiOn` is `RegPi` with `OnCtxN` — every context entry is a type at the index — added, and
it is a *consequence of a statement worth having on its own*:

    Regular env U n :  OnCtxN Γ → Γ ⊢ₙ e : A → ∃ u, u.WF U ∧ Γ ⊢ₙ A : .sort u

`regular_of` proves `Regular` from `Ordered env`, `InstLvl`, `RegConvE` (regularity along a
conversion, existential form) and one environment residual, `EnvReg` — "a constant's
instantiated type is a type **at the index**".  Every one of those holds at `n = 0`, so
`Regular`, `RegPiOn` and the whole `app`-case reduction are replayed there.

**The witness is not the empty environment.**  `CycleConv.lean`'s `propLoopEnv` — two
constants `A B : Prop` and the two δ-rules `A ≡ B`, `B ≡ A` — satisfies `EnvReg` at every
index, so `propLoopEnv_regular` and `propLoopEnv_regPiOn` hold with the `const` case of the
induction inhabited and the `defeqs` field non-empty.  `propLoopEnv_regPiOn_fires` applies
`RegPiOn` at an actual Π-typed variable in an actual well-formed context.

`OnCtxN.of_onCtx` closes the loop back to the tree's own hypothesis: every context that is
`OnCtx Γ (env.IsType U)` — what `Injectivity.lean`'s targets already assume — is `OnCtxN` at
*some* index.  So the relativisation is not a narrowing the consumers cannot meet.

## 3. The consumer, re-priced

`propTypeAgree_appCase_on_of` is `propTypeAgree_appCase_of` with `RegPi` replaced by
`RegPiOn`; the proof is the original one with a context hypothesis threaded.  It is not
enough on its own: the *statement* `PropTypeAgree` has to be relativised too, since its `lam`
case grows the context.  `propTypeAgree_on_of` runs that induction — the six closing cases
survive verbatim, and the one new datum is that the binder's universe is well formed, which
is `Regular.lvlWF`.  `propTypeAgreeOn_of_residuals` assembles the chain, and
`propTypeAgreeOn_zero_from_residuals` replays it at the base index over `propLoopEnv`.

So the corrected price of `PropTypeAgree`'s `app` case is

    Regular + InstLvl + PropUniq + PropConvInv     (all relativised to `OnCtxN`)

with `Regular` in place of the false `RegPi`, and `Regular` itself resting on `EnvReg`.

## 4. `PropConvInv`'s `extra` case

It is **open**: `propConvInv_of` discharges it by the hypothesis `PropExtraConv` and by
nothing else, and `PropExtraConv.zero` is true only because `≡₀` is syntactic equality, so
the base index tells nothing about this residual in particular.  `PropConv.lean`'s own
section is right that the shape argument (`WF.instL_lhs_ne_sort` and friends) cannot close
it.

`propExtraConv_of` reduces it one step further, to exactly two statements:

* `DefEqTypeN` — the environment's rules are typed **at the index**.  This is the generic
  obstruction `docs/handoff-stratified.md` §16.5 names, and both halves of its true shape are
  machine-checked here: `defEqTypeN_single` (and `envReg_single`) supply the index for **one**
  rule (one constant), and nothing supplies one index for all of them, because `VEnv.defeqs`
  and `VEnv.constants` are not finite by construction and `Stratified.mono` only raises.
* `SameTypeProp` — two terms of one type agree on being propositions.  It mentions no rule
  and no environment, and follows from `PropTypeUniq`, unique typing at a proposition.

At `propLoopEnv` the first half is discharged at *every* index
(`propLoopEnv_defEqTypeN`), because both sides of both rules are `.const`s and the `const`
rule mentions no conversion.  So at that environment `extra` is exactly `SameTypeProp`.

## 5. `SortNotProp` — the dependency is a cycle, and `extra` is not why

`SortNotProp.of_propConvInv` derives `SortNotProp` from the *statement* `PropConvInv`, not
from `propConvInv_of`, so the open `extra` case does not make it unsound.  But
`propConvInv_from_sortNotProp_cycle` writes out the composite and shows the shape:
`PropConvInv → SortNotProp → PropNotProof → PropConvInv`, at one fixed index with no descent.
`SortNotProp` has exactly two producers in the tree — `of_propConvInv` and `.zero` — so
`propNotProof_of''` cannot be used to discharge `propConvInv_of'`'s `PropNotProof` residual
while proving `PropConvInv`.  The same is true of the other route (`propNotProof_of` consumes
`PropTypeAgree`, which consumes `PropConvInv`).

Everything below is sorry-free; axioms are `propext`, `Quot.sound` and `Classical.choice`,
all on `Guard.lean`'s whitelist.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U n : Nat}

/-! ## 1. `RegPi` is unsatisfiable -/

/-- The one-entry context whose only binding is a Π-type with untypeable components. -/
def regPiCtx : List VExpr := [.forallE (.bvar 0) (.bvar 0)]

theorem regPiCtx_lookup : Lookup regPiCtx 0 (.forallE (.bvar 1) (.bvar 0)) :=
  Lookup.zero' rfl

theorem regPi_false : ¬ env.RegPi U n := by
  intro h
  obtain ⟨_, _, _, _, hA, _⟩ := h (Γ := regPiCtx) (f := .bvar 0) (.bvar regPiCtx_lookup)
  obtain ⟨_, hl, _⟩ := HasTypeN.bvar_inv hA
  exact absurd hl.lt (by simp [regPiCtx])

/-! ## 2. The relativised statement -/

/-- A type at the index, with its universe well formed. -/
def IsTypeN (env : VEnv) (U n : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, u.WF U ∧ env.HasTypeN U n Γ A (.sort u)

/-- Every entry of the context is a type at the index. -/
def OnCtxN (env : VEnv) (U n : Nat) (Γ : List VExpr) : Prop :=
  OnCtx Γ (env.IsTypeN U n)

theorem IsTypeN.weak (henv : Ordered env) {Γ : List VExpr} {A B : VExpr}
    (h : env.IsTypeN U n Γ A) : env.IsTypeN U n (B::Γ) A.lift :=
  let ⟨u, hu, h⟩ := h; ⟨u, hu, h.weak henv⟩

theorem OnCtxN.lookup (henv : Ordered env) {Γ : List VExpr} {A : VExpr} {i : Nat}
    (h : env.OnCtxN U n Γ) (hL : Lookup Γ i A) : env.IsTypeN U n Γ A :=
  OnCtx.lookup h hL (IsTypeN.weak henv)

/-- **`RegPi`, relativised to a well-formed context** — the repair. -/
def RegPiOn (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f A B : VExpr}, env.OnCtxN U n Γ →
    env.HasTypeN U n Γ f (.forallE A B) →
    ∃ u v, u.WF U ∧ v.WF U ∧
      env.HasTypeN U n Γ A (.sort u) ∧ env.HasTypeN U n (A::Γ) B (.sort v)

/-- Regularity at the index, in a well-formed context. -/
def Regular (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A : VExpr}, env.OnCtxN U n Γ → env.HasTypeN U n Γ e A →
    env.IsTypeN U n Γ A

/-- The environment-side residual: a constant's instantiated type is a type **at the index**. -/
def EnvReg (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {c : Name} {ci : VConstant} {ls : List VLevel},
    env.constants c = some ci → (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
    env.IsTypeN U n Γ (ci.type.instL ls)

/-- Regularity along a conversion, in the existential form the induction produces. -/
def RegConvE (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A A' : VExpr},
    env.IsDefEqN U n Γ A A' → env.IsTypeN U n Γ A → env.IsTypeN U n Γ A'

theorem regular_of' {Γ e A b} (H : Stratified env U n Γ e A b) :
    Ordered env → env.EnvReg U n → env.InstLvl U n → env.RegConvE U n → b = true →
    env.OnCtxN U n Γ → env.IsTypeN U n Γ A := by
  induction H with
  | bvar h => intro henv _ _ _ _ hΓ; exact hΓ.lookup henv h
  | sort h => intro _ _ _ _ _ _; refine ⟨_, ?_, .sort h⟩; exact h
  | const h1 h2 h3 => intro _ hce _ _ _ _; exact hce h1 h2 h3
  | app _ ha ihf _ =>
    intro henv hce hinst hrc _ hΓ
    obtain ⟨_, _, hpi⟩ := ihf henv hce hinst hrc (Eq.refl true) hΓ
    obtain ⟨_, v, _, hv, _, hB, _⟩ := HasTypeN.forallE_inv hpi
    exact ⟨v, hv, hinst ha hB⟩
  | lam hA _ ihA ihb =>
    intro henv hce hinst hrc _ hΓ
    obtain ⟨_, _, hsu⟩ := ihA henv hce hinst hrc (Eq.refl true) hΓ
    have hu := (HasTypeN.sort_inv hsu).1
    obtain ⟨v, hv, hB⟩ := ihb henv hce hinst hrc (Eq.refl true) ⟨hΓ, _, hu, hA⟩
    exact ⟨.imax _ v, ⟨hu, hv⟩, .forallE hu hv hA hB⟩
  | forallE hu hv _ _ _ _ =>
    intro _ _ _ _ _ _; refine ⟨_, ?_, .sort ⟨hu, hv⟩⟩; exact ⟨hu, hv⟩
  | conv h _ _ ih2 =>
    intro henv hce hinst hrc _ hΓ
    exact hrc h (ih2 henv hce hinst hrc (Eq.refl true) hΓ)
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro _ _ _ _ hb; exact nomatch hb

/-- **Regularity at the index**, from the environment residual, substitution at a level and
regularity along a conversion. -/
theorem regular_of (henv : Ordered env) (hce : env.EnvReg U n) (hinst : env.InstLvl U n)
    (hrc : env.RegConvE U n) : env.Regular U n :=
  fun hΓ H => regular_of' H henv hce hinst hrc (Eq.refl true) hΓ

/-- **The repair is a consequence of regularity**, and this is the only step where the Π shape
is used. -/
theorem Regular.regPiOn (h : env.Regular U n) : env.RegPiOn U n := by
  intro Γ f A B hΓ hf
  obtain ⟨_, _, hpi⟩ := h hΓ hf
  obtain ⟨u, v, hu, hv, hA, hB, _⟩ := HasTypeN.forallE_inv hpi
  exact ⟨u, v, hu, hv, hA, hB⟩

/-- Levels carried by a type are well formed — a by-product of regularity, and the datum
`Stratified` does not ship. -/
theorem Regular.lvlWF (h : env.Regular U n) {Γ : List VExpr} {A : VExpr} {u : VLevel}
    (hΓ : env.OnCtxN U n Γ) (hA : env.HasTypeN U n Γ A (.sort u)) : u.WF U :=
  let ⟨_, _, h⟩ := h hΓ hA; (HasTypeN.sort_inv h).1

/-! ## 3. The repair is satisfiable, at a non-degenerate environment -/

theorem RegConvE.zero : env.RegConvE U 0 := by
  intro _ _ _ h ht; rwa [← IsDefEqN.zero_iff.1 h]

/-- Environments all of whose constants are declared at type `Prop`. -/
def ConstPropType (env : VEnv) : Prop :=
  ∀ {c : Name} {ci : VConstant}, env.constants c = some ci → ci.type = .sort .zero

/-- For such an environment the constant residual is free, at **every** index. -/
theorem EnvReg.of_constPropType (h : ConstPropType env) : env.EnvReg U n := by
  intro Γ c ci ls h1 _ _
  rw [h h1]
  exact ⟨.succ .zero, trivial, .sort trivial⟩

theorem regPiOn_of (henv : Ordered env) (hce : env.EnvReg U n) (hinst : env.InstLvl U n)
    (hrc : env.RegConvE U n) : env.RegPiOn U n :=
  Regular.regPiOn (regular_of henv hce hinst hrc)

/-- **Regularity holds at the base index**, for any ordered environment whose constants'
types are themselves types at the index. -/
theorem regular_zero (henv : Ordered env) (hce : env.EnvReg U 0) : env.Regular U 0 :=
  regular_of henv hce (InstLvl.zero henv) RegConvE.zero

theorem regPiOn_zero (henv : Ordered env) (hce : env.EnvReg U 0) : env.RegPiOn U 0 :=
  Regular.regPiOn (regular_zero henv hce)

/-! ### The witness environment

`Theory/Typing/CycleConv.lean`'s `propLoopEnv` — two constants `A B : Prop` and the two
δ-rules `A ≡ B`, `B ≡ A` — is exactly the shape `PropConv.lean`'s `extra` discussion names
(`def MyProp : Prop := True`), and it comes with `propLoopEnv_wf`.  So the witness below is
not the empty environment: both the `const` case of the regularity induction and the
`defeqs` field are inhabited. -/

theorem propLoopEnv_constPropType : ConstPropType propLoopEnv := by
  intro c ci h
  revert h
  show (if `B = c then _ else if `A = c then _ else _) = _ → _
  split
  · intro h; cases h; rfl
  · split
    · intro h; cases h; rfl
    · intro h; exact absurd h nofun

theorem propLoopEnv_regular : propLoopEnv.Regular U 0 :=
  regular_zero propLoopEnv_wf.ordered (EnvReg.of_constPropType propLoopEnv_constPropType)

theorem propLoopEnv_regPiOn : propLoopEnv.RegPiOn U 0 :=
  Regular.regPiOn propLoopEnv_regular

/-! ### …and the witness actually fires

A Π-typed variable in a well-formed context over that environment: `RegPiOn` is applied at a
real instance, not merely shown to hold vacuously. -/

/-- `A → A`, over the witness environment. -/
def propArrow : VExpr := .forallE (.const `A []) (.const `A [])

theorem propLoopEnv_constA {Γ : List VExpr} :
    propLoopEnv.HasTypeN U n Γ (.const `A []) (.sort .zero) :=
  .const propLoopEnv_A nofun rfl

theorem propArrow_isTypeN {Γ : List VExpr} : propLoopEnv.IsTypeN U n Γ propArrow :=
  ⟨.imax .zero .zero, ⟨trivial, trivial⟩,
    .forallE trivial trivial propLoopEnv_constA propLoopEnv_constA⟩

theorem propLoopEnv_regPiOn_fires :
    ∃ u v, u.WF U ∧ v.WF U ∧
      propLoopEnv.HasTypeN U 0 [propArrow] (.const `A []) (.sort u) ∧
      propLoopEnv.HasTypeN U 0 (.const `A [] :: [propArrow]) (.const `A []) (.sort v) :=
  propLoopEnv_regPiOn (Γ := [propArrow]) (f := .bvar 0)
    ⟨trivial, propArrow_isTypeN⟩ (.bvar (Lookup.zero' rfl))

/-! ## 4. The consumer, discharged from the repair

`propTypeAgree_appCase_of` is `RegPi`'s only consumer in the tree (transitive
`getUsedConstantsAsSet` cone, `docs/handoff-regpi.md` §2).  Below is the same reduction with
`RegPi` replaced by `RegPiOn`, which costs a context hypothesis and nothing else. -/

/-- `PropTypeAgree.AppCase`, relativised to a well-formed context. -/
def PropTypeAgree.AppCaseOn (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A₀ B₀ A' : VExpr}, env.OnCtxN U n Γ →
    env.HasTypeN U n Γ f (.forallE A₀ B₀) → env.HasTypeN U n Γ a A₀ →
    (∀ {X : VExpr}, env.HasTypeN U n Γ f X →
      IsPropN env U n Γ (.forallE A₀ B₀) → IsPropN env U n Γ X) →
    env.HasTypeN U n Γ (.app f a) A' →
    IsPropN env U n Γ (B₀.inst a) → IsPropN env U n Γ A'

/-- **`propTypeAgree_appCase_of`, re-priced at a satisfiable hypothesis.**  Identical to the
original except that `RegPi` is `RegPiOn` and the context is well formed. -/
theorem propTypeAgree_appCase_on_of {k : Nat} (dinv : env.SortInvN U (k+1))
    (hreg : env.RegPiOn U (k+1)) (hinst : env.InstLvl U (k+1))
    (huniq : env.PropUniq U (k+1)) (pci : env.PropConvInv U (k+1)) :
    PropTypeAgree.AppCaseOn env U (k+1) := by
  intro Γ f a A₀ B₀ A' hΓ hf ha ihf H2 hp
  obtain ⟨_, _, hf₁, ha₁, hc⟩ := HasTypeN.app_inv H2
  obtain ⟨u₀, v₀, hu₀, hv₀, hA₀, hB₀⟩ := hreg hΓ hf
  have hv₀0 : v₀ ≈ (.zero : VLevel) := (huniq (hinst ha hB₀) hp).2 (by rfl)
  have hpi₀ : IsPropN env U (k+1) Γ (.forallE A₀ B₀) :=
    isPropN_forallE hu₀ hA₀ (isPropN_of_equiv_zero hv₀ hv₀0 hB₀)
  obtain ⟨_, _, _, hB₁⟩ := isPropN_forallE_inv dinv (ihf hf₁ hpi₀)
  exact (pci hc).1 (hinst ha₁ hB₁)

/-- `PropTypeAgree`, relativised to a well-formed context. -/
def PropTypeAgreeOn (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A A' : VExpr}, env.OnCtxN U n Γ →
    env.HasTypeN U n Γ e A → env.HasTypeN U n Γ e A' →
    IsPropN env U n Γ A → IsPropN env U n Γ A'

/-- **The six closing cases survive the relativisation.**  The context grows only at `lam`,
where the binder is a type by the rule's own premise — its universe being well formed is the
one extra datum, and it is `Regular.lvlWF`. -/
theorem propTypeAgree_on_of' {Γ e T b} (H : Stratified env U n Γ e T b) :
    b = true → env.SortInvN U n → env.Regular U n → env.PropConvInv U n →
    PropTypeAgree.AppCaseOn env U n → env.OnCtxN U n Γ →
    ∀ A', env.HasTypeN U n Γ e A' → IsPropN env U n Γ T → IsPropN env U n Γ A' := by
  induction H with
  | bvar h =>
    intro _ _ _ pci _ _ A' H2 hp
    obtain ⟨_, hl, hc⟩ := H2.bvar_inv
    exact (pci (Lookup.uniq h hl ▸ hc)).1 hp
  | sort _ => intro _ dinv _ _ _ _ _ _ hp; exact absurd hp (not_isPropN_sort dinv)
  | const h1 _ _ =>
    intro _ _ _ pci _ _ A' H2 hp
    obtain ⟨_, h1', _, _, hc⟩ := HasTypeN.const_inv H2
    cases Option.some.inj (h1'.symm.trans h1)
    exact (pci hc).1 hp
  | lam hA _ _ ih2 =>
    intro _ dinv hrg pci happ hΓ A' H2 hp
    obtain ⟨_, _, _, hbody₂, hc₂⟩ := HasTypeN.lam_inv H2
    exact (pci hc₂).1 (isPropN_forallE_congr dinv
      (fun h => ih2 (Eq.refl true) dinv hrg pci happ ⟨hΓ, _, hrg.lvlWF hΓ hA, hA⟩ _ hbody₂ h) hp)
  | forallE _ _ _ _ => intro _ dinv _ _ _ _ _ _ hp; exact absurd hp (not_isPropN_sort dinv)
  | app hf ha ihf _ =>
    intro _ dinv hrg pci happ hΓ A' H2 hp
    exact happ hΓ hf ha (fun H hpi => ihf (Eq.refl true) dinv hrg pci happ hΓ _ H hpi) H2 hp
  | conv h _ _ ih2 =>
    intro _ dinv hrg pci happ hΓ A' H2 hp
    exact ih2 (Eq.refl true) dinv hrg pci happ hΓ A' H2 ((pci h).2 hp)
  | rfl | symm | trans | sortDF | constDF | appDF | lamDF | forallEDF | beta | eta
  | proofIrrel | extra => intro hb; exact nomatch hb

theorem propTypeAgree_on_of (dinv : env.SortInvN U n) (hrg : env.Regular U n)
    (pci : env.PropConvInv U n) (happ : PropTypeAgree.AppCaseOn env U n) :
    env.PropTypeAgreeOn U n :=
  fun hΓ h1 h2 hp => propTypeAgree_on_of' h1 (Eq.refl true) dinv hrg pci happ hΓ _ h2 hp

/-- **The whole chain, with every hypothesis satisfiable.**  `RegPi` is gone; what replaces it
is `Regular`, which holds at the base index over `propLoopEnv`. -/
theorem propTypeAgreeOn_of_residuals {k : Nat} (dinv : env.SortInvN U (k+1))
    (hrg : env.Regular U (k+1)) (hinst : env.InstLvl U (k+1))
    (huniq : env.PropUniq U (k+1)) (pci : env.PropConvInv U (k+1)) :
    env.PropTypeAgreeOn U (k+1) :=
  propTypeAgree_on_of dinv hrg pci
    (propTypeAgree_appCase_on_of dinv (Regular.regPiOn hrg) hinst huniq pci)

/-! ### Non-vacuity: the relativised reduction replayed at the base index -/

theorem PropTypeAgree.AppCaseOn.zero : PropTypeAgree.AppCaseOn env U 0 := by
  intro _ _ _ _ _ _ _ hf ha _ H2 hp
  have h : env.HasTypeN U 0 _ (.app _ _) _ := .app hf ha
  exact HasTypeN.uniq_zero h H2 ▸ hp

theorem PropTypeAgreeOn.zero : env.PropTypeAgreeOn U 0 :=
  fun _ h1 h2 hp => HasTypeN.uniq_zero h1 h2 ▸ hp

/-- `propTypeAgree_on_of` reproves `PropTypeAgreeOn` at the base index from residuals that
hold — over an environment with constants and δ-rules, not the empty one. -/
theorem propTypeAgreeOn_zero_from_residuals : propLoopEnv.PropTypeAgreeOn U 0 :=
  propTypeAgree_on_of SortInvN.zero propLoopEnv_regular PropConvInv.zero
    PropTypeAgree.AppCaseOn.zero

/-! ## 5. The context hypothesis is reachable from the tree's own

`Theory/Typing/Injectivity.lean`'s targets carry `OnCtx Γ (env.IsType U)` — the *ambient*
well-formedness — and `PropConv.lean`'s docstring reads that as "`Injectivity.lean`'s targets
do not carry `OnCtx`", which is the opposite way round: they carry it, what they do not carry
is the *stratified* version.  The two are connected: a context is finite, so the indices its
entries land at have a maximum. -/

theorem IsTypeN.mono {m n : Nat} (le : m ≤ n) {Γ : List VExpr} {A : VExpr}
    (h : env.IsTypeN U m Γ A) : env.IsTypeN U n Γ A :=
  let ⟨u, hu, h⟩ := h; ⟨u, hu, h.mono le⟩

theorem OnCtxN.mono {m n : Nat} (le : m ≤ n) {Γ : List VExpr}
    (h : env.OnCtxN U m Γ) : env.OnCtxN U n Γ := OnCtx.mono (IsTypeN.mono le) h

/-- **Every ambiently well-formed context is `OnCtxN` at some index.**  The index depends on
the context, so a statement at a *fixed* `n` still has to raise it with `OnCtxN.mono`; what
this rules out is that `OnCtxN` is a hypothesis the tree's own targets cannot meet. -/
theorem OnCtxN.of_onCtx (henv : Ordered env) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → ∃ m, env.OnCtxN U m Γ
  | [], _ => ⟨0, trivial⟩
  | _::_, ⟨hΓ, u, hA⟩ => by
    obtain ⟨m, hm⟩ := OnCtxN.of_onCtx henv hΓ
    obtain ⟨m', hm'⟩ := HasType.stratifyN henv hΓ hA
    exact ⟨max m m', hm.mono (Nat.le_max_left ..),
      u, hA.sort_r henv hΓ, hm'.mono (Nat.le_max_right ..)⟩

/-! ## 6. `PropConvInv`'s `extra` case

**State of the case, read off `PropConv.lean`.**  `propConvInv_of`'s `extra` branch is
`exact r7 (.extra h1 h2 h3) h1 h2 h3` — it is discharged by the hypothesis `PropExtraConv`
and by nothing else.  So the case is *proved conditionally*, on a residual that is stated but
not proved, and `PropExtraConv.zero` is true only because `≡₀` is syntactic equality, which
makes the base index uninformative for this one residual.  The case is **open**.

The claim that it "closes mechanically" is wrong for the reason `PropConv.lean` gives:
`WF.instL_lhs_ne_sort` / `instL_lhs_ne_forallE` conclude that an endpoint *is not a given
syntactic shape*, and `PropConvInv`'s conclusion is a typing.

What follows is the reduction one step further, and it does close the case — from two
statements, one of which is discharged at a real environment. -/

/-- **The environment's rules are typed at the index.**  This is the generic obstruction
`docs/handoff-stratified.md` §16.5 names: an environment fact enters `Stratified` only at
*some* index, `mono` raises it, and nothing lowers it. -/
def DefEqTypeN (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {df : VDefEq} {ls : List VLevel},
    env.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    env.HasTypeN U n Γ (df.lhs.instL ls) (df.type.instL ls) ∧
      env.HasTypeN U n Γ (df.rhs.instL ls) (df.type.instL ls)

/-- **Two terms of one type agree on being propositions.**  The other half of the `extra`
case, and it says nothing about the environment. -/
def SameTypeProp (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e e' T : VExpr},
    env.HasTypeN U n Γ e T → env.HasTypeN U n Γ e' T →
    IsPropN env U n Γ e → IsPropN env U n Γ e'

/-- **The `extra` case, priced exactly.**  It closes from these two and nothing else — in
particular the conversion premise, which is what makes the other five conversion residuals
true at the base index, is not used. -/
theorem propExtraConv_of (hdt : env.DefEqTypeN U n) (hst : env.SameTypeProp U n) :
    env.PropExtraConv U n := by
  intro _ _ _ _ h1 h2 h3
  obtain ⟨hl, hr⟩ := hdt h1 h2 h3
  exact ⟨fun h => hst hl hr h, fun h => hst hr hl h⟩

/-- Unique typing at a proposition: the strong form of the second half. -/
def PropTypeUniq (env : VEnv) (U n : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e T : VExpr},
    env.HasTypeN U n Γ e T → IsPropN env U n Γ e → env.IsDefEqN U n Γ T (.sort .zero)

theorem PropTypeUniq.sameTypeProp (h : env.PropTypeUniq U n) : env.SameTypeProp U n :=
  fun he he' hp => .conv (h he hp) he'

theorem PropTypeUniq.zero : env.PropTypeUniq U 0 :=
  fun he hp => IsDefEqN.zero_iff.2 (HasTypeN.uniq_zero he hp)

theorem SameTypeProp.zero : env.SameTypeProp U 0 := PropTypeUniq.zero.sameTypeProp

/-! ### The environment half, discharged at the witness environment

`propLoopEnv`'s two δ-rules are exactly the `def MyProp : Prop := True` shape that
`PropConv.lean` names as the reason the shape argument fails.  Both sides of both rules are
`.const`s typed by the `const` rule, which mentions no conversion — so `DefEqTypeN` holds
there at **every** index, not just at the base one. -/

theorem propLoopEnv_constB {Γ : List VExpr} :
    propLoopEnv.HasTypeN U n Γ (.const `B []) (.sort .zero) :=
  .const propLoopEnv_B nofun rfl

theorem propLoopEnv_defEqTypeN : propLoopEnv.DefEqTypeN U n := by
  intro Γ df ls h1 _ h3
  obtain rfl | rfl | h := h1
  · cases List.eq_nil_of_length_eq_zero h3
    exact ⟨propLoopEnv_constB, propLoopEnv_constA⟩
  · cases List.eq_nil_of_length_eq_zero h3
    exact ⟨propLoopEnv_constA, propLoopEnv_constB⟩
  · exact absurd h nofun

/-- **At the witness environment the `extra` residual is environment-free**: at every index it
reduces to `SameTypeProp`, which mentions no rule. -/
theorem propLoopEnv_propExtraConv (hst : propLoopEnv.SameTypeProp U n) :
    propLoopEnv.PropExtraConv U n :=
  propExtraConv_of propLoopEnv_defEqTypeN hst

/-- …and the reduction is replayed at the base index, where both halves hold. -/
theorem propLoopEnv_propExtraConv_zero : propLoopEnv.PropExtraConv U 0 :=
  propExtraConv_of propLoopEnv_defEqTypeN SameTypeProp.zero

/-! ### The environment residuals hold *rule by rule*, at an index that depends on the rule

This is the exact shape of the §16.5 obstruction, machine-checked in both halves.  For a
**single** constant and a **single** rule the required index exists; what does not follow is a
single index that works for all of them, because `VEnv.constants` and `VEnv.defeqs` are not
finite by construction and `Stratified.mono` only raises. -/

theorem envReg_single (henv : Ordered env) {Γ : List VExpr} {c : Name} {ci : VConstant}
    {ls : List VLevel} (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.constants c = some ci) (h2 : ∀ l ∈ ls, l.WF U) (h3 : ls.length = ci.uvars) :
    ∃ m, env.IsTypeN U m Γ (ci.type.instL ls) := by
  obtain ⟨u, hu⟩ := IsDefEq.isType henv hΓ (HasType.const h1 h2 h3)
  obtain ⟨m, hm⟩ := HasType.stratifyN henv hΓ hu
  exact ⟨m, u, IsDefEq.sort_r henv hΓ hu, hm⟩

theorem defEqTypeN_single (henv : Ordered env) {Γ : List VExpr} {df : VDefEq}
    {ls : List VLevel} (h1 : env.defeqs df) (h2 : ∀ l ∈ ls, l.WF U)
    (_h3 : ls.length = df.uvars) (hΓ : OnCtx Γ (env.IsType U)) :
    ∃ m, env.HasTypeN U m Γ (df.lhs.instL ls) (df.type.instL ls) ∧
      env.HasTypeN U m Γ (df.rhs.instL ls) (df.type.instL ls) := by
  obtain ⟨hl, hr⟩ := henv.defEqWF h1
  have hl' : env.HasType U [] (df.lhs.instL ls) (df.type.instL ls) := by
    simpa using HasType.instL h2 hl
  have hr' : env.HasType U [] (df.rhs.instL ls) (df.type.instL ls) := by
    simpa using HasType.instL h2 hr
  obtain ⟨m₁, hm₁⟩ := HasType.stratifyN henv hΓ (HasType.weak0 (Γ := Γ) henv hl')
  obtain ⟨m₂, hm₂⟩ := HasType.stratifyN henv hΓ (HasType.weak0 (Γ := Γ) henv hr')
  exact ⟨max m₁ m₂, hm₁.mono (Nat.le_max_left ..), hm₂.mono (Nat.le_max_right ..)⟩

/-! ## 7. `SortNotProp` and `PropConvInv`: the dependency is a cycle

`SortNotProp.of_propConvInv` is a consequence of the *statement* `PropConvInv`, so it does not
depend on the `extra` case — nothing about `extra` makes it unsound.  What it does do is close
a loop at a fixed index: `PropConvInv` gives `SortNotProp` gives `PropNotProof`, and
`PropNotProof` is one of `propConvInv_of'`'s seven residuals.  The composite below is
machine-checked; the point is not that it is false but that `PropConvInv` occurs among the
hypotheses of a derivation of `PropConvInv`, with no descent in the index. -/

theorem propConvInv_from_sortNotProp_cycle (dinv : env.SortDisjInvN U n)
    (r1 : env.PropConstDF U n) (r2 : env.PropForallEDF U n) (r3 : env.PropAppDF U n)
    (r4 : env.PropBetaConv U n) (r5 : env.PropForallEDisjoint U n)
    (happ : PropNotProof.AppCase env U n) (r7 : env.PropExtraConv U n)
    (pci : env.PropConvInv U n) : env.PropConvInv U n :=
  propConvInv_of' dinv r1 r2 r3 r4 r5
    (propNotProof_of'' dinv (SortNotProp.of_propConvInv dinv.sort pci) happ) r7

/-! ## 8. Non-vacuity of the narrowed hypotheses

`VEnv.DefInv` is **false** at `env = ∅, U = 1, n = 1` (`DefInvRefute.defInv_one_false`), and
the refutation goes through **clause (2)** — `ForallEInvN` — alone.  Every consumer in
`PropConv.lean`, `AppCase.lean`, `UnivDiscrim.lean` and this file that used to carry `DefInv`
now carries the clause, or the pair of clauses, it actually consumes: `SortInvN` (1),
`SortForallEDisjN` (3), or `SortDisjInvN` (1 and 3, clause (2) dropped).

Narrowing on its own proves nothing.  This section **fires** each narrowed consumer, over
`CycleConv.propLoopEnv` — two constants `A B : Prop` and two δ-rules, `propLoopEnv_wf` — at
index `0`, where all three narrowed hypotheses hold.  (`AppCase.lean`'s three are fired in
`AppCase.lean` itself, §"Non-vacuity", since that file is a sibling of this one.)  `propLoopEnv` rather than `∅` because
the `const` case of these inductions and the `defeqs` field of `PropExtraConv` are **empty**
over `VEnv.empty`, so a replay there would be degenerate in exactly the way this section
exists to rule out.

Three consumers cannot be replayed here and are listed as such at the end of the section:
they are stated only at `n = k+1`, and `SortInvN propLoopEnv U 1` is open.  What the
narrowing buys *them* is that their hypothesis is no longer a refuted one — see
`docs/handoff-definv-rescue.md`.
-/

section NonVacuity

/-- Clause (1) at the base index over the witness environment. -/
theorem propLoopEnv_sortInvN0 : SortInvN propLoopEnv U 0 := SortInvN.zero

/-- Clause (3), same. -/
theorem propLoopEnv_sortForallEDisjN0 : SortForallEDisjN propLoopEnv U 0 :=
  SortForallEDisjN.zero

/-- The pair, same — this is the hypothesis that replaced `DefInv` wherever both clauses were
consumed, and it is inhabited. -/
theorem propLoopEnv_sortDisjInvN0 : SortDisjInvN propLoopEnv U 0 := SortDisjInvN.zero

/-! ### Clause (3) consumers, fired at terms that exist only over `propLoopEnv` -/

/-- **`not_isPropN_lam` fires** at the identity function on the environment's proposition `A`
— a λ that does not exist over `∅`, since `∅` has no constants. -/
theorem propLoopEnv_id_not_isProp {Γ : List VExpr} :
    ¬ IsPropN propLoopEnv U 0 Γ (.lam (.const `A []) (.bvar 0)) :=
  not_isPropN_lam propLoopEnv_sortForallEDisjN0

/-- **`propForallEDisjointCases` / `propForallEDisjoint_of` / `propForallEDisjoint_of'` fire**:
`PropForallEDisjoint` holds at index `0` over `propLoopEnv`.  Both routes are exercised —
`propForallEDisjoint_of` goes through `UniqueTypingN.sortForallEDisjoint_ofN`, which is the
call site this stream moved off the old `DefInv`-taking wrapper. -/
theorem propLoopEnv_propForallEDisjoint0 : propLoopEnv.PropForallEDisjoint U 0 :=
  propForallEDisjoint_of SortForallEDisjoint.AppCase.zero propLoopEnv_sortForallEDisjN0

theorem propLoopEnv_propForallEDisjoint0' : propLoopEnv.PropForallEDisjoint U 0 :=
  propForallEDisjoint_of' PropForallEDisjoint.AppCase.zero propLoopEnv_sortForallEDisjN0

/-- …and the conclusion has a **real instance**: `A` is a `⊢₀`-typed proposition of
`propLoopEnv`, so "it is not also Π-typed" is a statement about an inhabited premise. -/
theorem propLoopEnv_constA_not_pi {Γ : List VExpr} {X Y : VExpr} :
    ¬ propLoopEnv.HasTypeN U 0 Γ (.const `A []) (.forallE X Y) :=
  fun h => propLoopEnv_propForallEDisjoint0 propLoopEnv_constA h

/-- **`PropForallEDisjoint.appCase_iff` fires**, in the direction that carries the clause. -/
theorem propLoopEnv_propForallEDisjoint_iff0 :
    PropForallEDisjoint.AppCase propLoopEnv U 0 ↔ propLoopEnv.PropForallEDisjoint U 0 :=
  PropForallEDisjoint.appCase_iff propLoopEnv_sortForallEDisjN0

/-- **`propNotProof_appCase_ih_vacuous` fires** (`PropConv.lean`) and **`appCase_ih_vacuous`
fires** (`UnivDiscrim.lean`), at the environment's own Π-type `propArrow`.  Both say the
`app` case's induction hypothesis at the function carries no information; at index `0` the
premise `.forallE _ _ ≡₀ .sort _` is additionally syntactically impossible, which is what
makes these one-liners rather than theorems. -/
theorem propLoopEnv_propNotProof_ih_vacuous {Γ : List VExpr} {f : VExpr} :
    ∀ {p A B : VExpr},
      propLoopEnv.IsDefEqN U 0 Γ (.forallE (.const `A []) (.const `A [])) (.sort .zero) →
      propLoopEnv.HasTypeN U 0 Γ p (.sort .zero) →
      propLoopEnv.HasTypeN U 0 Γ f (.forallE A B) → False :=
  propNotProof_appCase_ih_vacuous propLoopEnv_sortForallEDisjN0

theorem propLoopEnv_appCase_ih_vacuous {Γ : List VExpr} {f : VExpr} :
    ∀ {u : VLevel} {A B : VExpr},
      propLoopEnv.IsDefEqN U 0 Γ (.forallE (.const `A []) (.const `A [])) (.sort u) →
      propLoopEnv.HasTypeN U 0 Γ f (.forallE A B) → False :=
  appCase_ih_vacuous propLoopEnv_sortForallEDisjN0

/-! ### Clause (1) consumers -/

/-- **`not_isPropN_sort` fires.** -/
theorem propLoopEnv_not_isPropN_sort {Γ : List VExpr} {l : VLevel} :
    ¬ IsPropN propLoopEnv U 0 Γ (.sort l) := not_isPropN_sort propLoopEnv_sortInvN0

/-- **`isPropN_forallE_inv` and `isPropN_forallE_congr` fire**, at the environment's Π-type
`propArrow`.  Both are *honestly* premise-empty at index `0` — `IsPropN _ 0 _ (.forallE A B)`
would need `.imax u v ≡₀ .zero`, and `≡₀` is syntactic equality — which their own docstrings
record; what fires is the statement, at a real environment and a real Π-type. -/
theorem propLoopEnv_isPropN_forallE_inv {Γ : List VExpr}
    (h : IsPropN propLoopEnv U 0 Γ propArrow) :
    ∃ u, u.WF U ∧ propLoopEnv.HasTypeN U 0 Γ (.const `A []) (.sort u) ∧
      IsPropN propLoopEnv U 0 (.const `A [] :: Γ) (.const `A []) :=
  isPropN_forallE_inv propLoopEnv_sortInvN0 h

theorem propLoopEnv_isPropN_forallE_congr {Γ : List VExpr} {B' : VExpr}
    (ih : IsPropN propLoopEnv U 0 (.const `A [] :: Γ) (.const `A []) →
      IsPropN propLoopEnv U 0 (.const `A [] :: Γ) B')
    (h : IsPropN propLoopEnv U 0 Γ propArrow) :
    IsPropN propLoopEnv U 0 Γ (.forallE (.const `A []) B') :=
  isPropN_forallE_congr propLoopEnv_sortInvN0 ih h

/-- **`propForallEDF_of` fires.** -/
theorem propLoopEnv_propForallEDF0 : propLoopEnv.PropForallEDF U 0 :=
  propForallEDF_of propLoopEnv_sortInvN0 CtxConvProp.zero RegConv.zero

/-- **`SortNotProp.of_propConvInv` fires**, and its conclusion has a real instance below. -/
theorem propLoopEnv_sortNotProp0 : propLoopEnv.SortNotProp U 0 :=
  SortNotProp.of_propConvInv propLoopEnv_sortInvN0 PropConvInv.zero

/-- **`propTypeAgree_of` / `propTypeAgree_of'` fire**, and so does
**`PropTypeAgree.appCase_iff`**. -/
theorem propLoopEnv_propTypeAgree0 : propLoopEnv.PropTypeAgree U 0 :=
  propTypeAgree_of' propLoopEnv_sortInvN0 PropConvInv.zero PropTypeAgree.AppCase.zero

theorem propLoopEnv_propTypeAgree_iff0 :
    PropTypeAgree.AppCase propLoopEnv U 0 ↔ propLoopEnv.PropTypeAgree U 0 :=
  PropTypeAgree.appCase_iff propLoopEnv_sortInvN0 PropConvInv.zero

/-- **`propTypeAgree_on_of'` / `propTypeAgree_on_of` fire** — this is
`propTypeAgreeOn_zero_from_residuals` above, restated here for the audit, and its `Regular`
hypothesis is the one that genuinely needs a non-empty environment
(`propLoopEnv_regular` goes through `propLoopEnv_constPropType`). -/
theorem propLoopEnv_propTypeAgreeOn0 : propLoopEnv.PropTypeAgreeOn U 0 :=
  propTypeAgreeOn_zero_from_residuals

/-! ### Consumers of both clauses -/

/-- **`propConvInv_of` / `propConvInv_of'` fire**, from seven residuals that all hold over
`propLoopEnv` at index `0`.  The seventh, `PropExtraConv`, is where the choice of environment
does work: over `∅` it is vacuous because `VEnv.empty` has no `defeqs`, while
`propLoopEnv_propExtraConv_zero` discharges it at an environment with **two** δ-rules. -/
theorem propLoopEnv_propConvInv0 : propLoopEnv.PropConvInv U 0 :=
  propConvInv_of' propLoopEnv_sortDisjInvN0 PropConstDF.zero PropForallEDF.zero
    PropAppDF.zero PropBetaConv.zero PropForallEDisjoint.zero PropNotProof.zero
    propLoopEnv_propExtraConv_zero

/-- **`propNotProof_of'` / `propNotProof_of''` fire**, and the conclusion has a real
instance: `B` is not a proof of `A`, two genuine `⊢₀` propositions of this environment. -/
theorem propLoopEnv_propNotProof0 : propLoopEnv.PropNotProof U 0 :=
  propNotProof_of'' propLoopEnv_sortDisjInvN0 propLoopEnv_sortNotProp0
    PropNotProof.AppCase.zero

theorem propLoopEnv_B_not_proof_A0 {Γ : List VExpr} :
    ¬ propLoopEnv.HasTypeN U 0 Γ (.const `B []) (.const `A []) :=
  fun h => propLoopEnv_propNotProof0 propLoopEnv_constB propLoopEnv_constA h

/-- **`propUniq_of` / `propUniq_of'` fire.** -/
theorem propLoopEnv_propUniq0 : propLoopEnv.PropUniq U 0 :=
  propUniq_of' propLoopEnv_sortDisjInvN0 PropUniq.AppCase.zero

/-- **`PropUniq.appCase_iff` and `PropNotProof.appCase_iff` fire.** -/
theorem propLoopEnv_propUniq_iff0 :
    PropUniq.AppCase propLoopEnv U 0 ↔ propLoopEnv.PropUniq U 0 :=
  PropUniq.appCase_iff propLoopEnv_sortDisjInvN0

theorem propLoopEnv_propNotProof_iff0 :
    PropNotProof.AppCase propLoopEnv U 0 ↔ propLoopEnv.PropNotProof U 0 :=
  PropNotProof.appCase_iff propLoopEnv_sortDisjInvN0 propLoopEnv_sortNotProp0

/-- **`propConvInv_from_sortNotProp_cycle` fires**, with every one of its nine hypotheses
discharged over `propLoopEnv` — including the `PropConvInv` that makes it a cycle. -/
theorem propLoopEnv_propConvInv_cycle0 : propLoopEnv.PropConvInv U 0 :=
  propConvInv_from_sortNotProp_cycle propLoopEnv_sortDisjInvN0 PropConstDF.zero
    PropForallEDF.zero PropAppDF.zero PropBetaConv.zero PropForallEDisjoint.zero
    PropNotProof.AppCase.zero propLoopEnv_propExtraConv_zero propLoopEnv_propConvInv0

/-! ### The three that cannot be fired at index `0`

`propTypeAgree_appCase_of` (`PropConv.lean`), `propTypeAgree_appCase_on_of` and
`propTypeAgreeOn_of_residuals` (this file) are stated only at `n = k+1`, and their narrowed
hypothesis at the smallest such index is `SortInvN env U 1`, which is **open** — over
`propLoopEnv` and over `∅` alike.  So no replay of the kind above exists for them.

What the narrowing does buy them is not nothing, and it is worth stating precisely.  Before
it, their hypothesis at `env = ∅, U = 1, k = 0` was `DefInv ∅ 1 1`, which
`DefInvRefute.defInv_one_false` **refutes** — so at that instance the three theorems were
literally vacuous.  After it, the hypothesis is `SortInvN ∅ 1 1`, which is not refuted, and
`SortClauses.empty_sortInvN_one_of_appDF` reduces it to the single residual
`SortRedAppDF ∅ 1 0`.  Their instance at `k = 0` is therefore open rather than empty.

`SortClauses.lean` is downstream of this file, so the reduction cannot be cited here as a
term; it is cited as a name. -/

end NonVacuity

end VEnv
end Lean4Lean
