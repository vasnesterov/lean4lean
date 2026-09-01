import Lean4Lean.Theory.Typing.InjChainLower
import Lean4Lean.Theory.Typing.InjSpineTransport

/-!
# The Π side collapses too, and `ConvCStrengthen` is not the gap

`Theory/Typing/InjChainLower.lean` settles the sort half of `InjMidLocal.lean` §1 negatively:
`SortChainAt` at the single term `.bvar 0` is *equivalent* to the global `ConvSortInv`.  Its Π
half is left open behind a named residual, **`ConvCStrengthen`** (strengthening for `ConvC`
chains), because `convPiInvCod_of_piChainAt_bvar` lands

    ConvC (A.liftN 1 0 :: .forallE A B :: Γ) (B.liftN 1 1) (B'.liftN 1 1)

against a goal of `ConvC (A::Γ) B B'` — the weakening image under `Ctx.LiftN 1 1`.

**That residual is an artefact of the target, not of the construction.**  The entry that has to
be stripped is the Π itself, and *strengthening across an inhabited entry is substitution*
(`ConvC.instN`, below, over `Ordered env` alone).  So the residual is only ever the
**uninhabited** Π — and no consumer in the tree ever asks for that case:

* `ConvPiInvCod`'s only consumer is `piChainAt_of_convPiInvCod`, whose premise
  `h1 : HasTypeStrong Γ f (.forallE A B) true` **is** an inhabitant of `.forallE A B`;
* likewise `ConvPiInv`'s consumers `baseUniqCAt_app`, `piChainAt_of_convPiInv` and
  `midCost_of_convInv`, all of which reach it through `uniqStrongCAt_of_baseUniqCAt`, which
  takes two typings of one subject.

So the right statement of the Π-side hypothesis is `ConvPiInvCodInhab` — `ConvPiInvCod` with the
inhabitant it always has — and then

    piChainAt_bvar_iff_convPiInvCodInhab :
      Ordered env → (PiChainAt env U (.bvar 0) ↔ ConvPiInvCodInhab env U)

is an **equivalence over `Ordered env` and nothing else**.  The Π side therefore collapses in
exactly the sense the sort side does, and `InjChainLower.lean`'s "the Π side does not collapse
the same way, and the reason is structural" is **wrong**: the structural observation it rests on
(only `bvar` can carry an arbitrary Π base type, so the context must be extended) is correct,
but the extension is *invertible* here, because the very hypothesis that produces the chain also
produces the term that inverts it.

## What this buys, stated exactly

`InjChainLower.convStep2_of_midCost_one` needs `ConvPiInv env U` on the side.  Here

    convStep2_of_localAt_bvar :
      Ordered env → SortChainAt env U (.bvar 0) → PiChainAt env U (.bvar 0) → ConvStep2 env U

takes **nothing** beyond `Ordered env`: no `ConvPiInv`, no `PiInv`, no `SortInv`, no
`ConvCStrengthen`, no `SortUniq`.  `SortUniq` and `ConvSortInv` come out with it
(`sortUniq_of_localAt_bvar`).  Both residuals are at the single term `.bvar 0`, i.e. at
`MidCost env U (.forallE (.sort .zero) (.bvar 0))` and `MidCost env U (.app (.bvar 0) (.bvar 0))`
— two *closed* terms (`convStep2_of_midCost_two`).

## And what it does not buy — read this before quoting the headline

`convStep2_iff_localAt_bvar` bounds the pair from **below** as well: modulo the two bridge
entries `env.SortInv U` and `PiInv env U` (which `InjMidLocal.midCost_all_iff_convStep2` already
spends for the same purpose), the two localised residuals at `.bvar 0` are *equivalent* to
`ConvStep2`.  So this is a **collapse, not a discharge**: after this file the whole of
`InjMidLocal.lean` §1's table is known to be worth exactly `ConvStep2`, at one variable, on both
halves.  Nothing here proves `SortChainAt`, `PiChainAt`, `ConvSortInv`, `ConvPiInvCod` or
`ConvPiInvCodInhab`; every theorem is an implication between hypotheses.

The concrete gain is negative and it is the point: **`ConvCStrengthen` is retired.**  It was the
one open residual `InjChainLower.lean` left on the Π side, and it is not needed for anything the
tree consumes.  §3 bounds it anyway, both ways: chain strengthening across an inhabited entry is
a theorem (`ConvC.strengthen_of_instN`), and the uninhabited case is the whole of the one-entry
statement (`ConvCStrengthen1Uninhab.convCStrengthen1`) — the same shape `Strengthen.lean` §12
records for the global strengthening hole, reached here without importing it (that file's
closure contains `UniqueTyping.lean`, hence `sorry`).

## Two further reformulations

* §7 removes the typing judgment from the Π residual altogether.  `.bvar 0`'s base type is
  `Lookup.zero`'s `X.lift`, and `HasTypeStrong.peelChain` turns each `true`-level typing into a
  chain out of it, so `PiChainAt env U (.bvar 0)` is *equivalent* (over `Ordered env`) to

      ConvPiFromEntry :  ConvC (X::Γ) X.lift (.forallE A B) →
                         ConvC (X::Γ) X.lift (.forallE A' B') → ConvC (A::X::Γ) B B'

  — two chains with a **common source** landing on Π-shapes have chain-linked codomains.  That
  is confluence at a Π head, with no subject and no typing in it, and it is the form a parallel
  reduction / Church–Rosser development can be aimed at.
* §8 chains §4 to both open injectivity holes through the tree's own `sorryAx`-free bridges
  (`piInvStratApp_of_convStep2`, `rigidShapeUniqNS_of_family_convStep2`).

## Axioms and cone, measured

Checked by the `#print axioms` block at the end; **nothing mentions `sorryAx`**.
`Classical.choice` appears in exactly two places: §3's classical case split and §8's hole-A
bridge (inherited from `piInvStratApp_of_convStep2`).  The import closure is 48 `Lean4Lean`
modules; `UniqueTyping.lean`, `ChurchRosser.lean` and `Strengthen.lean` are **absent**, so
`IsDefEqU.weakN_iff`, `IsDefEq.uniq`, `NormalEq.descend`, `WF.sortUniq'`, `IsDefEqU.sort_inv`,
`IsDefEqU.sort_forallE_inv` and `IsDefEqU.trans` — all measured to carry `sorryAx` on this
commit — are not consumed and not even present.  `Injectivity.lean` *is* present, carrying both
open holes; neither is reached (`#print axioms` is the witness, not the absence of a local
`sorry`).
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 Chains substitute, link by link -/

/-- **Substitution applies to a chain link by link**, over `Ordered env` and nothing else.
`ConvC.inst` (`BaseUniqChain.lean`) is the `k = 0` case with the substituted variable at the
head; this is the general `Ctx.InstN` form, which is what strengthening needs. -/
theorem ConvC.instN (henv : Ordered env) {Γ₀ : List VExpr} {e₀ A₀ : VExpr}
    (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀) (hΓ₀ : CtxStrong env U Γ₀) {k : Nat}
    {Γ₁ Γ : List VExpr} (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (hΓ : CtxStrong env U Γ)
    {A B : VExpr} (h : ConvC env U Γ₁ A B) :
    ConvC env U Γ (A.inst e₀ k) (B.inst e₀ k) := by
  induction h with
  | refl => exact .refl
  | step hl _ ih => exact .step (IsDefEqStrong.instN henv h₀ hΓ₀ W hl hΓ) ih

/-- **Chain strengthening across an *inhabited* entry is a theorem.**  The chain analogue of
`Strengthen.IsDefEqU.strengthen_of_instN`, and the reason `ConvCStrengthen`'s content is
confined to uninhabited entries. -/
theorem ConvC.strengthen_of_instN (henv : Ordered env) {Γ₀ : List VExpr} {e₀ A₀ : VExpr}
    (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀) (hΓ₀ : CtxStrong env U Γ₀) {k : Nat}
    {Γ' Γ : List VExpr} (W : Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ) (hΓ : CtxStrong env U Γ)
    {A B : VExpr} (h : ConvC env U Γ' (A.liftN 1 k) (B.liftN 1 k)) :
    ConvC env U Γ A B := by
  have := h.instN henv h₀ hΓ₀ W hΓ
  rwa [VExpr.inst_liftN, VExpr.inst_liftN] at this

/-! ## §2 The Π side, closed both ways

`ConvPiInvCod` states the codomain inversion for an *arbitrary* Π.  Every consumer in the tree
supplies a term of that Π — the subject whose two typings produced the chain.  That is the
statement below, and at `.bvar 0` it is *equivalent* to `PiChainAt`. -/

/-- **`ConvPiInvCod` with the inhabitant it always has.**  Compare `ConvPiInvCod`
(`InjChainLower.lean`), which drops `f`; the drop is what forces `ConvCStrengthen`. -/
def ConvPiInvCodInhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' f : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ f (.forallE A B) true →
    ConvC env U Γ (.forallE A B) (.forallE A' B') → ConvC env U (A::Γ) B B'

theorem ConvPiInvCod.inhab (h : ConvPiInvCod env U) : ConvPiInvCodInhab env U :=
  fun hΓ _ hc => h hΓ hc

theorem ConvPiInv.codInhab (h : ConvPiInv env U) : ConvPiInvCodInhab env U :=
  ConvPiInvCod.inhab h.cod

/-- **The headline.**  `PiChainAt` at the single term `.bvar 0` gives the whole codomain
inversion, over `Ordered env` and nothing else — no `ConvCStrengthen`.

The construction is `convPiInvCod_of_piChainAt_bvar`'s up to the last step: install a variable
of type `.forallE A B` at the head of the context, weaken the chain, transport, and read off
`ConvC (A.liftN 1 0 :: .forallE A B :: Γ) (B.liftN 1 1) (B'.liftN 1 1)`.  The last step is where
this differs: instead of *strengthening* away the installed Π variable, **substitute `f` for
it**.  `Ctx.InstN` at `k = 1` inverts the `Ctx.LiftN 1 1`, and `VExpr.inst_liftN` collapses both
endpoints. -/
theorem convPiInvCodInhab_of_piChainAt_bvar (henv : Ordered env)
    (hpc : PiChainAt env U (.bvar 0)) : ConvPiInvCodInhab env U := by
  intro Γ A B A' B' f hΓ hf hc
  cases hc with
  | refl => exact .refl
  | step hl t =>
    have hX := hl.hasType.1
    have hw := hl.defeq.sort_r henv hΓ.defeq
    have hΓX : CtxStrong env U (.forallE A B :: Γ) := ⟨hΓ, _, hX⟩
    obtain ⟨⟨uA, hA⟩, -⟩ := hl.forallE_inv' henv henv.strong hΓ (.inl rfl)
    have hΓA : CtxStrong env U (A :: Γ) := ⟨hΓ, _, hA⟩
    have hcw : ConvC env U (.forallE A B :: Γ)
        ((VExpr.forallE A B).liftN 1 0) ((VExpr.forallE A' B').liftN 1 0) :=
      (ConvC.step hl t).weakN henv (Ctx.LiftN.one (A := .forallE A B))
    have hb : env.HasTypeStrong U (.forallE A B :: Γ) (.bvar 0)
        ((VExpr.forallE A B).liftN 1 0) true :=
      .base (.bvar .zero hw (hX.weakN henv (.one (A := .forallE A B))).hasType'.1)
    have key := hpc hΓX hb (hcw.transportType henv hΓX hb)
    have W : Ctx.InstN Γ f (VExpr.forallE A B) 1
        (A.liftN 1 0 :: VExpr.forallE A B :: Γ) (A :: Γ) := by
      have := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := f) (A₀ := VExpr.forallE A B)).succ
        (A := A.liftN 1 0)
      rwa [VExpr.inst_liftN] at this
    exact key.strengthen_of_instN henv hf.refl hΓ W hΓA

/-- The converse half: the inhabited inversion localises at any subject whose base types are
already known unique.  At `.bvar 0` (`baseUniqCAt_bvar`, free) this closes the circle. -/
theorem piChainAt_of_convPiInvCodInhab (hpi : ConvPiInvCodInhab env U) {e : VExpr}
    (hbu : BaseUniqCAt env U e) : PiChainAt env U e :=
  fun hΓ h1 h2 => hpi hΓ h1 (uniqStrongCAt_of_baseUniqCAt hbu hΓ h1 h2)

/-- **The Π side, closed both ways.**  Compare `sortChainAt_bvar_iff_convSortInv`. -/
theorem piChainAt_bvar_iff_convPiInvCodInhab (henv : Ordered env) :
    PiChainAt env U (.bvar 0) ↔ ConvPiInvCodInhab env U :=
  ⟨convPiInvCodInhab_of_piChainAt_bvar henv,
    fun h => piChainAt_of_convPiInvCodInhab h baseUniqCAt_bvar⟩

/-- `PiChainAt` at one variable gives `PiChainAt` everywhere, given base uniqueness at the
subject — which the structural recursion of `baseUniqCAt_of_localAt_bvar` supplies. -/
theorem piChainAt_of_piChainAt_bvar (henv : Ordered env) (hpc : PiChainAt env U (.bvar 0))
    {e : VExpr} (hbu : BaseUniqCAt env U e) : PiChainAt env U e :=
  piChainAt_of_convPiInvCodInhab (convPiInvCodInhab_of_piChainAt_bvar henv hpc) hbu

/-! ## §3 `ConvCStrengthen`, bounded both ways anyway

Nothing above uses `ConvCStrengthen`.  For the record, here is what it is worth: the one-entry
form is implied by its restriction to uninhabited entries, exactly as `Strengthen.lean` §12
records for `StrengtheningTarget`.  The case split is classical and one line; §1 closes the
inhabited branch. -/

/-- `ConvCStrengthen` restricted to stripping a single entry. -/
def ConvCStrengthen1 (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {A B : VExpr}, Ctx.LiftN 1 k Γ Γ' →
    CtxStrong env U Γ → CtxStrong env U Γ' →
    ConvC env U Γ' (A.liftN 1 k) (B.liftN 1 k) → ConvC env U Γ A B

theorem ConvCStrengthen.one (H : ConvCStrengthen env U) : ConvCStrengthen1 env U :=
  fun W hΓ hΓ' h => H W hΓ hΓ' h

/-- The same, restricted to strippings whose entry has **no** inhabitant. -/
def ConvCStrengthen1Uninhab (env : VEnv) (U : Nat) : Prop :=
  ∀ {k : Nat} {Γ Γ' : List VExpr} {A B : VExpr}, Ctx.LiftN 1 k Γ Γ' →
    CtxStrong env U Γ → CtxStrong env U Γ' →
    (∀ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ → CtxStrong env U Γ₀ →
      ¬ env.IsDefEqStrong U Γ₀ e₀ e₀ A₀) →
    ConvC env U Γ' (A.liftN 1 k) (B.liftN 1 k) → ConvC env U Γ A B

theorem ConvCStrengthen1.uninhab (H : ConvCStrengthen1 env U) : ConvCStrengthen1Uninhab env U :=
  fun W hΓ hΓ' _ h => H W hΓ hΓ' h

/-- **The uninhabited case is the whole of the one-entry statement.** -/
theorem ConvCStrengthen1Uninhab.convCStrengthen1 (henv : Ordered env)
    (H : ConvCStrengthen1Uninhab env U) : ConvCStrengthen1 env U := by
  intro k Γ Γ' A B W hΓ hΓ' h
  by_cases hin : ∃ Γ₀ A₀ e₀, Ctx.InstN Γ₀ e₀ A₀ k Γ' Γ ∧ CtxStrong env U Γ₀ ∧
      env.IsDefEqStrong U Γ₀ e₀ e₀ A₀
  · obtain ⟨Γ₀, A₀, e₀, hI, hΓ₀, h₀⟩ := hin
    exact h.strengthen_of_instN henv h₀ hΓ₀ hI hΓ
  · exact H W hΓ hΓ' (fun Γ₀ A₀ e₀ hI hΓ₀ h₀ => hin ⟨Γ₀, A₀, e₀, hI, hΓ₀, h₀⟩) h

/-! ## §4 `ConvStep2` from the two residuals at `.bvar 0`, and nothing else -/

/-- **The whole of `BaseUniqCAt`, from the two localised residuals at the single term
`.bvar 0`.**  Compare `InjChainLower.baseUniqCAt_of_cod`, which takes the *global* `ConvSortInv`
and `ConvPiInvCod`. -/
theorem baseUniqCAt_of_localAt_bvar (henv : Ordered env)
    (hsc : SortChainAt env U (.bvar 0)) (hpc : PiChainAt env U (.bvar 0)) :
    ∀ e : VExpr, BaseUniqCAt env U e
  | .bvar _ => baseUniqCAt_bvar
  | .sort _ => baseUniqCAt_sort
  | .const _ _ => baseUniqCAt_const
  | .forallE D b => baseUniqCAt_forallE_local
      (sortChainAt_of_convSortInv (convSortInv_of_sortChainAt_bvar henv hsc)
        (baseUniqCAt_of_localAt_bvar henv hsc hpc D))
      (sortChainAt_of_convSortInv (convSortInv_of_sortChainAt_bvar henv hsc)
        (baseUniqCAt_of_localAt_bvar henv hsc hpc b))
  | .lam _ b => baseUniqCAt_lam henv
      (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of_localAt_bvar henv hsc hpc b))
  | .app f _ => baseUniqCAt_app_local henv
      (piChainAt_of_piChainAt_bvar henv hpc (baseUniqCAt_of_localAt_bvar henv hsc hpc f))

theorem baseUniqC_of_localAt_bvar (henv : Ordered env)
    (hsc : SortChainAt env U (.bvar 0)) (hpc : PiChainAt env U (.bvar 0)) : BaseUniqC env U :=
  fun hΓ h1 h2 => baseUniqCAt_of_localAt_bvar henv hsc hpc _ hΓ h1 h2

/-- **`ConvStep2` from two hypotheses at one variable.**  `InjChainLower.convStep2_of_midCost_one`
needs `ConvPiInv env U` in addition; this needs nothing beyond `Ordered env`. -/
theorem convStep2_of_localAt_bvar (henv : Ordered env)
    (hsc : SortChainAt env U (.bvar 0)) (hpc : PiChainAt env U (.bvar 0)) : ConvStep2 env U :=
  convStep2_of_baseUniqC henv (baseUniqC_of_localAt_bvar henv hsc hpc)

theorem sortUniq_of_localAt_bvar (henv : Ordered env)
    (hsc : SortChainAt env U (.bvar 0)) (hpc : PiChainAt env U (.bvar 0)) : env.SortUniq U := by
  intro Γ e u v hΓ _ _ h1 h2
  have hΓ' : CtxStrong env U Γ := .strong henv hΓ
  exact convSortInv_of_sortChainAt_bvar henv hsc hΓ'
    (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of_localAt_bvar henv hsc hpc e) hΓ'
      (h1.strong henv hΓ).hasType'.1 (h2.strong henv hΓ).hasType'.1)

/-- **`MidCost` at *two closed terms* is the whole corner.**  `MidCost` of
`.forallE (.sort .zero) (.bvar 0)` is the sort residual at `.bvar 0`; `MidCost` of
`.app (.bvar 0) (.bvar 0)` is the Π one. -/
theorem convStep2_of_midCost_two (henv : Ordered env)
    (h1 : MidCost env U (.forallE (.sort .zero) (.bvar 0)))
    (h2 : MidCost env U (.app (.bvar 0) (.bvar 0))) : ConvStep2 env U :=
  convStep2_of_localAt_bvar henv h1.2 h2

/-! ## §5 The bound from below: this is a collapse, not a discharge -/

/-- **The two residuals at `.bvar 0` are exactly `ConvStep2`**, modulo the two bridge entries
`InjMidLocal.midCost_all_iff_convStep2` already spends.  So the localisation of
`InjMidLocal.lean` §1 buys locality on *both* halves and strength on neither. -/
theorem convStep2_iff_localAt_bvar (henv : Ordered env) (hsi : env.SortInv U) (hpi : PiInv env U) :
    (SortChainAt env U (.bvar 0) ∧ PiChainAt env U (.bvar 0)) ↔ ConvStep2 env U := by
  refine ⟨fun ⟨h1, h2⟩ => convStep2_of_localAt_bvar henv h1 h2, fun hcs => ⟨?_, ?_⟩⟩
  · exact sortChainAt_of_convSortInv (convSortInv_of_convStep2 hcs hsi) baseUniqCAt_bvar
  · exact piChainAt_of_convPiInv (convPiInv_of_convStep2 henv hcs hpi) baseUniqCAt_bvar

/-! ## §6 Non-vacuity: the premises fire, over *every* ordered environment

`ProofRetypeHeads.prhPi1`/`prhPi2` are two **syntactically different** Π-types related by one
`IsDefEqStrong` link (`imax 0 0 ≈ 0`).  Installing `prhPi1` as a context entry makes `.bvar 0`
carry both, so `PiChainAt env U (.bvar 0)` and `ConvPiInvCodInhab env U` both have firing
premises with the two codomains syntactically distinct — the conclusion is not `ConvC.refl`.

Firing a premise is **not** evidence that the hypothesis is satisfiable (`ORCHESTRATOR.md`
rule 4); what it rules out is that §2 and §4 are about an empty set of instances. -/

theorem piChainAt_bvar_fires (henv : Ordered env) :
    ∃ (Γ : List VExpr) (A B A' B' f : VExpr), B ≠ B' ∧ CtxStrong env U Γ ∧
      env.HasTypeStrong U Γ f (.forallE A B) true ∧
      env.HasTypeStrong U Γ f (.forallE A' B') true ∧
      ConvC env U Γ (.forallE A B) (.forallE A' B') := by
  have h12 := prhPi12 (env := env) (U := U)
  have hw : (VLevel.imax (.succ (.succ .zero)) (.succ (.imax .zero .zero))).WF U :=
    ⟨trivial, trivial, trivial⟩
  have hΓ : CtxStrong env U [prhPi1] := ⟨trivial, _, h12.hasType.1⟩
  have h12Γ := h12.weak0 (Γ := [prhPi1]) henv
  have hf1 : env.HasTypeStrong U [prhPi1] (.bvar 0) prhPi1 true :=
    .base (.bvar .zero hw h12Γ.hasType.1.hasType'.1)
  have hf2 : env.HasTypeStrong U [prhPi1] (.bvar 0) prhPi2 true :=
    .defeq hw h12Γ h12Γ.hasType.1.hasType'.1 h12Γ.hasType.2.hasType'.1 hf1
  exact ⟨[prhPi1], .sort (.succ .zero), .sort (.imax .zero .zero), .sort (.succ .zero),
    .sort .zero, .bvar 0,
    (by intro h; injection h with h1; exact VLevel.noConfusion h1), hΓ, hf1, hf2, .one h12Γ⟩

/-! ## §7 The residual restated with no typing judgment in it

`PiChainAt env U (.bvar 0)` still mentions `HasTypeStrong`.  It need not: `.bvar 0`'s base type
is pinned by `Lookup.zero` to `X.lift` for the head entry `X`, and `HasTypeStrong.peelChain`
turns each `true`-level typing into a chain *out of that base type*.  So the residual is

    ConvPiFromEntry :  ConvC (X::Γ) X.lift (.forallE A B)  →
                       ConvC (X::Γ) X.lift (.forallE A' B') →  ConvC (A::X::Γ) B B'

— two chains with a **common source** landing on Π-shapes have chain-linked codomains.  That is
confluence at a Π head and nothing else: no typing judgment, no `HasTypeStrong`, no subject.
`piChainAt_bvar_iff_convPiFromEntry` is an equivalence over `Ordered env`.

This is the form a parallel-reduction / Church-Rosser development can be pointed at, and it is
the tightest statement of the Π half of `ConvStep2` in the tree: by §4 and §5, `ConvSortInv` and
`ConvPiFromEntry` together are *exactly* `ConvStep2`. -/

/-- **The Π half of `ConvStep2` with the typing judgment removed.**  `X.lift` is the base type
`Lookup.zero` assigns to `.bvar 0` in `X :: Γ`; `X` ranges over all types of `Γ`, so the source
of the two chains is an arbitrary term of `X :: Γ` that does not mention `.bvar 0`. -/
def ConvPiFromEntry (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {X A B A' B' : VExpr}, CtxStrong env U (X :: Γ) →
    ConvC env U (X::Γ) X.lift (.forallE A B) →
    ConvC env U (X::Γ) X.lift (.forallE A' B') → ConvC env U (A :: X :: Γ) B B'

theorem convPiFromEntry_of_piChainAt_bvar (henv : Ordered env)
    (hpc : PiChainAt env U (.bvar 0)) : ConvPiFromEntry env U := by
  intro Γ X A B A' B' hΓ h1 h2
  have ⟨hΓ0, _, hX⟩ := hΓ
  have hΓ0' : CtxStrong env U Γ := hΓ0
  have hXw := hX.weakN henv (.one (A := X))
  have hb : env.HasTypeStrong U (X::Γ) (.bvar 0) X.lift true :=
    .base (.bvar .zero (hX.defeq.sort_r henv hΓ0'.defeq) hXw.hasType'.1)
  exact hpc hΓ (h1.transportType henv hΓ hb) (h2.transportType henv hΓ hb)

theorem piChainAt_bvar_of_convPiFromEntry (h : ConvPiFromEntry env U) :
    PiChainAt env U (.bvar 0) := by
  intro Γ A B A' B' hΓ h1 h2
  obtain ⟨B₀, hb1, c1⟩ := h1.peelChain
  obtain ⟨B₀', hb2, c2⟩ := h2.peelChain
  cases hb1 with
  | bvar l1 _ _ =>
    cases hb2 with
    | bvar l2 _ _ =>
      cases l1 with
      | zero => cases l2 with
        | zero => exact h hΓ c1 c2

/-- **The Π residual is a typing-free chain statement.** -/
theorem piChainAt_bvar_iff_convPiFromEntry (henv : Ordered env) :
    PiChainAt env U (.bvar 0) ↔ ConvPiFromEntry env U :=
  ⟨convPiFromEntry_of_piChainAt_bvar henv, piChainAt_bvar_of_convPiFromEntry⟩

/-- **`ConvStep2` from `ConvSortInv` and one typing-free chain statement.** -/
theorem convStep2_of_convSortInv_convPiFromEntry (henv : Ordered env)
    (hsi : ConvSortInv env U) (hpe : ConvPiFromEntry env U) : ConvStep2 env U :=
  convStep2_of_localAt_bvar henv (sortChainAt_of_convSortInv hsi baseUniqCAt_bvar)
    (piChainAt_bvar_of_convPiFromEntry hpe)

theorem convStep2_iff_convSortInv_convPiFromEntry (henv : Ordered env) (hsi : env.SortInv U)
    (hpi : PiInv env U) :
    (ConvSortInv env U ∧ ConvPiFromEntry env U) ↔ ConvStep2 env U := by
  refine ⟨fun ⟨h1, h2⟩ => convStep2_of_convSortInv_convPiFromEntry henv h1 h2, fun hcs => ?_⟩
  refine ⟨convSortInv_of_convStep2 hcs hsi, convPiFromEntry_of_piChainAt_bvar henv ?_⟩
  exact piChainAt_of_convPiInv (convPiInv_of_convStep2 henv hcs hpi) baseUniqCAt_bvar

/-! ## §8 The two holes, from two hypotheses at one variable

`ConvStep2` is the node both injectivity holes share, and both bridges are `sorryAx`-free:
`piInvStratApp_of_convStep2` (`InjChainStep.lean`) for hole A
(`IsDefEqU.forallE_inv_stratified`) and `rigidShapeUniqNS_of_family_convStep2`
(`InjSpineTransport.lean`) for hole B (`WF.rigidShapeUniqNS`).  Composing with §4: -/

/-- **Hole A's instance, from the two residuals at `.bvar 0`.** -/
theorem piInvStratApp_of_localAt_bvar (henv : VEnv.WF env)
    (hsc : SortChainAt env U (.bvar 0)) (hpc : PiChainAt env U (.bvar 0))
    (hsi : env.SortInv U) (hpi : PiInv env U) : PiInvStratApp env U :=
  piInvStratApp_of_convStep2 henv (convStep2_of_localAt_bvar henv.ordered hsc hpc) hsi hpi

/-- **Hole B, from the two residuals at `.bvar 0` and the five conjuncts.** -/
theorem rigidShapeUniqNS_of_localAt_bvar (henv : Ordered env)
    (hsc : SortChainAt env U (.bvar 0)) (hpc : PiChainAt env U (.bvar 0))
    (hpi : env.PiInv U) (hsp : env.RigidSortPiDisj U) (hca : env.RigidConstAppInv U)
    (hcp : env.RigidConstPiDisj U) (hcs : env.RigidConstSortDisj U) :
    env.RigidShapeUniqNS U :=
  rigidShapeUniqNS_of_family_convStep2 henv (convStep2_of_localAt_bvar henv hsc hpc)
    hpi hsp hca hcp hcs

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.ConvC.instN
#print axioms Lean4Lean.VEnv.ConvC.strengthen_of_instN
#print axioms Lean4Lean.VEnv.ConvPiInvCod.inhab
#print axioms Lean4Lean.VEnv.ConvPiInv.codInhab
#print axioms Lean4Lean.VEnv.convPiInvCodInhab_of_piChainAt_bvar
#print axioms Lean4Lean.VEnv.piChainAt_of_convPiInvCodInhab
#print axioms Lean4Lean.VEnv.piChainAt_bvar_iff_convPiInvCodInhab
#print axioms Lean4Lean.VEnv.piChainAt_of_piChainAt_bvar
#print axioms Lean4Lean.VEnv.ConvCStrengthen.one
#print axioms Lean4Lean.VEnv.ConvCStrengthen1.uninhab
#print axioms Lean4Lean.VEnv.ConvCStrengthen1Uninhab.convCStrengthen1
#print axioms Lean4Lean.VEnv.baseUniqCAt_of_localAt_bvar
#print axioms Lean4Lean.VEnv.baseUniqC_of_localAt_bvar
#print axioms Lean4Lean.VEnv.convStep2_of_localAt_bvar
#print axioms Lean4Lean.VEnv.sortUniq_of_localAt_bvar
#print axioms Lean4Lean.VEnv.convStep2_of_midCost_two
#print axioms Lean4Lean.VEnv.convStep2_iff_localAt_bvar
#print axioms Lean4Lean.VEnv.piChainAt_bvar_fires
#print axioms Lean4Lean.VEnv.convPiFromEntry_of_piChainAt_bvar
#print axioms Lean4Lean.VEnv.piChainAt_bvar_of_convPiFromEntry
#print axioms Lean4Lean.VEnv.piChainAt_bvar_iff_convPiFromEntry
#print axioms Lean4Lean.VEnv.convStep2_of_convSortInv_convPiFromEntry
#print axioms Lean4Lean.VEnv.convStep2_iff_convSortInv_convPiFromEntry
#print axioms Lean4Lean.VEnv.piInvStratApp_of_localAt_bvar
#print axioms Lean4Lean.VEnv.rigidShapeUniqNS_of_localAt_bvar
end Audit
