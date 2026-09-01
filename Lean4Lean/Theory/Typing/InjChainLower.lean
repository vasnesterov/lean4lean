import Lean4Lean.Theory.Typing.InjMidLocal

/-!
# The localisation of `InjMidLocal.lean` §1 is worth **nothing** on the sort side, and the
# reason the Π side is different is that Π-types are not closed

`Theory/Typing/InjMidLocal.lean` §1 replaces the two global chain-inversion hypotheses of
`BaseUniqChain.lean` by *localised* residuals at proper subterms:

    SortChainAt env U e   -- two `HasTypeStrong … true` sort typings of `e` have `≈` levels
    PiChainAt   env U f   -- two `HasTypeStrong … true` Π typings of `f` have chain-linked cods

and bounds them from below only *globally*: `sortUniq_of_sortChainAt` needs `∀ e, SortChainAt`,
`midCost_all_iff_convStep2` needs `∀ e, MidCost`.  Its §6 concludes "§1 buys locality, not
strength", and its §0b says no route discharges either residual, "a no route found, not a
refutation".

**This file sharpens the sort half of that from a global bound to a single-term bound, and the
verdict is a collapse.**

    sortChainAt_bvar_iff_convSortInv :
      Ordered env → (SortChainAt env U (.bvar 0) ↔ ConvSortInv env U)

`SortChainAt` at the *one* term `.bvar 0` — no quantification over subjects at all — is
**equivalent** to the global hypothesis it was supposed to localise.  Hence, via
`InjMidLocal.MidCost`,

    convSortInv_of_midCost_one :
      Ordered env → MidCost env U (.forallE (.sort .zero) (.bvar 0)) → ConvSortInv env U

so `MidCost` at a *single closed term* already implies the sort half of the corner, and (with
the Π half) `ConvStep2` in full (`convStep2_of_midCost_one`).  `InjMidLocal.lean` §1's table is
therefore not a localisation of the sort residual in any useful sense: it is the same
hypothesis, reached at one variable.

## Why the collapse happens, and why it is not a defect of the proof

`SortChainAt` localises the **subject** and leaves the **context** universally quantified, and
the arbitrary sort enters through the context.  Concretely: in `Γ₊ = .sort u :: Γ` the variable
`.bvar 0` has base type `Lookup.zero`'s `(.sort u).lift`, and `(.sort u).lift = .sort u` **on
the nose** — sorts are closed, so lifting is invisible.  So for *any* `u` at all one can
manufacture a subject whose base type is `.sort u`, transport it along the chain
(`ConvC.transportType`, free), and read off `u ≈ v`.  The chain itself is carried across the
context extension by `ConvC.weakN`, which is `IsDefEqStrong.weakN` link by link and costs only
`Ordered env`.

## The Π side: the same argument breaks, at exactly one point, and structurally

`convPiInvCod_of_piChainAt_bvar` runs the identical construction for `PiChainAt` and gets

    ConvC env U (A.liftN 1 0 :: .forallE A B :: Γ) (B.liftN 1 1) (B'.liftN 1 1)

where the target is `ConvC env U (A::Γ) B B'`.  The two are related by
`Ctx.LiftN 1 1 (A::Γ) (A.liftN 1 0 :: .forallE A B :: Γ)`, i.e. the obtained statement is the
*weakening image* of the wanted one, and closing the gap is `ConvCStrengthen` — strengthening
for chains.  **That gap is structural, not an artifact:**

* `.sort u` is closed, so installing a variable of type `.sort u` costs no lifting;
  `.forallE A B` is not, so installing a variable of type `.forallE A B` lifts `A` and `B`.
* the only `HasTypeStrong` head whose *base* type can be an arbitrary Π is `bvar` — `const`
  gives closed types, `lam`/`app` require the Π to be inhabited or a function to already exist,
  `sort`/`forallE` give sorts.  So there is no way to install an arbitrary Π-typed subject
  without touching the context.

And `ConvCStrengthen` is **not** merely `Strengthen.Strengthening`: a chain's *interior* nodes
are arbitrary terms, not lifted ones, which is precisely the case
`Strengthen.TransStrengthening` isolates as the one with vacuous induction hypotheses.  So the
Π side of `InjMidLocal.lean` §1 survives this file — it is not shown to collapse, and it is not
shown to be worth anything either.

## A second, independent finding: `ConvPiInv`'s domain conjunct is dead code

`ConvPiInv` (`BaseUniqChain.lean`) concludes `ConvC Γ A A' ∧ ConvC (A::Γ) B B'`.  Every consumer
in the tree takes `.2`: `baseUniqCAt_app`, `baseUniqCAt_app_local`, `piChainAt_of_convPiInv`.
`ConvPiInvCod` below deletes the domain conjunct, and `baseUniqCAt_of_cod`, `baseUniqC_of_cod`,
`convStep2_of_cod`, `sortUniq_of_cod` re-derive the whole `BaseUniqChain`/`InjMidLocal`
development from `ConvSortInv ∧ ConvPiInvCod`.  This matters for the semantic route:
`Theory/Typing/InjSortPiModel.lean` records `PiInv`'s **domain** conjunct as dead in the set
model (`not_forallPropDomInj`); that particular death is now irrelevant to `ConvStep2`.  It does
*not* rescue anything — the codomain conjunct still needs faithfulness — but it removes one of
the two obstructions from the accounting.

## What is *not* claimed

Nothing here discharges `SortChainAt`, `PiChainAt`, `ConvSortInv`, `ConvPiInvCod` or
`ConvCStrengthen`.  Every theorem is an implication between hypotheses.  The sort-side result
is a **negative**: it says the localisation is not progress, by exhibiting the collapse.  No
non-derivability is claimed for either residual, and no environment is exhibited in which they
fail.

## A gap in the negative controls, and why no rogue environment refutes these residuals

`InjMidLocal.lean` §7 supplies negative controls for `SortInvRaw` and `VEnv.SortInv` at
`rogueSortEnv` — an environment whose single definitional equation identifies `Sort 0` with
`Sort 1`.  Those controls **do not cover the file's own localised residuals**, and cannot be
made to: they work because `IsDefEq.extra` (`Theory/Typing/Basic.lean:54`) has *three* premises
and **no** typing premises, so the rogue equation fires unconditionally.  `IsDefEqStrong.extra`
(`Theory/Typing/Strong.lean:77`) has *nine*, five of them typings — including
`[] ⊢ df.lhs.instL ls : df.type.instL ls` and the same for `rhs` — and at `rogueSortEnv` that
demands `[] ⊢ .sort .zero : .sort (.succ (.succ .zero))`, i.e. a conversion `Sort 1 ≡ Sort 2`
which the environment does not contain.  So the rogue equation never becomes a `ConvC` link.

Pushing this: a two-link chain `.sort u ⇝ M ⇝ .sort v` at `IsDefEqStrong` needs `M` typed at
both `.sort w₁ ≈ .succ u` and `.sort w₂ ≈ .succ v`, i.e. it needs a `SortUniq` violation one
level down in order to produce one.  Hence **no rogue-environment refutation of `SortChainAt`,
`PiChainAt`, `ConvSortInv` or `ConvPiInvCod` is available by this idiom**, and no non-vacuity
control of that shape exists for them.  `[analysis]` — this is a hand argument about the rule
set, not a machine-checked non-derivability result; what is machine-checked is only the premise
counts, which are read off the two inductives.

## Axioms

Checked by the `#print axioms` block at the end; nothing mentions `sorryAx`.  The import closure
is `InjMidLocal.lean`'s, unchanged, so `UniqueTyping.lean` and `ChurchRosser.lean` are still
absent and `IsDefEqU.weakN_iff`, `IsDefEq.uniq`, `NormalEq.descend`, `WF.sortUniq'`,
`IsDefEqU.sort_inv` — all measured to carry `sorryAx` on this commit — are not consumed.
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- **Chains weaken**, link by link, for `Ordered env` and nothing else.  The type index of
each link is a syntactic sort, and `(VExpr.sort u).liftN n k = .sort u` definitionally, so no
level bookkeeping appears. -/
theorem ConvC.weakN (henv : Ordered env) {n k : Nat} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') {A B : VExpr} (h : ConvC env U Γ A B) :
    ConvC env U Γ' (A.liftN n k) (B.liftN n k) := by
  induction h with
  | refl => exact .refl
  | step hl _ ih => exact .step (hl.weakN henv W) ih

/-- **A `true`-level typing transports along a chain of its type**, and this costs nothing
beyond `Ordered env` — one `HasTypeStrong.defeq` per link, each link supplying its own two
endpoint typings through `IsDefEqStrong.hasType'`.  Compare `ConvC.transport`, the same
statement for `IsDefEqStrong`. -/
theorem ConvC.transportType (henv : Ordered env) {Γ : List VExpr} (hΓ : CtxStrong env U Γ)
    {A B : VExpr} (h : ConvC env U Γ A B) :
    ∀ {e : VExpr}, env.HasTypeStrong U Γ e A true → env.HasTypeStrong U Γ e B true := by
  induction h with
  | refl => exact id
  | step hl _ ih =>
    exact fun he => ih (.defeq (hl.defeq.sort_r henv hΓ.defeq) hl hl.hasType'.1 hl.hasType'.2 he)

/-- **The headline.**  `SortChainAt` at the single term `.bvar 0` gives the global
`ConvSortInv`, over `Ordered env` and nothing else.

Given a chain `ConvC Γ (.sort u) (.sort v)`, put a variable of type `.sort u` at the head of the
context.  `(.sort u).lift = .sort u`, so `Lookup.zero` types `.bvar 0` at `.sort u` exactly, and
the weakened chain still runs from `.sort u` to `.sort v`; transport gives the second typing and
the hypothesis reads off `u ≈ v`. -/
theorem convSortInv_of_sortChainAt_bvar (henv : Ordered env)
    (hsc : SortChainAt env U (.bvar 0)) : ConvSortInv env U := by
  intro Γ u v hΓ hc
  cases hc with
  | refl => exact rfl
  | step hl t =>
    have hu : u.WF U := sortWF_of_hasTypeStrong hl.hasType'.1
    have hΓ' : CtxStrong env U (.sort u :: Γ) := ⟨hΓ, _, .sortDF hu hu rfl⟩
    have hcw : ConvC env U (.sort u :: Γ) (.sort u) (.sort v) :=
      (ConvC.step hl t).weakN henv (Ctx.LiftN.one (A := .sort u))
    have hb : env.HasTypeStrong U (.sort u :: Γ) (.bvar 0) (.sort u) true :=
      .base (.bvar (A := .sort u) (u := .succ u) .zero hu (.base (.sort' hu hu rfl)))
    exact hsc hΓ' hb (hcw.transportType henv hΓ' hb)

/-! ## The sort side, closed both ways -/

theorem sortChainAt_bvar_iff_convSortInv (henv : Ordered env) :
    SortChainAt env U (.bvar 0) ↔ ConvSortInv env U :=
  ⟨convSortInv_of_sortChainAt_bvar henv,
    fun h => sortChainAt_of_convSortInv h baseUniqCAt_bvar⟩

theorem sortUniq_of_sortChainAt_bvar (henv : Ordered env) (hpi : ConvPiInv env U)
    (hsc : SortChainAt env U (.bvar 0)) : env.SortUniq U :=
  sortUniq_of_convInv henv (convSortInv_of_sortChainAt_bvar henv hsc) hpi

/-- **`MidCost` at a single closed term is the whole hole.** -/
theorem convSortInv_of_midCost_one (henv : Ordered env)
    (h : MidCost env U (.forallE (.sort .zero) (.bvar 0))) : ConvSortInv env U :=
  convSortInv_of_sortChainAt_bvar henv h.2

theorem convStep2_of_midCost_one (henv : Ordered env) (hpi : ConvPiInv env U)
    (h : MidCost env U (.forallE (.sort .zero) (.bvar 0))) : ConvStep2 env U :=
  convStep2_of_convInv henv (convSortInv_of_midCost_one henv h) hpi

/-! ## The Π side: the domain conjunct of `ConvPiInv` is never used -/

/-- `ConvPiInv` with the domain conjunct deleted. -/
def ConvPiInvCod (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr}, CtxStrong env U Γ →
    ConvC env U Γ (.forallE A B) (.forallE A' B') → ConvC env U (A::Γ) B B'

theorem ConvPiInv.cod (h : ConvPiInv env U) : ConvPiInvCod env U := fun hΓ hc => (h hΓ hc).2

theorem piChainAt_of_convPiInvCod (hpi : ConvPiInvCod env U) {e : VExpr}
    (hbu : BaseUniqCAt env U e) : PiChainAt env U e :=
  fun hΓ h1 h2 => hpi hΓ (uniqStrongCAt_of_baseUniqCAt hbu hΓ h1 h2)

theorem baseUniqCAt_of_cod (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInvCod env U) : ∀ e : VExpr, BaseUniqCAt env U e
  | .bvar _ => baseUniqCAt_bvar
  | .sort _ => baseUniqCAt_sort
  | .const _ _ => baseUniqCAt_const
  | .forallE D b => baseUniqCAt_forallE_local
      (sortChainAt_of_convSortInv hsi (baseUniqCAt_of_cod henv hsi hpi D))
      (sortChainAt_of_convSortInv hsi (baseUniqCAt_of_cod henv hsi hpi b))
  | .lam _ b => baseUniqCAt_lam henv
      (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of_cod henv hsi hpi b))
  | .app f _ => baseUniqCAt_app_local henv
      (piChainAt_of_convPiInvCod hpi (baseUniqCAt_of_cod henv hsi hpi f))

theorem baseUniqC_of_cod (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInvCod env U) : BaseUniqC env U :=
  fun hΓ h1 h2 => baseUniqCAt_of_cod henv hsi hpi _ hΓ h1 h2

theorem convStep2_of_cod (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInvCod env U) : ConvStep2 env U :=
  convStep2_of_baseUniqC henv (baseUniqC_of_cod henv hsi hpi)

theorem sortUniq_of_cod (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInvCod env U) : env.SortUniq U := by
  intro Γ e u v hΓ _ _ h1 h2
  have hΓ' : CtxStrong env U Γ := .strong henv hΓ
  exact hsi hΓ' (uniqStrongCAt_of_baseUniqCAt (baseUniqCAt_of_cod henv hsi hpi e) hΓ'
    (h1.strong henv hΓ).hasType'.1 (h2.strong henv hΓ).hasType'.1)

/-! ## The Π side lower bound, and its exact residual -/

/-- **Strengthening for chains.**  The chain analogue of `Strengthen.Strengthening`; the hard
case is the same one `Strengthen.TransStrengthening` isolates — the *interior* nodes of the
chain are arbitrary terms, not lifted ones. -/
def ConvCStrengthen (env : VEnv) (U : Nat) : Prop :=
  ∀ {n k : Nat} {Γ Γ' : List VExpr} {A B : VExpr}, Ctx.LiftN n k Γ Γ' →
    CtxStrong env U Γ → CtxStrong env U Γ' →
    ConvC env U Γ' (A.liftN n k) (B.liftN n k) → ConvC env U Γ A B

theorem convPiInvCod_of_piChainAt_bvar (henv : Ordered env) (hst : ConvCStrengthen env U)
    (hpc : PiChainAt env U (.bvar 0)) : ConvPiInvCod env U := by
  intro Γ A B A' B' hΓ hc
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
      .base (.bvar .zero hw
        (hX.weakN henv (.one (A := .forallE A B))).hasType'.1)
    have key := hpc hΓX hb (hcw.transportType henv hΓX hb)
    have hΓAX : CtxStrong env U (A.liftN 1 0 :: .forallE A B :: Γ) :=
      ⟨hΓX, _, hA.weakN henv (.one (A := .forallE A B))⟩
    exact hst (Ctx.LiftN.one (A := .forallE A B)).succ hΓA hΓAX key

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.ConvC.weakN
#print axioms Lean4Lean.VEnv.ConvC.transportType
#print axioms Lean4Lean.VEnv.convSortInv_of_sortChainAt_bvar
#print axioms Lean4Lean.VEnv.sortChainAt_bvar_iff_convSortInv
#print axioms Lean4Lean.VEnv.sortUniq_of_sortChainAt_bvar
#print axioms Lean4Lean.VEnv.convSortInv_of_midCost_one
#print axioms Lean4Lean.VEnv.convStep2_of_midCost_one
#print axioms Lean4Lean.VEnv.ConvPiInv.cod
#print axioms Lean4Lean.VEnv.piChainAt_of_convPiInvCod
#print axioms Lean4Lean.VEnv.baseUniqCAt_of_cod
#print axioms Lean4Lean.VEnv.baseUniqC_of_cod
#print axioms Lean4Lean.VEnv.convStep2_of_cod
#print axioms Lean4Lean.VEnv.sortUniq_of_cod
#print axioms Lean4Lean.VEnv.convPiInvCod_of_piChainAt_bvar
end Audit
