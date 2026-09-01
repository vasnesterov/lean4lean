import Lean4Lean.Theory.Typing.InjMidpoint
import Lean4Lean.Theory.Typing.RawDefEq

/-!
# The two costly midpoint heads, priced exactly — and the collapse that is free

`Theory/Typing/InjMidpoint.lean` localises `ConvStep2` at its midpoint and leaves this table:

| midpoint head | its §1 pricing |
| --- | --- |
| `.bvar`, `.sort`, `.const` | nothing |
| `.lam D b` | `BaseUniqCAt` at the body |
| `.app f a` | `ConvPiInv` **+ `BaseUniqCAt` at the function** |
| `.forallE D b` | `ConvSortInv` **+ `BaseUniqCAt` at domain and body** |

**The bold parts are not needed, and the two global hypotheses are not needed either.**  Both
bottom rows go through `BaseUniqChain.baseUniqCAt_forallE` / `baseUniqCAt_app`, and in each the
`UniqStrongCAt` premises are consumed *only* as the argument of the global inversion hypothesis.
The composites are

    SortChainAt env U e  --  two `HasTypeStrong` sort typings of `e` have equivalent levels
    PiChainAt   env U f  --  two `HasTypeStrong` Π typings of `f` have chain-linked codomains

and §1 re-prices the table as

| `.app f a` | `PiChainAt` at the function — **one** hypothesis, at a proper subterm |
| `.forallE D b` | `SortChainAt` at domain and body — **two**, both at proper subterms |

with the `BaseUniqCAt` recursion gone from both rows.  `MidCost` is `InjMidpoint.MidFree` with
its two `False` clauses replaced by these prices (`midCost_of_midFree`), and
`baseUniqCAt_of_midCost` makes **no recursive call** at `.forallE` or `.app`.

## §0a So: does the `ParRedKn` grading analogy transfer?  No, and here is the reason

`Theory/Typing/KKetaRow.lean` (ledger row 47) rescued a stuck induction by *grading* the
relation, because there the failure was a descent failure — a sub-derivation one node larger.
Here there is no descent failure to fix.  Two checks:

1. **The recursion already terminates.**  `baseUniqCAt_of` is structural on the term, and
   `baseUniqCAt_of_midCost` shows the two costly heads make no recursive call at all once their
   residual is supplied.  Nothing about the two obstructions is a measure.
2. **The only case a size measure would buy is already free.**  Grading a pair of
   `HasTypeStrong` derivations by `|H₁| + |H₂|` and stating the conclusion as a `ConvC` chain
   would let one handle `HasTypeStrong.defeq` by prepending one `ConvC.step`.  That case is
   `HasTypeStrong.peelChain`'s `defeq` case, `[propext]` and hypothesis-free — *checked*, in
   `BaseUniqChain.lean`.  The remaining cases are the six heads, and `baseUniqCAt_forallE_local`
   / `baseUniqCAt_app_local` below are exactly what `forallE` and `app` then need.  (This half of
   the argument is a hand analysis of the case split, not a machine-checked non-existence
   result; what is machine-checked is that the `defeq` case costs nothing and that the two head
   cases cost exactly the two residuals.)

So the honest statement is: **`InjMidpoint.lean` §4's "there is no measure in which term plus
its own types descends" is true but mislocated.**  The residual is not a descent obligation.  It
is *inversion of a chain at a rigid head*, and inversion does not localise — see §0b.

## §0b Why the localisation of §1 cannot be pushed to a discharge

No route in this tree discharges `SortChainAt` or `PiChainAt` at **any** head, and the reason
is uniform: both speak about `HasTypeStrong … true`, and `HasTypeStrong.defeq` puts an
*unrestricted* conversion between a subject's base type and the type in question.  So every
`true`-level statement inherits the whole chain-inversion problem no matter what the subject's
head is.  Concretely `SortChainAt env U (.sort l)` — the easiest conceivable instance — still
asks one to invert `ConvC Γ (.sort (.succ l')) (.sort a)` for an arbitrary chain; the tree's only
inversion lemma for a `true`-level sort typing is `SortUniq.HasTypeStrong.sort_type`, which takes
`env.SortUniq U`, and its docstring already says the `defeq` case is where that is spent.
Contrast the three free heads of `MidFree`, which are free because their *base* types are pinned
syntactically (`Lookup.uniq`; `env.constants` is a function) or by the typing rule's own level
side condition (`sort'`).

**This is a "no route found", not a refutation** — no non-derivability is claimed here.  What
*is* proved is the lower bound: `sortUniq_of_sortChainAt` and `midCost_all_iff_convStep2`.

`sortUniq_of_sortChainAt` and `midCost_all_iff_convStep2` bound this from below: quantified over
all subjects, the localised residuals are `SortUniq`-strength and `ConvStep2` respectively.  **So
§1 buys locality, not strength** — the same verdict `InjMidpoint.lean` §2 records for the global
forms, and it must be read that way.

## §2 The one collapse that costs nothing: Carneiro's three-place judgment

`ConvC.collapse` spends `SortUniq` once per junction because `IsDefEqStrong.trans` demands a
single type index for both halves.  `Theory/Typing/RawDefEq.lean` transcribes the reference's
`Γ ⊢ e ≡ e'` (`~/lean-type-theory/axioms.tex:30–41`), whose `trans` and `symm` carry **no type**.
So

```lean
ConvC.eq_or_raw : ConvC env U Γ A B → A = B ∨ env.IsDefEqRaw U Γ A B
```

is unconditional — no `Ordered`, no `CtxStrong`, no level anywhere (`[propext]`).  Hence

```lean
convStep2_of_raw : Ordered env → SortInvRaw env U → PiInvRaw env U → ConvStep2 env U
```

where `SortInvRaw`/`PiInvRaw` are `SortInv`/`PiInv` with the premise `IsDefEqU` replaced by
`IsDefEqRaw`.  **Read this correctly.**  It is a *route*, not a reduction, and the direction of
the bound is the wrong one for a reduction:

* `SortInvRaw.sortInv`, `PiInvRaw.piInv` — the raw forms are **at least as strong** as the
  existing ones (`IsDefEqU.raw` is the one-line reason);
* the converses are `sortInvRaw_of_sortInv` / `piInvRaw_of_piInv`, both gated on `RawToU`, the
  reference's "Regularity continued", whose `trans` case is `IsDefEqU.trans`, i.e.
  `IsDefEq.uniq`.  So they are **not** available and this file does not claim them.

What the route is worth: it removes the four-place obstruction from the *statement* of the
residual.  `ConvStep2` no longer needs any level alignment, any collapse, or any `SortUniq` —
only sort- and Π-injectivity for the judgment the reference's confluence development actually
runs over.  What it does not do is supply those: `SortInvRaw`'s hard case is `trans`, which is
the confluence content, and `RawDefEq.lean`'s own closing paragraph already warns that nobody has
written that development against `IsDefEqRaw`.  Treat §2 as relocating the residual onto the
reference's judgment, and nothing more.

## §3 Non-vacuity and the negative controls

`not_sortInvRaw_rogue` refutes `SortInvRaw` in an environment whose single definitional equation
identifies `Sort 0` with `Sort 1`, so the statement is not trivially true.  `not_sortInv_rogue`
checks — rather than asserts — that the *same* environment refutes `VEnv.SortInv`, because
`IsDefEq.extra` (`Theory/Typing/Basic.lean:54`) has the same premises as `IsDefEqRaw.extra`; so
the refutation is a property both statements share and not a defect of the raw form.
`sortInvRaw_fires` fires the premise with the two levels syntactically different.

The two localised residuals are *carried*, never discharged: §1's theorems take them as
hypotheses, and §0b says they are free nowhere.  Firing a branch is not evidence that a
hypothesis is satisfiable (`ORCHESTRATOR.md` rule 4).

## §4 Cone

Nothing here is imported by anything; every statement is unconditional or takes its inputs as
hypotheses.  The `#print axioms` block at the end checks all 25 theorems; none mentions
`sorryAx`, despite `Injectivity.lean` — carrying *both* open holes — being in the import closure
through `InjMidpoint`.  The closure is 43 `Lean4Lean` modules and does **not** contain
`Theory/Typing/UniqueTyping.lean` or `ChurchRosser.lean`, so `IsDefEqU.weakN_iff`,
`IsDefEq.uniq` and `NormalEq.descend` are not even present.  Nothing here consumes
`WF.sortUniq'`, `IsDefEqU.sort_inv` or `IsDefEqU.sort_forallE_inv`, all three of which carry
`sorryAx` (ledger row 41, re-measured on this commit).
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## §1 The two hypotheses `baseUniqCAt_forallE` / `baseUniqCAt_app` actually consume -/

/-- **`ConvSortInv` localised at one subject.**  Two `HasTypeStrong` sort typings of `e` have
equivalent levels.  This is *all* `baseUniqCAt_forallE` uses `ConvSortInv` for, and it is
localised: it speaks about `e` only. -/
def SortChainAt (env : VEnv) (U : Nat) (e : VExpr) : Prop :=
  ∀ {Γ : List VExpr} {u v : VLevel}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e (.sort u) true → env.HasTypeStrong U Γ e (.sort v) true → u ≈ v

/-- **`ConvPiInv` localised at one subject, codomain half only.**  Two `HasTypeStrong` Π typings
of `f` have chain-linked codomains.  This is *all* `baseUniqCAt_app` uses `ConvPiInv` for: it
discards the domain conjunct outright. -/
def PiChainAt (env : VEnv) (U : Nat) (f : VExpr) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ f (.forallE A B) true →
    env.HasTypeStrong U Γ f (.forallE A' B') true → ConvC env U (A::Γ) B B'

/-- **`.forallE`, from two localised hypotheses at proper subterms and nothing else.**
`BaseUniqChain.baseUniqCAt_forallE` takes global `ConvSortInv` *and* `UniqStrongCAt` at the
domain and body; both `UniqStrongCAt`s are only ever fed to `ConvSortInv`, so the composite
`SortChainAt` is the real cost and the recursion disappears. -/
theorem baseUniqCAt_forallE_local {D b : VExpr}
    (hdom : SortChainAt env U D) (hbody : SortChainAt env U b) :
    BaseUniqCAt env U (.forallE D b) := by
  intro Γ A B hΓ h1 h2
  cases h1 with
  | forallE a1 a2 a3 a4 =>
    cases h2 with
    | forallE b1 b2 b3 b4 =>
      have hΓ' : CtxStrong env U (D::Γ) := ⟨hΓ, _, a3.refl⟩
      exact .one (.sortDF (l := .imax _ _) (l' := .imax _ _) ⟨a1, a2⟩ ⟨b1, b2⟩
        (VLevel.imax_congr (hdom hΓ a3 b3) (hbody hΓ' a4 b4)))

/-- **`.app`, from one localised hypothesis at the function and nothing else** — in particular
**no** `BaseUniqCAt`/`UniqStrongCAt` at the function.  `baseUniqCAt_app`'s two hypotheses
(`ConvPiInv` and `UniqStrongCAt f`) are consumed only in the composite
`(hpi hΓ (hfn hΓ a6 b6)).2`, which is `PiChainAt f` on the nose. -/
theorem baseUniqCAt_app_local (henv : Ordered env) {f a : VExpr}
    (hfn : PiChainAt env U f) : BaseUniqCAt env U (.app f a) := by
  intro Γ A B hΓ h1 h2
  cases h1 with
  | app a1 a2 a3 a4 a5 a6 a7 a8 =>
    cases h2 with
    | app b1 b2 b3 b4 b5 b6 b7 b8 =>
      exact ConvC.inst henv hΓ a7.refl (hfn hΓ a6 b6)

/-! ## §2 Nothing is lost: the old hypotheses give the new ones -/

theorem sortChainAt_of_convSortInv (hsi : ConvSortInv env U) {e : VExpr}
    (hbu : BaseUniqCAt env U e) : SortChainAt env U e :=
  fun hΓ h1 h2 => hsi hΓ (uniqStrongCAt_of_baseUniqCAt hbu hΓ h1 h2)

theorem piChainAt_of_convPiInv (hpi : ConvPiInv env U) {e : VExpr}
    (hbu : BaseUniqCAt env U e) : PiChainAt env U e :=
  fun hΓ h1 h2 => (hpi hΓ (uniqStrongCAt_of_baseUniqCAt hbu hΓ h1 h2)).2

/-! ## §3 The localised midpoint table -/

theorem convStep2At_forallE_local (henv : Ordered env) {D b : VExpr}
    (hdom : SortChainAt env U D) (hbody : SortChainAt env U b) :
    ConvStep2At env U (.forallE D b) :=
  convStep2At_of_baseUniqCAt henv (baseUniqCAt_forallE_local hdom hbody)

theorem convStep2At_app_local (henv : Ordered env) {f a : VExpr}
    (hfn : PiChainAt env U f) : ConvStep2At env U (.app f a) :=
  convStep2At_of_baseUniqCAt henv (baseUniqCAt_app_local henv hfn)

/-- **`InjMidpoint.MidFree`, extended.**  The free heads, closed under `.lam`, plus the two
costly heads priced at their *localised* residuals.  Compare `MidFree`, whose `.forallE` and
`.app` clauses are `False`. -/
def MidCost (env : VEnv) (U : Nat) : VExpr → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .lam _ b => MidCost env U b
  | .forallE D b => SortChainAt env U D ∧ SortChainAt env U b
  | .app f _ => PiChainAt env U f

theorem baseUniqCAt_of_midCost (henv : Ordered env) :
    ∀ {e : VExpr}, MidCost env U e → BaseUniqCAt env U e := by
  intro e
  induction e with
  | bvar => exact fun _ => baseUniqCAt_bvar
  | sort => exact fun _ => baseUniqCAt_sort
  | const => exact fun _ => baseUniqCAt_const
  | app _ _ ihf _ => exact fun h => baseUniqCAt_app_local henv h
  | forallE _ _ _ _ => exact fun h => baseUniqCAt_forallE_local h.1 h.2
  | lam _ _ _ ihb => exact fun h => baseUniqCAt_lam henv (uniqStrongCAt_of_baseUniqCAt (ihb h))

theorem convStep2At_of_midCost (henv : Ordered env) {Y : VExpr} (h : MidCost env U Y) :
    ConvStep2At env U Y :=
  convStep2At_of_baseUniqCAt henv (baseUniqCAt_of_midCost henv h)

/-- `MidCost` extends `MidFree` **as a definition**: the two heads `MidFree` sends to `False` are
priced rather than excluded.  No *instance* of the extension is claimed — the two prices are
hypotheses, and §0b says nothing in this tree discharges them. -/
theorem midCost_of_midFree : ∀ {e : VExpr}, MidFree e → MidCost env U e := by
  intro e
  induction e with
  | bvar => exact id
  | sort => exact id
  | const => exact id
  | app => exact fun h => h.elim
  | forallE => exact fun h => h.elim
  | lam _ _ _ ihb => exact ihb

/-! ## §4 The chain collapses into the reference's three-place judgment for free -/

/-- **A `ConvC` chain is a `IsDefEqRaw` conversion, unconditionally.**

`ConvC.collapse` spends one `SortUniq` per junction to compose the chain into a single
*four-place* `IsDefEqStrong`.  Carneiro's `Γ ⊢ e ≡ e'` (`RawDefEq.IsDefEqRaw`) has a type-free
`trans` rule, so composing costs nothing there.  The `refl` case cannot produce
`IsDefEqRaw.refl` (which wants a typing), so the conclusion is a disjunction — which is
exactly as strong for both consumers below. -/
theorem ConvC.eq_or_raw {Γ : List VExpr} {A B : VExpr} (h : ConvC env U Γ A B) :
    A = B ∨ env.IsDefEqRaw U Γ A B := by
  induction h with
  | refl => exact .inl rfl
  | step hl _ ih =>
    refine .inr ?_
    match ih with
    | .inl e => exact e ▸ hl.defeq.raw
    | .inr t => exact hl.defeq.raw.trans t

/-- Sort injectivity for the reference's judgment. -/
def SortInvRaw (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {u v : VLevel}, OnCtx Γ (env.IsType U) →
    env.IsDefEqRaw U Γ (.sort u) (.sort v) → u ≈ v

/-- Π-injectivity for the reference's judgment; conclusion verbatim from `PiInv`. -/
def PiInvRaw (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B A' B' : VExpr}, OnCtx Γ (env.IsType U) →
    env.IsDefEqRaw U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u)

theorem convSortInv_of_sortInvRaw (h : SortInvRaw env U) : ConvSortInv env U := by
  intro Γ u v hΓ hc
  rcases hc.eq_or_raw with e | hr
  · injection e with e'; subst e'; exact rfl
  · exact h hΓ.defeq hr

theorem convPiInv_of_piInvRaw (henv : Ordered env) (h : PiInvRaw env U) : ConvPiInv env U := by
  intro Γ A B A' B' hΓ hc
  rcases hc.eq_or_raw with e | hr
  · injection e with e1 e2; subst e1; subst e2; exact ⟨.refl, .refl⟩
  · obtain ⟨⟨u1, hd⟩, u2, hb⟩ := h hΓ.defeq hr
    exact ⟨.one (hd.strong henv hΓ.defeq),
      .one (hb.strong henv (Γ := _::_) ⟨hΓ.defeq, _, hd.hasType.1⟩)⟩

/-- **`ConvStep2` from reference-shaped injectivity, with no collapse anywhere.** -/
theorem convStep2_of_raw (henv : Ordered env) (hsr : SortInvRaw env U) (hpr : PiInvRaw env U) :
    ConvStep2 env U :=
  convStep2_of_convInv henv (convSortInv_of_sortInvRaw hsr) (convPiInv_of_piInvRaw henv hpr)

/-! ## §5 Bounds on the raw forms, both ways -/

theorem SortInvRaw.sortInv (h : SortInvRaw env U) : env.SortInv U := fun hΓ hd => h hΓ hd.raw

theorem PiInvRaw.piInv (h : PiInvRaw env U) : PiInv env U := fun hΓ hd => h hΓ hd.raw

/-- The reference's "Regularity continued" — the converse of `IsDefEq.raw`, packaged.  Its
`trans` case is `IsDefEqU.trans`, i.e. `IsDefEq.uniq`; that is *exactly* why the two converses
below are not available. -/
def RawToU (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ : VExpr}, OnCtx Γ (env.IsType U) →
    env.IsDefEqRaw U Γ e₁ e₂ → env.IsDefEqU U Γ e₁ e₂

theorem sortInvRaw_of_sortInv (hru : RawToU env U) (h : env.SortInv U) : SortInvRaw env U :=
  fun hΓ hr => h hΓ (hru hΓ hr)

theorem piInvRaw_of_piInv (hru : RawToU env U) (h : PiInv env U) : PiInvRaw env U :=
  fun hΓ hr => h hΓ (hru hΓ hr)

/-! ## §6 The localisation is per-midpoint only: globally it is the same node

Bound the two localised residuals from **below**.  Quantified over all subjects they are not
weaker than what they replaced, so §1–§3 buy locality, not strength — exactly the verdict
`InjMidpoint.lean` §2 records for the global statements. -/

theorem sortUniq_of_sortChainAt (henv : Ordered env) (h : ∀ e, SortChainAt env U e) :
    env.SortUniq U := by
  intro Γ e u v hΓ _ _ h1 h2
  have hΓ' : CtxStrong env U Γ := .strong henv hΓ
  exact h e hΓ' (h1.strong henv hΓ).hasType'.1 (h2.strong henv hΓ).hasType'.1

theorem baseUniqC_of_midCost (henv : Ordered env) (h : ∀ e, MidCost env U e) :
    BaseUniqC env U := fun hΓ h1 h2 => baseUniqCAt_of_midCost henv (h _) hΓ h1 h2

theorem convStep2_of_midCost (henv : Ordered env) (h : ∀ e, MidCost env U e) :
    ConvStep2 env U := convStep2_of_baseUniqC henv (baseUniqC_of_midCost henv h)

/-- The converse of `baseUniqC_of_midCost`'s input: the two chain-inversion hypotheses supply
`MidCost` everywhere.  With `sortUniq_of_sortChainAt` this closes the circle:
`(∀ e, MidCost) ⟺ ConvStep2` modulo the two bridge entries. -/
theorem midCost_of_convInv (henv : Ordered env) (hsi : ConvSortInv env U)
    (hpi : ConvPiInv env U) : ∀ e : VExpr, MidCost env U e
  | .bvar _ => trivial
  | .sort _ => trivial
  | .const _ _ => trivial
  | .lam _ b => midCost_of_convInv henv hsi hpi b
  | .forallE D b => ⟨sortChainAt_of_convSortInv hsi (baseUniqCAt_of henv hsi hpi D),
      sortChainAt_of_convSortInv hsi (baseUniqCAt_of henv hsi hpi b)⟩
  | .app f _ => piChainAt_of_convPiInv hpi (baseUniqCAt_of henv hsi hpi f)

theorem midCost_all_iff_convStep2 (henv : Ordered env) (hsi : env.SortInv U)
    (hpi : PiInv env U) : (∀ e, MidCost env U e) ↔ ConvStep2 env U := by
  refine ⟨convStep2_of_midCost henv, fun hcs => ?_⟩
  exact midCost_of_convInv henv (convSortInv_of_convStep2 hcs hsi)
    (convPiInv_of_convStep2 henv hcs hpi)

/-! ## §7 The raw forms have content, and it is the same content `SortInv` has

`SortInvRaw` is refutable at a rogue environment, and its premise fires with the two levels
syntactically different.  The refutation is **not** a defect of the raw form: `IsDefEq.extra`
(`Theory/Typing/Basic.lean:54`) has character-for-character the same premises as
`IsDefEqRaw.extra`, so the identical witness refutes `VEnv.SortInv` at the same environment.
The moral is that both statements need an environment hypothesis, and neither is trivial. -/

/-- An environment whose single definitional equation identifies `Sort 0` with `Sort 1`. -/
def rogueSortEnv : VEnv where
  constants _ := none
  defeqs df := df = ⟨0, .sort .zero, .sort (.succ .zero), .sort (.succ (.succ .zero))⟩

theorem not_sortInvRaw_rogue : ¬ SortInvRaw rogueSortEnv 0 := by
  intro h
  have hr : rogueSortEnv.IsDefEqRaw 0 [] (.sort .zero) (.sort (.succ .zero)) := by
    have := IsDefEqRaw.extra (env := rogueSortEnv) (U := 0) (Γ := []) (ls := [])
      (df := ⟨0, .sort .zero, .sort (.succ .zero), .sort (.succ (.succ .zero))⟩)
      rfl (by simp) rfl
    simpa [VExpr.instL, VLevel.inst] using this
  have := VLevel.equiv_def.1 (h (Γ := []) trivial hr) []
  simp [VLevel.eval] at this

/-- **The parity claim, checked rather than asserted.**  The *same* environment refutes
`VEnv.SortInv`, because `IsDefEq.extra` (`Theory/Typing/Basic.lean:54`) has the same premises as
`IsDefEqRaw.extra`.  So `not_sortInvRaw_rogue` is not evidence against the raw form. -/
theorem not_sortInv_rogue : ¬ rogueSortEnv.SortInv 0 := by
  intro h
  have hd : rogueSortEnv.IsDefEq 0 [] (.sort .zero) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) := by
    have := IsDefEq.extra (env := rogueSortEnv) (uvars := 0) (Γ := []) (ls := [])
      (df := ⟨0, .sort .zero, .sort (.succ .zero), .sort (.succ (.succ .zero))⟩)
      rfl (by simp) rfl
    simpa [VExpr.instL, VLevel.inst] using this
  have := VLevel.equiv_def.1 (h (Γ := []) trivial ⟨_, hd⟩) []
  simp [VLevel.eval] at this

/-- The premise fires with the two levels syntactically different, so `SortInvRaw` is not
vacuous either. -/
theorem sortInvRaw_fires (env : VEnv) (U : Nat) :
    ((VExpr.sort (.imax .zero .zero) : VExpr) ≠ .sort .zero) ∧
      env.IsDefEqRaw U [] (.sort (.imax .zero .zero)) (.sort .zero) :=
  ⟨by intro h; injection h with h; exact VLevel.noConfusion h,
   .sortDF ⟨trivial, trivial⟩ trivial VLevel.imax_zero⟩

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.baseUniqCAt_forallE_local
#print axioms Lean4Lean.VEnv.baseUniqCAt_app_local
#print axioms Lean4Lean.VEnv.sortChainAt_of_convSortInv
#print axioms Lean4Lean.VEnv.piChainAt_of_convPiInv
#print axioms Lean4Lean.VEnv.convStep2At_forallE_local
#print axioms Lean4Lean.VEnv.convStep2At_app_local
#print axioms Lean4Lean.VEnv.baseUniqCAt_of_midCost
#print axioms Lean4Lean.VEnv.convStep2At_of_midCost
#print axioms Lean4Lean.VEnv.midCost_of_midFree
#print axioms Lean4Lean.VEnv.ConvC.eq_or_raw
#print axioms Lean4Lean.VEnv.convSortInv_of_sortInvRaw
#print axioms Lean4Lean.VEnv.convPiInv_of_piInvRaw
#print axioms Lean4Lean.VEnv.convStep2_of_raw
#print axioms Lean4Lean.VEnv.SortInvRaw.sortInv
#print axioms Lean4Lean.VEnv.PiInvRaw.piInv
#print axioms Lean4Lean.VEnv.sortInvRaw_of_sortInv
#print axioms Lean4Lean.VEnv.piInvRaw_of_piInv
#print axioms Lean4Lean.VEnv.sortUniq_of_sortChainAt
#print axioms Lean4Lean.VEnv.baseUniqC_of_midCost
#print axioms Lean4Lean.VEnv.convStep2_of_midCost
#print axioms Lean4Lean.VEnv.midCost_of_convInv
#print axioms Lean4Lean.VEnv.midCost_all_iff_convStep2
#print axioms Lean4Lean.VEnv.not_sortInvRaw_rogue
#print axioms Lean4Lean.VEnv.not_sortInv_rogue
#print axioms Lean4Lean.VEnv.sortInvRaw_fires
end Audit
