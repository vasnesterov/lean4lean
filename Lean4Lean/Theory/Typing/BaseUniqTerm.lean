import Lean4Lean.Theory.Typing.ProofRetypeHeads
-- Imported only so that `Experimental/ConeJoin.lean` (not this stream's file) reaches
-- `BaseUniqChain.lean` without an edit outside this stream's own files.  Nothing below uses it.
import Lean4Lean.Theory.Typing.BaseUniqChain

/-!
# `BaseUniq` by induction on the **term**

`Theory/Typing/ProofRetypeHeads.lean` reduces all four residuals of
`IsDefEqStrong.retypes` to one statement, `BaseUniq`, and prices it head by head:

| head | discharged by | Π-injectivity? |
|---|---|---|
| `.bvar`, `.const`, `.sort` | nothing at all | no |
| `.forallE` | `SortUniq` alone | no |
| `.lam` | unique typing at the **body** — a proper subterm | no |
| `.app` | unique typing at the **function** — a proper subterm — plus `PiInv` | yes |

Two of those rows call for *unique typing at a proper subterm*, and the file it comes from
states it globally (`UniqStrong`), which turns the table into a circle: `baseUniq_of` would
consume `UniqStrong`, and `uniqStrong_of_baseUniq` produces `UniqStrong` from `BaseUniq` at
**all** terms.

**The circle is not real, and this file machine-checks that.**  The load-bearing observation
is about `HasTypeStrong.peelEq`: peeling `defeq` wrappers changes the *type*, never the
*subject*.  So `uniqStrong_of_baseUniq`'s proof, run at a fixed subject `e`, consumes
`BaseUniq` **only at `e`** — never at any other term.  Indexing both predicates by the subject
(`BaseUniqAt`, `UniqStrongAt`) makes that visible to the elaborator, and the recursion then
runs on `VExpr`'s own structure:

* `.lam D b` needs `UniqStrongAt b`, which needs `BaseUniqAt b` — `b` is a proper subterm;
* `.app f a` needs `UniqStrongAt f`, which needs `BaseUniqAt f` — `f` is a proper subterm;
* the other four heads need no recursive call at all.

Hence **`baseUniq_of_sortUniq_piInv`**: `Ordered env → SortUniq → PiInv → BaseUniq`, and with
it

```
retypes_of_sortUniq_piInv : Ordered env → SortUniq env U → PiInv env U →
  IsDefEqStrong U Γ e₁ e₂ A → CtxStrong env U Γ → Retypes env U Γ e₁ e₂
```

with **no `VEnv.WF`, no stratification, and no `PiInvStratApp`** — where
`RetypeAdmissible.lean`'s `retypes_of_piInvStratApp` needed all three.

## What the delta actually is — read this before quoting the headline

The *implication* is not new.  `Injectivity.piInvStratApp_of` already gives
`VEnv.WF + SortUniq + PiInv → PiInvStratApp`, and `RetypeAdmissible.retypes_of_piInvStratApp`
turns that into `retypes`.  `retypes_of_sortUniq_piInv_via_strat` below is that composite,
written out so the comparison is a hypothesis list rather than a claim.  What is new:

| | via `PiInvStratApp` | this file |
|---|---|---|
| environment hypothesis | `VEnv.WF env` | **`Ordered env`** |
| axioms | `propext, Classical.choice, Quot.sound` | **`propext, Quot.sound`** |
| machinery | `HasTypeStratified`, `uniqAux`, height induction | none |
| shape of the induction | over `IsDefEqStrong`, height-indexed | **structural recursion on `VExpr`** |

## The localisation goes through at the subject and **not** at the type **[SUPERSEDED]**

**Corrected on 2026-08-30 by `Theory/Typing/BaseUniqChain.lean`.**  The paragraph below is
kept because it states the failing step correctly *for the conclusion it assumed* — a single
equation.  With the conclusion stated as a **chain** (`ConvC`), `peelChain` takes no hypothesis
at all, `uniqStrongCAt_of_baseUniqCAt` takes no hypothesis at all, and `SortUniq` disappears
from this route entirely; what survives is `ConvSortInv`, sort injectivity along a chain, and
that is consumed at the Π's **own domain and body**, both proper subterms.  The corner's circle
is not cut — `sortUniq_iff_convSortInv` says the two are the same hypothesis — but the claim
*"`SortUniq` is used at a place the term recursion does not reach"* is false as stated.

`SortUniq` survives as a hypothesis, and the exact reason is worth recording, because the
obvious next move is to localise it the same way.  `baseUniqAt_forallE` uses `SortUniq` only at
the Π's *own* domain and body — both proper subterms — so it would localise.
`uniqStrongAt_of_baseUniqAt` does not: it goes through `HasTypeStrong.peelEq`, whose `defeq`
case applies `SortUniq` at the derivation's intermediate **type** `A`, which is an arbitrary
term with no structural relation to the subject.  Trying instead to prove `UniqStrongAt` by
induction on the derivation hits the same wall in the same case: the two conversions
`A' ≡ A : .sort u` and `A' ≡ B : .sort w` are indexed at *different* sorts, and composing them
is the four-place obstruction (`handoff-injectivity.md` §2).  So `SortUniq` is not a passenger
here; it is used at a place the term recursion does not reach.

## What this does *not* do **[analysis]**

It does not cut the corner's circle.  `SortUniq` is still a hypothesis, and
`sortUniq_iff_piInvStratApp` (`Injectivity.lean`) says `SortUniq` and `PiInvStratApp` are
interderivable given `PiInv`.  What changes is the *shape* of the demand: the `retypes`
obligation is now discharged from the two statements the corner already names as its
irreducible halves (`SortUniq`, the level half; `PiInv`, the normalisation half), rather than
from the stratified fusion of the two, and the induction that discharges it is a structural
recursion on `VExpr` rather than an induction over a derivation carrying a height index.

Every implication below is an **upper** bound.  Nothing here shows that `BaseUniq` *requires*
`PiInv`, and no refutation of `BaseUniq` is offered; see `ProofRetypeHeads.lean`'s
"What is *not* claimed".

## Axioms

Every declaration is checked by the `#print axioms` block at the end; none mentions `sorryAx`.
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## Subject-indexed forms

`BaseUniq` and `UniqStrong` with the subject term pulled out of the `∀`.  `BaseUniq env U` is
`∀ e, BaseUniqAt env U e` definitionally-up-to-binder-order, and `baseUniq_of_baseUniqAt`
below is that repackaging. -/

/-- `BaseUniq` at a single subject term. -/
def BaseUniqAt (env : VEnv) (U : Nat) (e : VExpr) : Prop :=
  ∀ {Γ : List VExpr} {A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A false → env.HasTypeStrong U Γ e B false →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)

/-- `UniqStrong` at a single subject term. -/
def UniqStrongAt (env : VEnv) (U : Nat) (e : VExpr) : Prop :=
  ∀ {Γ : List VExpr} {A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A true → env.HasTypeStrong U Γ e B true →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)

/-- **The check the whole file turns on.**  `uniqStrong_of_baseUniq`, run at a fixed subject,
uses `BaseUniq` *only at that subject*: `HasTypeStrong.peelEq` rewrites the type and leaves the
subject alone, so the two base typings it produces are typings of the same `e` the conclusion
is about.  Nothing here re-enters `BaseUniq` at another term. -/
theorem uniqStrongAt_of_baseUniqAt (henv : Ordered env) (hsu : env.SortUniq U)
    {e : VExpr} (hbu : BaseUniqAt env U e) : UniqStrongAt env U e := by
  intro Γ A B hΓ h1 h2
  obtain ⟨A₀, hA₀, u1, e1⟩ := h1.peelEq henv hsu hΓ
  obtain ⟨B₀, hB₀, u2, e2⟩ := h2.peelEq henv hsu hΓ
  obtain ⟨w, e0⟩ := hbu hΓ hA₀ hB₀
  have hu1 := e1.defeq.sort_r henv hΓ.defeq
  have hu2 := e2.defeq.sort_r henv hΓ.defeq
  have hw := e0.defeq.sort_r henv hΓ.defeq
  have hwu1 := hsu hΓ.defeq hw hu1 e0.hasType.1.defeq e1.hasType.1.defeq
  have e0' := e0.atSort hw hu1 hwu1
  have hu2u1 := hsu hΓ.defeq hu2 hu1 e2.hasType.1.defeq e0'.hasType.2.defeq
  exact ⟨u1, (e1.symm.trans e0').trans (e2.atSort hu2 hu1 hu2u1)⟩

/-! ## The six heads -/

/-- `.bvar` is free: `Lookup.uniq` makes the two base types syntactically equal. -/
theorem baseUniqAt_bvar {i : Nat} : BaseUniqAt env U (.bvar i) := by
  intro Γ A B _ h1 h2
  cases h1 with
  | bvar l1 u1 t1 => cases h2 with | bvar l2 u2 t2 => cases l1.uniq l2; exact ⟨_, t1.refl⟩

/-- `.const` is free: `env.constants` is a function, so the two base types are syntactically
equal. -/
theorem baseUniqAt_const {c : Name} {ls : List VLevel} : BaseUniqAt env U (.const c ls) := by
  intro Γ A B _ h1 h2
  cases h1 with
  | const c1 c2 c3 c4 c5 c6 =>
    cases h2 with
    | const d1 d2 d3 d4 d5 d6 => cases c1.symm.trans d1; exact ⟨_, c6.refl⟩

/-- `.sort` is free: the two base types are `.sort (.succ l')` and `.sort (.succ l'')` with
`l ≈ l'` and `l ≈ l''`, and `sortDF` closes it. -/
theorem baseUniqAt_sort {l : VLevel} : BaseUniqAt env U (.sort l) := by
  intro Γ A B _ h1 h2
  cases h1 with
  | sort' a1 a2 a3 =>
    cases h2 with
    | sort' b1 b2 b3 =>
      exact ⟨_, .sortDF (l := .succ _) (l' := .succ _) a2 b2
        (VLevel.succ_congr (a3.symm.trans b3))⟩

/-- `.forallE` costs `SortUniq` and nothing else — in particular no Π-injectivity and no
recursive call. -/
theorem baseUniqAt_forallE (hsu : env.SortUniq U) {D b : VExpr} :
    BaseUniqAt env U (.forallE D b) := by
  intro Γ A B hΓ h1 h2
  cases h1 with
  | forallE a1 a2 a3 a4 =>
    cases h2 with
    | forallE b1 b2 b3 b4 =>
      have hu := hsu hΓ.defeq a1 b1 a3.hasType b3.hasType
      have hv := hsu (Γ := D::Γ) ⟨hΓ.defeq, _, a3.hasType⟩ a2 b2 a4.hasType b4.hasType
      exact ⟨_, .sortDF (l := .imax _ _) (l' := .imax _ _) ⟨a1, a2⟩ ⟨b1, b2⟩
        (VLevel.imax_congr hu hv)⟩

/-- `.lam` costs unique typing at the **body** — a proper subterm — and nothing else. -/
theorem baseUniqAt_lam (henv : Ordered env) {D b : VExpr}
    (hbody : UniqStrongAt env U b) : BaseUniqAt env U (.lam D b) := by
  intro Γ A B hΓ h1 h2
  cases h1 with
  | lam a1 a2 a3 a4 a5 a6 =>
    cases h2 with
    | lam b1 b2 b3 b4 b5 b6 =>
      have hΓ' : CtxStrong env U (D::Γ) := ⟨hΓ, _, a3.refl⟩
      obtain ⟨w, hw⟩ := hbody hΓ' a5 b5
      exact ⟨_, .forallEDF a1 (hw.defeq.sort_r henv hΓ'.defeq) a3.refl hw hw⟩

/-- `.app` costs unique typing at the **function** — a proper subterm — plus `PiInv`.  This
is the only head at which Π-injectivity enters. -/
theorem baseUniqAt_app (henv : Ordered env) (hpi : PiInv env U) {f a : VExpr}
    (hfn : UniqStrongAt env U f) : BaseUniqAt env U (.app f a) := by
  intro Γ A B hΓ h1 h2
  cases h1 with
  | app a1 a2 a3 a4 a5 a6 a7 a8 =>
    cases h2 with
    | app b1 b2 b3 b4 b5 b6 b7 b8 =>
      obtain ⟨w, hw⟩ := hfn hΓ a6 b6
      obtain ⟨-, u, hB⟩ := hpi hΓ.defeq ⟨_, hw.defeq⟩
      exact ⟨u, (IsDefEq.instDF henv hΓ.defeq hB a7.refl.defeq).strong henv hΓ.defeq⟩

/-! ## The induction on the term -/

/-- **`BaseUniq` at every term, by structural recursion on the term.**

The two recursive calls are at `f` in `.app f a` and at `b` in `.lam D b`; both are proper
subterms, and each is routed through `uniqStrongAt_of_baseUniqAt` at the *same* subterm.
No case re-enters the statement at an unrelated term, which is what
`uniqStrong_of_baseUniq` (stated globally) would have forced. -/
theorem baseUniqAt_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) : ∀ e : VExpr, BaseUniqAt env U e
  | .bvar _ => baseUniqAt_bvar
  | .sort _ => baseUniqAt_sort
  | .const _ _ => baseUniqAt_const
  | .forallE _ _ => baseUniqAt_forallE hsu
  | .lam _ b => baseUniqAt_lam henv
      (uniqStrongAt_of_baseUniqAt henv hsu (baseUniqAt_of_sortUniq_piInv henv hsu hpi b))
  | .app f _ => baseUniqAt_app henv hpi
      (uniqStrongAt_of_baseUniqAt henv hsu (baseUniqAt_of_sortUniq_piInv henv hsu hpi f))

/-- The subject-indexed family repackaged as the global statement. -/
theorem baseUniq_of_baseUniqAt (h : ∀ e : VExpr, BaseUniqAt env U e) : BaseUniq env U :=
  fun hΓ h1 h2 => h _ hΓ h1 h2

/-- **`SortUniq + PiInv → BaseUniq`.**  No `VEnv.WF`, no `HasTypeStratified`, no
`PiInvStratApp`. -/
theorem baseUniq_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) : BaseUniq env U :=
  baseUniq_of_baseUniqAt (baseUniqAt_of_sortUniq_piInv henv hsu hpi)

/-- **`SortUniq + PiInv → UniqStrong`.**  Compare
`RetypeAdmissible.uniqStrong_of_piInvStratApp`, which takes `VEnv.WF env` and goes through
`HasTypeStratified`. -/
theorem uniqStrong_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) : UniqStrong env U :=
  uniqStrong_of_baseUniq henv hsu (baseUniq_of_sortUniq_piInv henv hsu hpi)

/-! ## The prize -/

/-- **`SortUniq + PiInv → retypes`.**

`RetypeAdmissible.retypes_of_piInvStratApp` proves the same conclusion from `VEnv.WF env` and
`PiInvStratApp`.  This route needs neither: `Ordered env` (which `IsDefEq.strong` already
carries) plus the corner's two named halves. -/
theorem retypes_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) {Γ : List VExpr} {e₁ e₂ A : VExpr}
    (H : env.IsDefEqStrong U Γ e₁ e₂ A) (hΓ : CtxStrong env U Γ) :
    Retypes env U Γ e₁ e₂ :=
  retypes_of_baseUniq henv (baseUniq_of_sortUniq_piInv henv hsu hpi) H hΓ

/-- **The delta, made machine-visible rather than asserted.**

The *implication* `SortUniq + PiInv → retypes` was already reachable before this file, by
composing `Injectivity.piInvStratApp_of` with `RetypeAdmissible.retypes_of_piInvStratApp`.
Here is that composite, written out.  Compare its hypothesis list with
`retypes_of_sortUniq_piInv`'s: the difference is **`VEnv.WF env` versus `Ordered env`**, and
(not visible in the type) a proof that never mentions `HasTypeStratified`, `uniqAux`, or an
induction over `IsDefEqStrong`.

So this file's contribution is *not* a new implication between named statements.  It is a
weaker hypothesis and a structurally different proof: a recursion on `VExpr`. -/
theorem retypes_of_sortUniq_piInv_via_strat (henv : VEnv.WF env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) {Γ : List VExpr} {e₁ e₂ A : VExpr}
    (H : env.IsDefEqStrong U Γ e₁ e₂ A) (hΓ : CtxStrong env U Γ) :
    Retypes env U Γ e₁ e₂ :=
  retypes_of_piInvStratApp henv (piInvStratApp_of henv hsu hpi) H hΓ

/-- The `hasType'` `retype` case, from the same two hypotheses. -/
theorem retype_of_conv_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) {Γ : List VExpr} {e₁ e₂ A B : VExpr} (hΓ : CtxStrong env U Γ)
    (h : env.IsDefEqStrong U Γ e₁ e₂ A) (h1B : env.HasTypeStrong U Γ e₁ B true) :
    env.HasTypeStrong U Γ e₂ B true :=
  (retypes_of_sortUniq_piInv henv hsu hpi h hΓ (B := B) (.inl h1B)).hasType'.2

/-- The four computation-rule residuals, from the same two hypotheses. -/
theorem betaRetype_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) : BetaRetype env U :=
  betaRetype_of_baseUniq henv (baseUniq_of_sortUniq_piInv henv hsu hpi)

theorem etaRetype_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) : EtaRetype env U :=
  etaRetype_of_baseUniq henv (baseUniq_of_sortUniq_piInv henv hsu hpi)

theorem proofRetype_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) : ProofRetype env U :=
  proofRetype_of_baseUniq henv (baseUniq_of_sortUniq_piInv henv hsu hpi)

theorem extraRetype_of_sortUniq_piInv (henv : Ordered env) (hsu : env.SortUniq U)
    (hpi : PiInv env U) : ExtraRetype env U :=
  extraRetype_of_baseUniq henv (baseUniq_of_sortUniq_piInv henv hsu hpi)

/-! ## Non-vacuity, and the negative control for the flag

The whole reduction turns on the recursive calls taking `UniqStrongAt` (flag `true`) at the
subterm, not `BaseUniqAt` (flag `false`).  That distinction is the *only* thing that puts
`SortUniq` in the result: `uniqStrongAt_of_baseUniqAt` is this file's sole consumer of
`SortUniq`, so the neighbouring reading — *"the recursion can take `BaseUniqAt` at the
subterm"* — would deliver `PiInv → retypes` with **no `SortUniq` at all**.  The two readings
differ in one `Bool`: same arity, same shape, same head.  It is rejected below, at the very
witness `ProofRetypeHeads.baseUniqApp_nonvacuous` already uses. -/

/-- **The negative control.**  In `baseUniqApp_nonvacuous`'s witness the second `.app`
derivation's function premise is `HasTypeStrong [prhPi1] (.bvar 0) prhPi2 true`, reached
through `HasTypeStrong.defeq` — and `prhPi2` is **not** a base type of `.bvar 0` there, since
`Lookup` pins the only one to `prhPi1`.  So the subterm premise genuinely lives at flag
`true`. -/
theorem app_fn_premise_is_not_base (henv : Ordered env) :
    env.HasTypeStrong U [prhPi1] (.bvar 0) prhPi2 true ∧
      ¬ env.HasTypeStrong U [prhPi1] (.bvar 0) prhPi2 false := by
  have h12 := prhPi12 (env := env) (U := U)
  have hw : (VLevel.imax (.succ (.succ .zero)) (.succ (.imax .zero .zero))).WF U :=
    ⟨trivial, trivial, trivial⟩
  have h12Γ := h12.weak0 (Γ := [prhPi1]) henv
  refine ⟨.defeq hw h12Γ h12Γ.hasType.1.hasType'.1 h12Γ.hasType.2.hasType'.1
    (.base (.bvar .zero hw h12Γ.hasType.1.hasType'.1)), ?_⟩
  intro h
  cases h with
  | bvar l _ _ =>
    have he : prhPi2 = prhPi1 := Lookup.uniq l (Lookup.zero (ty := prhPi1) (Γ := []))
    simp only [prhPi1, prhPi2] at he
    injection he with _ he2
    injection he2 with he3
    exact VLevel.noConfusion he3

/-- **The neighbouring reading, rejected.**  If the `true` flag on a subterm premise could be
dropped, `uniqStrongAt_of_baseUniqAt` — and with it `SortUniq` — would drop out of the whole
development. -/
theorem base_flag_not_droppable (henv : Ordered env) :
    ¬ ∀ {Γ : List VExpr} {e T : VExpr},
        env.HasTypeStrong U Γ e T true → env.HasTypeStrong U Γ e T false := by
  intro H
  have ⟨h1, h2⟩ := app_fn_premise_is_not_base (env := env) (U := U) henv
  exact h2 (H h1)

/-- **The `.app` branch of the recursion fires non-degenerately.**  Over every ordered
environment, at an application whose two base types are *syntactically different*, so the
conclusion is neither `refl` nor the input re-indexed at its own type.  The recursive call
inside is at the function `.bvar 0`, which lands in the free `.bvar` case — i.e. the descent
happens.

`SortUniq` and `PiInv` are carried, not discharged: this fires the branch, it is not evidence
that the two hypotheses are jointly satisfiable.  Per `ORCHESTRATOR.md` rule 4. -/
theorem baseUniqAt_app_fires (henv : Ordered env) (hsu : env.SortUniq U) (hpi : PiInv env U) :
    ∃ (Γ : List VExpr) (f a A B : VExpr), A ≠ B ∧ CtxStrong env U Γ ∧
      env.HasTypeStrong U Γ (.app f a) A false ∧
      env.HasTypeStrong U Γ (.app f a) B false ∧
      ∃ u, env.IsDefEqStrong U Γ A B (.sort u) := by
  obtain ⟨Γ, f, a, A, B, hne, hΓ, h1, h2⟩ := baseUniqApp_nonvacuous (env := env) (U := U) henv
  exact ⟨Γ, f, a, A, B, hne, hΓ, h1, h2,
    baseUniqAt_of_sortUniq_piInv henv hsu hpi (.app f a) hΓ h1 h2⟩

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.uniqStrongAt_of_baseUniqAt
#print axioms Lean4Lean.VEnv.baseUniqAt_bvar
#print axioms Lean4Lean.VEnv.baseUniqAt_const
#print axioms Lean4Lean.VEnv.baseUniqAt_sort
#print axioms Lean4Lean.VEnv.baseUniqAt_forallE
#print axioms Lean4Lean.VEnv.baseUniqAt_lam
#print axioms Lean4Lean.VEnv.baseUniqAt_app
#print axioms Lean4Lean.VEnv.baseUniqAt_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.baseUniq_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.uniqStrong_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.retypes_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.retypes_of_sortUniq_piInv_via_strat
#print axioms Lean4Lean.VEnv.retype_of_conv_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.betaRetype_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.etaRetype_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.proofRetype_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.extraRetype_of_sortUniq_piInv
#print axioms Lean4Lean.VEnv.app_fn_premise_is_not_base
#print axioms Lean4Lean.VEnv.base_flag_not_droppable
#print axioms Lean4Lean.VEnv.baseUniqAt_app_fires
end Audit
