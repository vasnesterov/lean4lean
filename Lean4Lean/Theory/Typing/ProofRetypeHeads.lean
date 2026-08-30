import Lean4Lean.Theory.Typing.RetypeAdmissible
import Lean4Lean.Theory.Typing.SortUniq

/-!
# `ProofRetype`, and why it is not a residual of its own

`Theory/Typing/RetypeAdmissible.lean` proves `IsDefEqStrong.retypes` from four hypotheses, one
per computation rule (`BetaRetype`, `EtaRetype`, `ProofRetype`, `ExtraRetype`), and singles out
`ProofRetype` as the one to attack: *"unique typing at an arbitrary proof, which is not
normalisation content at all."*

**Both halves of that reading are wrong, and this file machine-checks the corrections.**

## 1. The four residuals are one statement, and the induction is unnecessary

`retypeAt_of_baseUniq` re-indexes *any* conversion at *any* base type of either endpoint, from
one hypothesis:

```lean
def BaseUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ e A B}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A false → env.HasTypeStrong U Γ e B false →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)
```

Nothing in its proof mentions a rule: the rule's premises are used only to build the rule's own
conclusion.  So `proofRetype_of_baseUniq`, `betaRetype_of_baseUniq`, `etaRetype_of_baseUniq` and
`extraRetype_of_baseUniq` are the *same* three-line proof four times, and
`retypes_of_baseUniq` reproves `IsDefEqStrong.retypes` **with no induction over
`IsDefEqStrong` at all**.  `ProofRetype` is therefore not a distinct obligation; it is one
instantiation of `BaseUniq`.

## 2. The `defeq` chain is not an obstruction — it is walked, not composed

`RetypeAdmissible.lean` records that plain Π-injectivity cannot discharge `BetaRetype` because
*"the two Π-types are related through a chain of `HasTypeStrong.defeq` wrappers, and composing
those into a single `IsDefEqU` is composition-at-different-types, i.e. `uniq`."*  The chain
does not have to be composed.  `HasTypeStrong.peelDown` walks it one `defeqDF` at a time,
transporting the conversion the rule already has down to a *base* type, and it takes **no
hypothesis whatever** — no `Ordered`, no `CtxStrong`, no `SortUniq`.  Composition is needed
only when the chain is wanted as an *equation* (`HasTypeStrong.peelEq`), and that is the one
place a level is compared with a level.

## 3. The residual is three head shapes; `bvar`, `const` and `sort` are free

`baseUniq_of` discharges `.bvar` (by `Lookup.uniq`), `.const` (the environment is a function)
and `.sort` (two base typings of `.sort l` are at `.sort (.succ l')` and `.sort (.succ l'')`
with `l ≈ l'` and `l ≈ l''`) with no hypothesis at all.  What remains:

| head | discharged by | needs Π-injectivity? |
|---|---|---|
| `.forallE` | `SortUniq` alone (`baseUniqForallE_of_sortUniq`) | no |
| `.lam` | unique typing at the **body**, a proper subterm (`baseUniqLam_of_uniqStrong`) | no |
| `.app` | unique typing at the **function**, plus `PiInv` (`baseUniqApp_of`) | **yes** |

So the term at which the base type is taken is unrestricted, and in particular it ranges over
applications.  "Unique typing at an arbitrary proof" *contains* Π-injectivity at every proof
that happens to be an application, and it contains `SortUniq` at every proof whose type is
reached through a Π-formation.  It is not new content, and it is not the cheap one.

## 4. How weak is `BaseUniq`?  Exactly `UniqStrong`, modulo `SortUniq`

* `baseUniq_of_uniqStrong` — `UniqStrong → BaseUniq`, one line.
* `uniqStrong_of_baseUniq` — `BaseUniq + SortUniq → UniqStrong`.

So `handoff-injectivity.md` §4B.5's open question — *are the four residuals strictly weaker
than the corner?* — is answered in the negative up to `SortUniq`: the conjunction of the four
is implied by `BaseUniq`, and `BaseUniq` together with `SortUniq` gives back full unique typing
over `HasTypeStrong`.

## Non-vacuity, and the negative control

* `proofRetype_fires` runs `ProofRetype` over **every** ordered environment at an instance with
  the two endpoints syntactically different **and** the re-indexed type `X` syntactically
  different from the proposition `p` the `proofIrrel` rule fired at, so the conclusion is
  neither reflexivity nor the rule's own conclusion.  It goes through the free `bvar` case.
* `baseUniqApp_nonvacuous` exhibits, over every ordered environment, an **application with two
  syntactically different base types** — so the `.app` residual is a real obligation and not
  `rfl`.  `base_types_not_syntactically_unique` reads it as a rejection: the neighbouring
  strengthening "base types are syntactically unique", which would collapse `BaseUniq` to
  nothing, is **false**, at a witness that differs from the free cases in no arity or shape.
* Collapse test (`ORCHESTRATOR.md` rule 5): `BaseUniqApp`, `BaseUniqLam` and `BaseUniqForallE`
  each fire only at their own head, and `proofRetype_fires`' witness is at a `.bvar`, which
  none of the three admits.  So `baseUniq_of` is a reduction and not a restatement.

## What is *not* claimed

Every implication above is an **upper** bound: `BaseUniq` is *discharged by* those hypotheses.
Nothing here shows a residual *requires* Π-injectivity, and no refutation of `ProofRetype` or
of `BaseUniq` is offered.  A refutation would need an `Ordered` environment in which some term
has two base types that are not convertible; `Ordered` type-checks every `defeqs` entry, so
such an environment exists only if Π-injectivity fails in it, and showing *that* needs an
underivability proof, which this tree still has no instrument for.  Per `ORCHESTRATOR.md`
rule 4: *"no witness" is not evidence of truth.*

## Axioms

Every declaration is checked by the `#print axioms` block at the end; none mentions `sorryAx`.
-/
namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Peel the `defeq` wrappers off a `HasTypeStrong` derivation **downwards**. -/
theorem HasTypeStrong.peelDown :
    ∀ {Γ : List VExpr} {e B : VExpr} {b : Bool}, env.HasTypeStrong U Γ e B b →
      ∃ B₀, env.HasTypeStrong U Γ e B₀ false ∧
        ∀ {e₂ : VExpr}, env.IsDefEqStrong U Γ e e₂ B → env.IsDefEqStrong U Γ e e₂ B₀ := by
  intro Γ e B b H
  induction H with
  | bvar h1 h2 h3 _ => exact ⟨_, .bvar h1 h2 h3, id⟩
  | sort' h1 h2 h3 => exact ⟨_, .sort' h1 h2 h3, id⟩
  | const h1 h2 h3 h4 h5 h6 _ _ => exact ⟨_, .const h1 h2 h3 h4 h5 h6, id⟩
  | app h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ => exact ⟨_, .app h1 h2 h3 h4 h5 h6 h7 h8, id⟩
  | lam h1 h2 h3 h4 h5 h6 _ _ _ _ => exact ⟨_, .lam h1 h2 h3 h4 h5 h6, id⟩
  | forallE h1 h2 h3 h4 _ _ => exact ⟨_, .forallE h1 h2 h3 h4, id⟩
  | base h => exact ⟨_, h, id⟩
  | defeq h1 h2 _ _ _ _ _ ih5 =>
    obtain ⟨B₀, hb, t⟩ := ih5
    exact ⟨B₀, hb, fun hd => t (.defeqDF h1 h2.symm hd)⟩

/-- **Base-type uniqueness**: any two *base* (non-`defeq`) typings of the same term are at
convertible types. -/
def BaseUniq (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A false → env.HasTypeStrong U Γ e B false →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)

def BaseUniqApp (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {f a A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ (.app f a) A false → env.HasTypeStrong U Γ (.app f a) B false →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)

def BaseUniqLam (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {D e A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ (.lam D e) A false → env.HasTypeStrong U Γ (.lam D e) B false →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)

def BaseUniqForallE (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {D e A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ (.forallE D e) A false → env.HasTypeStrong U Γ (.forallE D e) B false →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)

/-- **Three of six head shapes are free.** -/
theorem baseUniq_of (happ : BaseUniqApp env U) (hlam : BaseUniqLam env U)
    (hfa : BaseUniqForallE env U) : BaseUniq env U := by
  intro Γ e A B hΓ h1 h2
  cases h1 with
  | bvar l1 u1 t1 =>
    cases h2 with
    | bvar l2 u2 t2 => cases l1.uniq l2; exact ⟨_, t1.refl⟩
  | sort' a1 a2 a3 =>
    cases h2 with
    | sort' b1 b2 b3 =>
      exact ⟨_, .sortDF (l := .succ _) (l' := .succ _) a2 b2
        (VLevel.succ_congr (a3.symm.trans b3))⟩
  | const c1 c2 c3 c4 c5 c6 =>
    cases h2 with
    | const d1 d2 d3 d4 d5 d6 => cases c1.symm.trans d1; exact ⟨_, c6.refl⟩
  | app a1 a2 a3 a4 a5 a6 a7 a8 => exact happ hΓ (.app a1 a2 a3 a4 a5 a6 a7 a8) h2
  | lam a1 a2 a3 a4 a5 a6 => exact hlam hΓ (.lam a1 a2 a3 a4 a5 a6) h2
  | forallE a1 a2 a3 a4 => exact hfa hΓ (.forallE a1 a2 a3 a4) h2

/-- **The `.forallE` residual is exactly `SortUniq`** — the corner's *other* half, and no
Π-injectivity anywhere. -/
theorem baseUniqForallE_of_sortUniq (hsu : env.SortUniq U) : BaseUniqForallE env U := by
  intro Γ D e A B hΓ h1 h2
  cases h1 with
  | forallE a1 a2 a3 a4 =>
    cases h2 with
    | forallE b1 b2 b3 b4 =>
      have hu := hsu hΓ.defeq a1 b1 a3.hasType b3.hasType
      have hv := hsu (Γ := D::Γ) ⟨hΓ.defeq, _, a3.hasType⟩ a2 b2 a4.hasType b4.hasType
      exact ⟨_, .sortDF (l := .imax _ _) (l' := .imax _ _) ⟨a1, a2⟩ ⟨b1, b2⟩
        (VLevel.imax_congr hu hv)⟩

/-- **The `.lam` residual is a plain recursion**: unique typing at the *body*, a proper
subterm, and nothing else.  No Π-injectivity and no `SortUniq`. -/
theorem baseUniqLam_of_uniqStrong (henv : Ordered env) (huniq : UniqStrong env U) :
    BaseUniqLam env U := by
  intro Γ D e A B hΓ h1 h2
  cases h1 with
  | lam a1 a2 a3 a4 a5 a6 =>
    cases h2 with
    | lam b1 b2 b3 b4 b5 b6 =>
      have hΓ' : CtxStrong env U (D::Γ) := ⟨hΓ, _, a3.refl⟩
      obtain ⟨w, hw⟩ := huniq hΓ' a5 b5
      exact ⟨_, .forallEDF a1 (hw.defeq.sort_r henv hΓ'.defeq) a3.refl hw hw⟩

/-- **The `.app` residual is where Π-injectivity enters, and the only place it does.**
Unique typing at the function head gives the two Π-types a common conversion; `PiInv` is
what turns that into a conversion of the two *codomains*, which is what the two base types
of the application are instances of. -/
theorem baseUniqApp_of (henv : Ordered env) (huniq : UniqStrong env U) (hpi : PiInv env U) :
    BaseUniqApp env U := by
  intro Γ f a A B hΓ h1 h2
  cases h1 with
  | app a1 a2 a3 a4 a5 a6 a7 a8 =>
    cases h2 with
    | app b1 b2 b3 b4 b5 b6 b7 b8 =>
      obtain ⟨w, hw⟩ := huniq hΓ a6 b6
      obtain ⟨-, u, hB⟩ := hpi hΓ.defeq ⟨_, hw.defeq⟩
      exact ⟨u, (IsDefEq.instDF henv hΓ.defeq hB a7.refl.defeq).strong henv hΓ.defeq⟩

/-- The upper bound: `BaseUniq` is no stronger than unique typing. -/
theorem baseUniq_of_uniqStrong (h : UniqStrong env U) : BaseUniq env U :=
  fun hΓ h1 h2 => h hΓ (.base h1) (.base h2)

/-- **Re-indexing at a base type, from `BaseUniq` alone.**

This is the whole of the four residuals of `IsDefEqStrong.retypes`, in one statement and with
**no induction**: whatever conversion a rule concludes, it can be re-indexed at any base type
of either endpoint.  The `defeq` chain between the rule's own type index and that base type is
never *composed* — `peelDown` walks it one `defeqDF` at a time, which is why nothing here
needs `SortUniq` or a conversion at two different sorts. -/
theorem retypeAt_of_baseUniq (henv : Ordered env) (hbu : BaseUniq env U)
    {Γ : List VExpr} {e₁ e₂ A X : VExpr} (hΓ : CtxStrong env U Γ)
    (canon : env.IsDefEqStrong U Γ e₁ e₂ A)
    (hor : env.HasTypeStrong U Γ e₁ X false ∨ env.HasTypeStrong U Γ e₂ X false) :
    env.IsDefEqStrong U Γ e₁ e₂ X := by
  cases hor with
  | inl hb =>
    obtain ⟨P₀, hP₀, t⟩ := canon.hasType'.1.peelDown
    obtain ⟨u, hc⟩ := hbu hΓ hP₀ hb
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc (t canon)
  | inr hb =>
    obtain ⟨P₀, hP₀, t⟩ := canon.hasType'.2.peelDown
    obtain ⟨u, hc⟩ := hbu hΓ hP₀ hb
    exact (IsDefEqStrong.defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc (t canon.symm)).symm

/-- **`BaseUniq` discharges `ProofRetype`.** -/
theorem proofRetype_of_baseUniq (henv : Ordered env) (hbu : BaseUniq env U) :
    ProofRetype env U := fun hΓ h1 h2 h3 hor =>
  retypeAt_of_baseUniq henv hbu hΓ (.proofIrrel h1 h2 h3) hor

/-- The same argument, verbatim, for the other three residuals. -/
theorem betaRetype_of_baseUniq (henv : Ordered env) (hbu : BaseUniq env U) :
    BetaRetype env U := fun hΓ h1 h2 h3 h4 h5 h6 h7 h8 hor =>
  retypeAt_of_baseUniq henv hbu hΓ (.beta h1 h2 h3 h4 h5 h6 h7 h8) hor

theorem etaRetype_of_baseUniq (henv : Ordered env) (hbu : BaseUniq env U) :
    EtaRetype env U := fun hΓ h1 h2 h3 h4 h5 h6 h7 h8 hor =>
  retypeAt_of_baseUniq henv hbu hΓ (.eta h1 h2 h3 h4 h5 h6 h7 h8) hor

theorem extraRetype_of_baseUniq (henv : Ordered env) (hbu : BaseUniq env U) :
    ExtraRetype env U := fun hΓ h1 h2 h3 h4 h5 h6 h7 h8 h9 hor =>
  retypeAt_of_baseUniq henv hbu hΓ (.extra h1 h2 h3 h4 h5 h6 h7 h8 h9) hor

/-- **`retypes` itself, from `BaseUniq`, with no induction over `IsDefEqStrong` at all.** -/
theorem retypes_of_baseUniq (henv : Ordered env) (hbu : BaseUniq env U)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : env.IsDefEqStrong U Γ e₁ e₂ A)
    (hΓ : CtxStrong env U Γ) : Retypes env U Γ e₁ e₂ := by
  intro B hor
  cases hor with
  | inl h => exact h.peelTo fun hb => retypeAt_of_baseUniq henv hbu hΓ H (.inl hb)
  | inr h =>
    exact (h.peelTo fun hb => (retypeAt_of_baseUniq henv hbu hΓ H (.inr hb)).symm).symm

/-! ## `BaseUniq` is unique typing, modulo `SortUniq`

`baseUniq_of_uniqStrong` is one half.  The other half needs exactly one extra ingredient, and
it is `SortUniq`: peeling a `defeq` chain *as an equation* (rather than transporting a
conversion along it, which `peelDown` does for free) has to compose two conversions indexed at
two different sorts, and that is the only place a level is ever compared with a level. -/

theorem IsDefEqStrong.atSort {Γ : List VExpr} {X Y : VExpr} {u v : VLevel}
    (h : env.IsDefEqStrong U Γ X Y (.sort u)) (hu : u.WF U) (hv : v.WF U) (e : u ≈ v) :
    env.IsDefEqStrong U Γ X Y (.sort v) :=
  .defeqDF (u := .succ u) (by exact hu) (.sortDF hu hv e) h

/-- Peel the `defeq` wrappers off, keeping the resulting **equation** between the base type and
the derivation's type.  Contrast `peelDown`, which keeps no equation and needs no hypothesis. -/
theorem HasTypeStrong.peelEq (henv : Ordered env) (hsu : env.SortUniq U) :
    ∀ {Γ : List VExpr} {e B : VExpr} {b : Bool}, CtxStrong env U Γ →
      env.HasTypeStrong U Γ e B b →
      ∃ B₀, env.HasTypeStrong U Γ e B₀ false ∧
        ∃ u, env.IsDefEqStrong U Γ B₀ B (.sort u) := by
  intro Γ e B b hΓ H
  induction H with
  | bvar h1 h2 h3 _ => exact ⟨_, .bvar h1 h2 h3, _, h3.refl⟩
  | sort' h1 h2 h3 => exact ⟨_, .sort' h1 h2 h3, _, .sortDF (by exact h2) (by exact h2) rfl⟩
  | const h1 h2 h3 h4 h5 h6 _ _ => exact ⟨_, .const h1 h2 h3 h4 h5 h6, _, h6.refl⟩
  | app h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ =>
    exact ⟨_, .app h1 h2 h3 h4 h5 h6 h7 h8, _, h8.refl⟩
  | lam h1 h2 h3 h4 h5 h6 _ _ _ _ => exact ⟨_, .lam h1 h2 h3 h4 h5 h6, _, h6.refl⟩
  | forallE h1 h2 h3 h4 _ _ =>
    exact ⟨_, .forallE h1 h2 h3 h4, _,
      .sortDF (by exact ⟨h1, h2⟩) (by exact ⟨h1, h2⟩) rfl⟩
  | base h ih => exact ih hΓ
  | defeq h1 h2 h3 h4 h5 _ _ ih5 =>
    obtain ⟨B₀, hb, u', e1⟩ := ih5 hΓ
    have hu' := e1.defeq.sort_r henv hΓ.defeq
    have := hsu hΓ.defeq hu' h1 e1.hasType.2.defeq h3.hasType
    exact ⟨B₀, hb, _, (e1.atSort hu' h1 this).trans h2⟩

/-- **The converse of `baseUniq_of_uniqStrong`, modulo `SortUniq`.** -/
theorem uniqStrong_of_baseUniq (henv : Ordered env) (hsu : env.SortUniq U)
    (hbu : BaseUniq env U) : UniqStrong env U := by
  intro Γ e A B hΓ h1 h2
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

/-! ## The headline reduction -/

/-- **`ProofRetype` reduces to three head shapes.**  `bvar`, `const` and `sort` are free. -/
theorem proofRetype_of_heads (henv : Ordered env)
    (happ : BaseUniqApp env U) (hlam : BaseUniqLam env U) (hfa : BaseUniqForallE env U) :
    ProofRetype env U :=
  proofRetype_of_baseUniq henv (baseUniq_of happ hlam hfa)

/-- **All four residuals of `IsDefEqStrong.retypes`, from the same three head shapes.** -/
theorem retypes_of_heads (henv : Ordered env)
    (happ : BaseUniqApp env U) (hlam : BaseUniqLam env U) (hfa : BaseUniqForallE env U)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : env.IsDefEqStrong U Γ e₁ e₂ A)
    (hΓ : CtxStrong env U Γ) : Retypes env U Γ e₁ e₂ :=
  retypes_of_baseUniq henv (baseUniq_of happ hlam hfa) H hΓ

/-! ## Non-vacuity, and a negative control -/

/-- `∀ X : Prop, X` — a closed proposition available over every environment. -/
def prhQ : VExpr := .forallE (.sort .zero) (.bvar 0)
/-- `∀ X : Sort (imax 0 0), prhQ` -/
def prhA : VExpr := .forallE (.sort (.imax .zero .zero)) prhQ
/-- `∀ X : Prop, prhQ` — convertible to `prhA`, and not syntactically equal to it. -/
def prhB : VExpr := .forallE (.sort .zero) prhQ

theorem prhB_ne_prhA : prhB ≠ prhA := by
  intro h
  rw [prhA, prhB] at h
  injection h with h1 _
  injection h1 with h2
  exact VLevel.noConfusion h2

theorem prhQ_type : env.IsDefEqStrong U [] prhQ prhQ (.sort (.imax (.succ .zero) .zero)) :=
  .forallEDF trivial trivial (.sortDF trivial trivial rfl)
    (.bvar (u := .succ .zero) .zero trivial (.sortDF trivial trivial rfl))
    (.bvar (u := .succ .zero) .zero trivial (.sortDF trivial trivial rfl))

theorem prhAB (henv : Ordered env) :
    env.IsDefEqStrong U [] prhA prhB
      (.sort (.imax (.succ (.imax .zero .zero)) (.imax (.succ .zero) .zero))) :=
  .forallEDF ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
    (.sortDF ⟨trivial, trivial⟩ trivial VLevel.imax_zero)
    (prhQ_type.weak0 henv) (prhQ_type.weak0 henv)

theorem prhB_type (henv : Ordered env) :
    env.IsDefEqStrong U [] prhB prhB
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) .zero))) :=
  .forallEDF trivial ⟨trivial, trivial⟩ (.sortDF trivial trivial rfl)
    (prhQ_type.weak0 henv) (prhQ_type.weak0 henv)

/-- **`ProofRetype` fires non-degenerately, over every ordered environment.**  The two
endpoints are syntactically different terms, and the type `X` the conclusion is re-indexed at
is syntactically different from the proposition `p` the `proofIrrel` rule fired at — so the
instance is neither reflexivity nor the rule's own conclusion.  It goes through the free
(`bvar`) case of `baseUniq_of`. -/
theorem proofRetype_fires (henv : Ordered env) (hpr : ProofRetype env U) :
    ∃ (Γ : List VExpr) (p h h' X : VExpr), h ≠ h' ∧ p ≠ X ∧
      CtxStrong env U Γ ∧ env.HasTypeStrong U Γ h X false ∧
      env.IsDefEqStrong U Γ h h' X := by
  have hAB := prhAB (env := env) (U := U) henv
  have hA := hAB.hasType.1
  have hB := prhB_type (env := env) (U := U) henv
  have hwA : (VLevel.imax (.succ (.imax .zero .zero)) (.imax (.succ .zero) .zero)).WF U :=
    ⟨⟨trivial, trivial⟩, trivial, trivial⟩
  have hwB : (VLevel.imax (.succ .zero) (.imax (.succ .zero) .zero)).WF U :=
    ⟨trivial, trivial, trivial⟩
  have hΓ : CtxStrong env U [prhB, prhA] := ⟨⟨trivial, _, hA⟩, _, hB.weak0 henv⟩
  have hAΓ := hA.weak0 (Γ := [prhB, prhA]) henv
  have hBΓ := hB.weak0 (Γ := [prhB, prhA]) henv
  have hABΓ := hAB.weak0 (Γ := [prhB, prhA]) henv
  have hprop : env.IsDefEqStrong U [prhB, prhA] prhB prhB (.sort .zero) :=
    .defeqDF (u := .succ _) (by exact hwB)
      (.sortDF hwB trivial (VLevel.imax_eq_zero.2 VLevel.imax_zero)) hBΓ
  have hbase : env.HasTypeStrong U [prhB, prhA] (.bvar 1) prhA false :=
    .bvar (.succ .zero) hwA hAΓ.hasType'.1
  have hb1 : env.IsDefEqStrong U [prhB, prhA] (.bvar 1) (.bvar 1) prhB :=
    .defeqDF hwA hABΓ (.bvar (.succ .zero) hwA hAΓ)
  have hb0 : env.IsDefEqStrong U [prhB, prhA] (.bvar 0) (.bvar 0) prhB :=
    .bvar .zero hwB hBΓ
  exact ⟨_, _, _, _, _, by simp,
    prhB_ne_prhA, hΓ, hbase,
    hpr hΓ hprop hb1 hb0 (.inl hbase)⟩

/-! ### The negative control: the free cases do **not** extend to syntactic uniqueness -/

/-- `(X : Type) → Sort (imax 0 0)` -/
def prhPi1 : VExpr := .forallE (.sort (.succ .zero)) (.sort (.imax .zero .zero))
/-- `(X : Type) → Prop` — convertible to `prhPi1`, not equal to it. -/
def prhPi2 : VExpr := .forallE (.sort (.succ .zero)) (.sort .zero)

theorem prhPi12 :
    env.IsDefEqStrong U [] prhPi1 prhPi2
      (.sort (.imax (.succ (.succ .zero)) (.succ (.imax .zero .zero)))) :=
  .forallEDF trivial ⟨trivial, trivial⟩ (.sortDF trivial trivial rfl)
    (.sortDF ⟨trivial, trivial⟩ trivial VLevel.imax_zero)
    (.sortDF ⟨trivial, trivial⟩ trivial VLevel.imax_zero)

/-- **The `.app` residual is not vacuous, and it is not `rfl`.**  Over *every* ordered
environment there is an application with **two syntactically different** base types.

This is the rejection-style negative control for `baseUniq_of`: the three head shapes it
discharges are all discharged with the two types *equal* or level-equivalent, and the
neighbouring statement "base types are syntactically unique" — which would make `BaseUniq`
trivial — is **false**, at a witness no arity or shape check distinguishes from the free
cases. -/
theorem baseUniqApp_nonvacuous (henv : Ordered env) :
    ∃ (Γ : List VExpr) (f a A B : VExpr), A ≠ B ∧ CtxStrong env U Γ ∧
      env.HasTypeStrong U Γ (.app f a) A false ∧
      env.HasTypeStrong U Γ (.app f a) B false := by
  have h12 := prhPi12 (env := env) (U := U)
  have hw : (VLevel.imax (.succ (.succ .zero)) (.succ (.imax .zero .zero))).WF U :=
    ⟨trivial, trivial, trivial⟩
  have hΓ : CtxStrong env U [prhPi1] := ⟨trivial, _, h12.hasType.1⟩
  have h12Γ := h12.weak0 (Γ := [prhPi1]) henv
  have hdom : env.HasTypeStrong U [prhPi1] (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) true := .base (.sort' trivial trivial rfl)
  have hcod1 : env.HasTypeStrong U [.sort (.succ .zero), prhPi1]
      (.sort (.imax .zero .zero)) (.sort (.succ (.imax .zero .zero))) true :=
    .base (.sort' ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ rfl)
  have hcod2 : env.HasTypeStrong U [.sort (.succ .zero), prhPi1]
      (.sort .zero) (.sort (.succ .zero)) true := .base (.sort' trivial trivial rfl)
  have ha : env.HasTypeStrong U [prhPi1] (.sort .zero) (.sort (.succ .zero)) true :=
    .base (.sort' trivial trivial rfl)
  have hf1 : env.HasTypeStrong U [prhPi1] (.bvar 0) prhPi1 true :=
    .base (.bvar .zero hw h12Γ.hasType.1.hasType'.1)
  have hf2 : env.HasTypeStrong U [prhPi1] (.bvar 0) prhPi2 true :=
    .defeq hw h12Γ h12Γ.hasType.1.hasType'.1 h12Γ.hasType.2.hasType'.1 hf1
  refine ⟨[prhPi1], .bvar 0, .sort .zero, .sort (.imax .zero .zero), .sort .zero,
    (by intro h; injection h with h1; exact VLevel.noConfusion h1), hΓ, ?_, ?_⟩
  · exact .app (u := .succ (.succ .zero)) (v := .succ (.imax .zero .zero))
      trivial ⟨trivial, trivial⟩ hdom hcod1
      (.base (.forallE trivial ⟨trivial, trivial⟩ hdom hcod1)) hf1 ha
      (.base (.sort' ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ rfl))
  · exact .app (u := .succ (.succ .zero)) (v := .succ .zero) trivial trivial hdom hcod2
      (.base (.forallE trivial trivial hdom hcod2)) hf2 ha
      (.base (.sort' trivial trivial rfl))

/-- **The neighbouring strengthening is refuted**, at the witness above. -/
theorem base_types_not_syntactically_unique (henv : Ordered env) :
    ¬ ∀ {Γ : List VExpr} {e A B : VExpr}, CtxStrong env U Γ →
        env.HasTypeStrong U Γ e A false → env.HasTypeStrong U Γ e B false → A = B := by
  intro H
  obtain ⟨Γ, f, a, A, B, hne, hΓ, h1, h2⟩ := baseUniqApp_nonvacuous (env := env) (U := U) henv
  exact hne (H hΓ h1 h2)

end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.HasTypeStrong.peelDown
#print axioms Lean4Lean.VEnv.baseUniq_of
#print axioms Lean4Lean.VEnv.baseUniqForallE_of_sortUniq
#print axioms Lean4Lean.VEnv.baseUniqLam_of_uniqStrong
#print axioms Lean4Lean.VEnv.baseUniqApp_of
#print axioms Lean4Lean.VEnv.baseUniq_of_uniqStrong
#print axioms Lean4Lean.VEnv.HasTypeStrong.peelEq
#print axioms Lean4Lean.VEnv.uniqStrong_of_baseUniq
#print axioms Lean4Lean.VEnv.retypeAt_of_baseUniq
#print axioms Lean4Lean.VEnv.proofRetype_of_baseUniq
#print axioms Lean4Lean.VEnv.betaRetype_of_baseUniq
#print axioms Lean4Lean.VEnv.etaRetype_of_baseUniq
#print axioms Lean4Lean.VEnv.extraRetype_of_baseUniq
#print axioms Lean4Lean.VEnv.retypes_of_baseUniq
#print axioms Lean4Lean.VEnv.retypes_of_heads
#print axioms Lean4Lean.VEnv.proofRetype_of_heads
#print axioms Lean4Lean.VEnv.proofRetype_fires
#print axioms Lean4Lean.VEnv.baseUniqApp_nonvacuous
#print axioms Lean4Lean.VEnv.base_types_not_syntactically_unique
end Audit
