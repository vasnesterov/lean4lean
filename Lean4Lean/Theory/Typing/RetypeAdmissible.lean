import Lean4Lean.Theory.Typing.RetypeCase

/-!
# The `retype` enlargement, priced at the rule it is actually paid for

`docs/handoff-injectivity.md` §4A.4 left one open question:

> Is `HasTypeStrong.retype` provable without `PiInvStratApp`?  If it is, Route A is free.

**The question is answerable, and the answer is that `HasTypeStrong.retype` is not the
obligation.**  `Theory/Typing/RetypeCase.lean` states the `retype` case of
`IsDefEqStrong.hasType'` *without* the conversion premise, on the ground that its proof (from
unique typing) does not need it.  But the case **carries** that premise: `hasType'`'s `retype`
node is built from `IsDefEqStrong Γ e₁ e₂ A` together with `HasTypeStrong Γ e₁ B`, and the
first of those is exactly what a subject-directed induction can consume.  Dropping it left a
statement with nothing to induct on — three typings of two unrelated terms — and that is the
form which looked stuck.  (The conversion-free form implies this one, through `hasType'`; the
converse is not known, so it is at least as strong and plausibly strictly so.)

This file proves the obligation Route A actually has —

```lean
theorem IsDefEqStrong.retypes :
    env.IsDefEqStrong U Γ e₁ e₂ A → CtxStrong env U Γ →
    ∀ {B}, (env.HasTypeStrong U Γ e₁ B true ∨ env.HasTypeStrong U Γ e₂ B true) →
      env.IsDefEqStrong U Γ e₁ e₂ B
```

— by induction on the conversion, and it is **`sorry`-free and free of `PiInvStratApp`,
`VEnv.WF`, `SortUniq` and every member of the injectivity family**.  What it costs instead is
four hypotheses, one per rule, and they are exactly the rules the induction cannot close.

## What is free, and what is not

`IsDefEqStrong` has thirteen rules.  **Nine of them cost nothing**: `bvar`, `symm`, `trans`,
`sortDF`, `constDF`, `appDF`, `lamDF`, `forallEDF`, `defeqDF`.  The pattern is uniform and is
the point of the file: in a *congruence* rule the two sides have the same head, so a base
typing of the left side is rebuilt for the right side **at the very same type**, out of the
induction hypotheses for the sub-conversions.  No level is ever compared with another level,
which is why `SortUniq` never appears.  Concretely, in `appDF` the induction hypothesis at the
function turns `f : .forallE A₀ B₀` (whatever Π-type the *typing* derivation chose, not the one
the *conversion* was indexed at) into `f ≡ f' : .forallE A₀ B₀`, and likewise at the argument;
`IsDefEqStrong.instDF` then supplies the codomain congruence and the `appDF` rule re-fires at
`B₀.inst a`.  `lamDF` and `forallEDF` are the same move with `IsDefEqStrong.defeqDF_l` doing
the context conversion.

**The residual is exactly the four computation rules** — `beta`, `eta`, `proofIrrel`, `extra`
— i.e. precisely the rules whose two sides have *unrelated head shapes*, so that a base typing
of one side says nothing about the other.  Each residual below is stated with the whole
premise list of its own rule available, plus the peeled (`false`, i.e. non-`defeq`) base
typing of one of the two sides: that is the weakest form the induction ever needs.

## Consequences for the enlargement

* **Route A opens no new hole beyond these four** (subject to the merge noted below), and
  `HasTypeStrong.retype_of_conv` is the `hasType'` case in the shape
  `Theory/Typing/Enlarged.lean` states it.
* The four residuals are **no stronger than the corner**: `retypes_of_piInvStratApp` derives
  all four from `PiInvStratApp` (through `uniqAux`), so nothing here is a new obligation.
  Whether they are *strictly* weaker is open; they are certainly *localised*, which
  `HasTypeStrong.retype` was not.
* **Do not read them as free.**  Each asks for the type its own rule is indexed at to be
  related to an arbitrary *base* type of one endpoint — unique typing at that endpoint,
  restricted to one term shape.  For `beta` that is Π-injectivity at `.lam A e`, and plain
  `IsDefEqU.forallE_inv` does **not** suffice on its own: the two Π-types are related through
  a chain of `HasTypeStrong.defeq` wrappers, and composing those into the single `IsDefEqU`
  that `forallE_inv` consumes is composition-at-different-types, i.e. `uniq` again.
  `ProofRetype` is the odd one out and the one worth attacking first: it is unique typing at
  an arbitrary **proof**, which is not normalisation content at all.
* The collapse test (`ORCHESTRATOR.md` rule 5) passes: no residual can be instantiated to give
  the target.  `BetaRetype` fires only when the left endpoint is a β-redex, `ProofRetype` only
  when the shared type is a proposition and both endpoints inhabit it, `ExtraRetype` only at an
  `env.defeqs` instance, `EtaRetype` only at an η-expansion.  None of those premises can be met
  by a general `IsDefEqStrong Γ e₁ e₂ A`, so the reduction is proper rather than a restatement.

## What transfers to the enlarged judgment, and the one thing that does not transfer for free

Everything above is about the judgment the tree has **today**, and it is machine-checked
there.  Under the in-place enlargement (`IsDefEqStrong` gains
`retype : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ : B → Γ ⊢ e₁ ≡ e₂ : B`) the picture is this, and the last
item is the caveat:

* `weakN`, `instN`, `instL`, `mono`, `defeq`, `hasType`, `isType'`, `forallE_inv'` each gain a
  `retype` case that is discharged by a premise's induction hypothesis — the rule is closed
  under substitution and weakening, and its type index comes from its second premise.
  `HasTypeStrong` gains **no** constructor, so `HasTypeStrong.refl` and
  `HasTypeStrong.peelTo` are untouched.  *(analysis, not checked here.)*
* **`retypes` and `hasType'` must then be proved by one simultaneous induction.**  This is
  forced by exactly one line: the `trans` case below reaches `e₂ : B` through
  `d1.hasType'.2`, where `d1` is *constructed* from an induction hypothesis and is not a
  sub-derivation, so in the enlarged setting `retypes` would need `hasType'` in full while
  `hasType'`'s new `retype` case needs `retypes` in full.  Merging is enough and costs
  nothing: state the conclusion as `IsDefEqStrong Γ e₁ e₂ B ∧ e₁ : B ∧ e₂ : B`, and the
  `trans` case reads `e₂ : B` off its own induction hypothesis instead.  The merged
  induction's new `retype` case is then discharged by the *first* premise's induction
  hypothesis alone.  *(analysis: the merge is not carried out here, because the enlarged
  judgment is not defined in this tree; what is checked is that the appeal to `hasType'`
  occurs in exactly one case and is removable in that way.)*

## Non-vacuity, and the negative control that is *not* available

`retypes_fires` runs the theorem at an instance with `e₁ ≠ e₂` **and** `A ≠ B` syntactically,
over **every** environment, using only the free (`sortDF`) case — so the conclusion is neither
reflexivity nor a re-derivation of the input.

A negative control of the *rejection* kind — a neighbouring statement shown false at a witness
— is **not available here, and the reason is itself the finding**: every neighbouring
weakening (for instance, replacing "`B` is a type of `e₁`" by "`B` is a type of `Γ`") is
refuted only by showing some `IsDefEqStrong Γ e₁ e₂ B` is *underivable*, and this tree has no
inversion principle that pins a term's types without exactly the content of `SortUniq`.
Recorded per `ORCHESTRATOR.md` rule 4: *"no witness" is not evidence of truth.*

## Axioms

Every declaration below is checked by the `#print axioms` block at the end of the file; none
mentions `sorryAx`.
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

/-- Peel the `defeq` wrappers off a `HasTypeStrong` derivation: a conversion at every *base*
type of `e` is a conversion at every type of `e`.  This is the inner induction that every case
of `IsDefEqStrong.retypes` uses, and it is where the `defeq` rule stops mattering. -/
theorem HasTypeStrong.peelTo :
    ∀ {Γ : List VExpr} {e B : VExpr} {b : Bool}, env.HasTypeStrong U Γ e B b →
    ∀ {e₂ : VExpr},
      (∀ {B'}, env.HasTypeStrong U Γ e B' false → env.IsDefEqStrong U Γ e e₂ B') →
      env.IsDefEqStrong U Γ e e₂ B := by
  intro Γ e B b H
  induction H with
  | bvar h1 h2 h3 _ => exact fun base => base (.bvar h1 h2 h3)
  | sort' h1 h2 h3 => exact fun base => base (.sort' h1 h2 h3)
  | const h1 h2 h3 h4 h5 h6 _ _ => exact fun base => base (.const h1 h2 h3 h4 h5 h6)
  | app h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ _ =>
    exact fun base => base (.app h1 h2 h3 h4 h5 h6 h7 h8)
  | lam h1 h2 h3 h4 h5 h6 _ _ _ _ => exact fun base => base (.lam h1 h2 h3 h4 h5 h6)
  | forallE h1 h2 h3 h4 _ _ => exact fun base => base (.forallE h1 h2 h3 h4)
  | base h => exact fun base => base h
  | defeq h1 h2 _ _ _ _ _ ih => exact fun base => .defeqDF h1 h2 (ih base)


def Retypes (env : VEnv) (U : Nat) (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  ∀ {B : VExpr}, (env.HasTypeStrong U Γ e₁ B true ∨ env.HasTypeStrong U Γ e₂ B true) →
    env.IsDefEqStrong U Γ e₁ e₂ B

def BetaRetype (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B e e' X : VExpr} {u v : VLevel},
    CtxStrong env U Γ → u.WF U → v.WF U →
    env.IsDefEqStrong U Γ A A (.sort u) →
    env.IsDefEqStrong U (A::Γ) B B (.sort v) →
    env.IsDefEqStrong U (A::Γ) e e B →
    env.IsDefEqStrong U Γ e' e' A →
    env.IsDefEqStrong U Γ (B.inst e') (B.inst e') (.sort v) →
    env.IsDefEqStrong U Γ (e.inst e') (e.inst e') (B.inst e') →
    (env.HasTypeStrong U Γ (.app (.lam A e) e') X false ∨
      env.HasTypeStrong U Γ (e.inst e') X false) →
    env.IsDefEqStrong U Γ (.app (.lam A e) e') (e.inst e') X

def EtaRetype (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {A B e X : VExpr} {u v : VLevel},
    CtxStrong env U Γ → u.WF U → v.WF U →
    env.IsDefEqStrong U Γ A A (.sort u) →
    env.IsDefEqStrong U (A::Γ) B B (.sort v) →
    env.IsDefEqStrong U (A.lift::A::Γ) (B.liftN 1 1) (B.liftN 1 1) (.sort v) →
    env.IsDefEqStrong U Γ e e (.forallE A B) →
    env.IsDefEqStrong U (A::Γ) e.lift e.lift (.forallE A.lift (B.liftN 1 1)) →
    env.IsDefEqStrong U (A::Γ) A.lift A.lift (.sort u) →
    (env.HasTypeStrong U Γ (.lam A (.app e.lift (.bvar 0))) X false ∨
      env.HasTypeStrong U Γ e X false) →
    env.IsDefEqStrong U Γ (.lam A (.app e.lift (.bvar 0))) e X

def ProofRetype (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {p h h' X : VExpr},
    CtxStrong env U Γ →
    env.IsDefEqStrong U Γ p p (.sort .zero) →
    env.IsDefEqStrong U Γ h h p →
    env.IsDefEqStrong U Γ h' h' p →
    (env.HasTypeStrong U Γ h X false ∨ env.HasTypeStrong U Γ h' X false) →
    env.IsDefEqStrong U Γ h h' X

def ExtraRetype (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {df : VDefEq} {ls : List VLevel} {X : VExpr} {u : VLevel},
    CtxStrong env U Γ → env.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
    u.WF U →
    env.IsDefEqStrong U [] (df.type.instL ls) (df.type.instL ls) (.sort u) →
    env.IsDefEqStrong U [] (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U [] (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) →
    env.IsDefEqStrong U Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) →
    (env.HasTypeStrong U Γ (df.lhs.instL ls) X false ∨
      env.HasTypeStrong U Γ (df.rhs.instL ls) X false) →
    env.IsDefEqStrong U Γ (df.lhs.instL ls) (df.rhs.instL ls) X

theorem IsDefEqStrong.retypes (henv : Ordered env)
    (hbeta : BetaRetype env U) (heta : EtaRetype env U)
    (hproof : ProofRetype env U) (hextra : ExtraRetype env U) :
    ∀ {Γ : List VExpr} {e₁ e₂ A : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ A →
      CtxStrong env U Γ → Retypes env U Γ e₁ e₂ := by
  intro Γ e₁ e₂ A H
  induction H with
  | bvar h1 h2 h3 ih => intro _ _ h; exact h.elim (·.refl) (·.refl)
  | symm _ ih => intro hΓ _ h; exact (ih hΓ h.symm).symm
  | trans _ _ ih1 ih2 =>
    intro hΓ _ h
    cases h with
    | inl h => have d1 := ih1 hΓ (.inl h); exact d1.trans (ih2 hΓ (.inl d1.hasType'.2))
    | inr h => have d2 := ih2 hΓ (.inr h); exact (ih1 hΓ (.inr d2.hasType'.1)).trans d2
  | sortDF h1 h2 h3 =>
    intro _ _ h
    cases h with
    | inl h =>
      refine h.peelTo fun hb => ?_
      let .sort' b1 b2 b3 := hb
      refine .defeqDF (u := .succ (.succ _)) h1 ?_ (.sortDF h1 h2 h3)
      exact .sortDF (l := .succ _) (l' := .succ _) h1 b2 (VLevel.succ_congr b3)
    | inr h =>
      refine (h.peelTo fun hb => ?_).symm
      let .sort' b1 b2 b3 := hb
      refine IsDefEqStrong.symm (.defeqDF (u := .succ (.succ _)) h1 ?_ (.sortDF h1 h2 h3))
      exact .sortDF (l := .succ _) (l' := .succ _) h1 b2 (VLevel.succ_congr (h3.trans b3))
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    intro _ _ h
    cases h with
    | inl h =>
      refine h.peelTo fun hb => ?_
      let .const b1 b2 b3 b4 b5 b6 := hb
      cases h1.symm.trans b1
      exact .constDF h1 h2 h3 h4 h5 h6 h7 h8
    | inr h =>
      refine (h.peelTo fun hb => ?_).symm
      let .const b1 b2 b3 b4 b5 b6 := hb
      cases h1.symm.trans b1
      exact IsDefEqStrong.symm (.defeqDF h6 h8 (.constDF h1 h2 h3 h4 h5 h6 h7 h8))
  | appDF h1 h2 h3 h4 h5 h6 h7 ih3 ih4 ih5 ih6 ih7 =>
    intro hΓ _ h
    cases h with
    | inl h =>
      refine h.peelTo fun hb => ?_
      let .app b1 b2 b3 b4 b5 b6 b7 b8 := hb
      have df := ih5 hΓ (.inl b6)
      have da := ih6 hΓ (.inl b7)
      have dB := IsDefEqStrong.instDF (v := .succ _) henv hΓ b1 b2 b3.refl
        (.sortDF b2 b2 rfl) b4.refl da
      simp only [VExpr.inst] at dB
      exact .appDF b1 b2 b3.refl b4.refl df da dB
    | inr h =>
      refine (h.peelTo fun hb => ?_).symm
      let .app b1 b2 b3 b4 b5 b6 b7 b8 := hb
      have df := ih5 hΓ (.inr b6)
      have da := ih6 hΓ (.inr b7)
      have dB := IsDefEqStrong.instDF (v := .succ _) henv hΓ b1 b2 b3.refl
        (.sortDF b2 b2 rfl) b4.refl da
      simp only [VExpr.inst] at dB
      exact IsDefEqStrong.symm (.defeqDF b2 dB (.appDF b1 b2 b3.refl b4.refl df da dB))
  | lamDF h1 h2 h3 h4 h5 h6 h7 ih3 ih4 ih5 ih6 ih7 =>
    intro hΓ _ h
    cases h with
    | inl h =>
      refine h.peelTo fun hb => ?_
      let .lam b1 b2 b3 b4 b5 b6 := hb
      have dA := ih3 hΓ (.inl b3)
      have dbody := ih6 ⟨hΓ, _, b3.refl⟩ (.inl b5)
      exact .lamDF b1 b2 dA b4.refl (dA.defeqDF_l henv hΓ b4.refl)
        dbody (dA.defeqDF_l henv hΓ dbody)
    | inr h =>
      refine (h.peelTo fun hb => ?_).symm
      let .lam b1 b2 b3 b4 b5 b6 := hb
      have dA := ih3 hΓ (.inr b3)
      have hB := dA.symm.defeqDF_l henv hΓ b4.refl
      have hbody' := dA.symm.defeqDF_l henv hΓ b5.refl
      have dbody := ih6 ⟨hΓ, _, dA.hasType.1⟩ (.inr hbody'.hasType'.1)
      have main := IsDefEqStrong.lamDF b1 b2 dA hB b4.refl dbody
        (dA.defeqDF_l henv hΓ dbody)
      exact IsDefEqStrong.symm (.defeqDF (u := .imax _ _) ⟨b1, b2⟩
        (.forallEDF b1 b2 dA hB b4.refl) main)
  | forallEDF h1 h2 h3 h4 h5 ih3 ih4 ih5 =>
    intro hΓ _ h
    cases h with
    | inl h =>
      refine h.peelTo fun hb => ?_
      let .forallE b1 b2 b3 b4 := hb
      have dA := ih3 hΓ (.inl b3)
      have dbody := ih4 ⟨hΓ, _, b3.refl⟩ (.inl b4)
      exact .forallEDF b1 b2 dA dbody (dA.defeqDF_l henv hΓ dbody)
    | inr h =>
      refine (h.peelTo fun hb => ?_).symm
      let .forallE b1 b2 b3 b4 := hb
      have dA := ih3 hΓ (.inr b3)
      have hbody' := dA.symm.defeqDF_l henv hΓ b4.refl
      have dbody := ih4 ⟨hΓ, _, dA.hasType.1⟩ (.inr hbody'.hasType'.1)
      exact IsDefEqStrong.symm (.forallEDF b1 b2 dA dbody (dA.defeqDF_l henv hΓ dbody))
  | defeqDF h1 h2 h3 ih2 ih3 => intro hΓ _ h; exact ih3 hΓ h
  | beta h1 h2 h3 h4 h5 h6 h7 h8 ih3 ih4 ih5 ih6 ih7 ih8 =>
    intro hΓ _ h
    cases h with
    | inl h => exact h.peelTo fun hb => hbeta hΓ h1 h2 h3 h4 h5 h6 h7 h8 (.inl hb)
    | inr h => exact (h.peelTo fun hb => (hbeta hΓ h1 h2 h3 h4 h5 h6 h7 h8 (.inr hb)).symm).symm
  | eta h1 h2 h3 h4 h5 h6 h7 h8 ih3 ih4 ih5 ih6 ih7 ih8 =>
    intro hΓ _ h
    cases h with
    | inl h => exact h.peelTo fun hb => heta hΓ h1 h2 h3 h4 h5 h6 h7 h8 (.inl hb)
    | inr h => exact (h.peelTo fun hb => (heta hΓ h1 h2 h3 h4 h5 h6 h7 h8 (.inr hb)).symm).symm
  | proofIrrel h1 h2 h3 ih1 ih2 ih3 =>
    intro hΓ _ h
    cases h with
    | inl h => exact h.peelTo fun hb => hproof hΓ h1 h2 h3 (.inl hb)
    | inr h => exact (h.peelTo fun hb => (hproof hΓ h1 h2 h3 (.inr hb)).symm).symm
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 ih5 ih6 ih7 ih8 ih9 =>
    intro hΓ _ h
    cases h with
    | inl h => exact h.peelTo fun hb => hextra hΓ h1 h2 h3 h4 h5 h6 h7 h8 h9 (.inl hb)
    | inr h => exact (h.peelTo fun hb => (hextra hΓ h1 h2 h3 h4 h5 h6 h7 h8 h9 (.inr hb)).symm).symm

/-- **The obligation Route A actually has**: the `retype` case of `IsDefEqStrong.hasType'`,
with the conversion premise the case really carries. -/
theorem HasTypeStrong.retype_of_conv (henv : Ordered env)
    (hbeta : BetaRetype env U) (heta : EtaRetype env U)
    (hproof : ProofRetype env U) (hextra : ExtraRetype env U)
    {Γ : List VExpr} {e₁ e₂ A B : VExpr} (hΓ : CtxStrong env U Γ)
    (h : env.IsDefEqStrong U Γ e₁ e₂ A) (h1B : env.HasTypeStrong U Γ e₁ B true) :
    env.HasTypeStrong U Γ e₂ B true :=
  (h.retypes henv hbeta heta hproof hextra hΓ (.inl h1B)).hasType'.2

/-- The same in the hypothesis shape the *consumers* carry.  `IsDefEq.strong` already takes
`Ordered env` and `OnCtx Γ (env.IsType U)`, so if the enlargement's obligation is discharged
there rather than inside `IsDefEqStrong.hasType'`, Route A costs **no new hypothesis at all** —
`CtxStrong.strong` manufactures the stronger context invariant from the weaker one. -/
theorem HasTypeStrong.retype_of_conv' (henv : Ordered env)
    (hbeta : BetaRetype env U) (heta : EtaRetype env U)
    (hproof : ProofRetype env U) (hextra : ExtraRetype env U)
    {Γ : List VExpr} {e₁ e₂ A B : VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqStrong U Γ e₁ e₂ A) (h1B : env.HasTypeStrong U Γ e₁ B true) :
    env.HasTypeStrong U Γ e₂ B true :=
  retype_of_conv henv hbeta heta hproof hextra (CtxStrong.strong henv hΓ) h h1B

/-! ## Pricing: all four residuals follow from unique typing -/

/-- Unique typing, packaged over `HasTypeStrong`. -/
def UniqStrong (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ : List VExpr} {e A B : VExpr}, CtxStrong env U Γ →
    env.HasTypeStrong U Γ e A true → env.HasTypeStrong U Γ e B true →
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u)

theorem uniqStrong_of_piInvStratApp (henv : VEnv.WF env) (hpi : PiInvStratApp env U) :
    UniqStrong env U := by
  intro Γ e A B hΓ h1 h2
  obtain ⟨n₁, s1⟩ := h1.stratify
  obtain ⟨n₂, s2⟩ := h2.stratify
  obtain ⟨u, hAB, -⟩ := uniqAux henv hpi _ hΓ.defeq
    (Nat.le_max_left n₁ n₂) (Nat.le_max_right n₁ n₂) s1 s2
  exact ⟨u, hAB.strong henv.ordered hΓ.defeq⟩

theorem betaRetype_of_uniqStrong (henv : Ordered env) (huniq : UniqStrong env U) :
    BetaRetype env U := by
  intro Γ A B e e' X u v hΓ h1 h2 h3 h4 h5 h6 h7 h8 hor
  have canon := IsDefEqStrong.beta h1 h2 h3 h4 h5 h6 h7 h8
  refine hor.elim (fun hb => ?_) (fun hb => ?_)
  · have ⟨_, hc⟩ := huniq hΓ canon.hasType'.1 (.base hb)
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc canon
  · have ⟨_, hc⟩ := huniq hΓ canon.hasType'.2 (.base hb)
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc canon

theorem etaRetype_of_uniqStrong (henv : Ordered env) (huniq : UniqStrong env U) :
    EtaRetype env U := by
  intro Γ A B e X u v hΓ h1 h2 h3 h4 h5 h6 h7 h8 hor
  have canon := IsDefEqStrong.eta h1 h2 h3 h4 h5 h6 h7 h8
  refine hor.elim (fun hb => ?_) (fun hb => ?_)
  · have ⟨_, hc⟩ := huniq hΓ canon.hasType'.1 (.base hb)
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc canon
  · have ⟨_, hc⟩ := huniq hΓ canon.hasType'.2 (.base hb)
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc canon

theorem proofRetype_of_uniqStrong (henv : Ordered env) (huniq : UniqStrong env U) :
    ProofRetype env U := by
  intro Γ p h h' X hΓ h1 h2 h3 hor
  have canon := IsDefEqStrong.proofIrrel h1 h2 h3
  refine hor.elim (fun hb => ?_) (fun hb => ?_)
  · have ⟨_, hc⟩ := huniq hΓ canon.hasType'.1 (.base hb)
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc canon
  · have ⟨_, hc⟩ := huniq hΓ canon.hasType'.2 (.base hb)
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc canon

theorem extraRetype_of_uniqStrong (henv : Ordered env) (huniq : UniqStrong env U) :
    ExtraRetype env U := by
  intro Γ df ls X u hΓ h1 h2 h3 h4 h5 h6 h7 h8 h9 hor
  have canon := IsDefEqStrong.extra h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine hor.elim (fun hb => ?_) (fun hb => ?_)
  · have ⟨_, hc⟩ := huniq hΓ canon.hasType'.1 (.base hb)
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc canon
  · have ⟨_, hc⟩ := huniq hΓ canon.hasType'.2 (.base hb)
    exact .defeqDF (hc.defeq.sort_r henv hΓ.defeq) hc canon

/-- **Upper bound.**  The four residuals together are no stronger than the corner. -/
theorem retypes_of_piInvStratApp (henv : VEnv.WF env) (hpi : PiInvStratApp env U)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : env.IsDefEqStrong U Γ e₁ e₂ A)
    (hΓ : CtxStrong env U Γ) : Retypes env U Γ e₁ e₂ :=
  H.retypes henv.ordered
    (betaRetype_of_uniqStrong henv.ordered (uniqStrong_of_piInvStratApp henv hpi))
    (etaRetype_of_uniqStrong henv.ordered (uniqStrong_of_piInvStratApp henv hpi))
    (proofRetype_of_uniqStrong henv.ordered (uniqStrong_of_piInvStratApp henv hpi))
    (extraRetype_of_uniqStrong henv.ordered (uniqStrong_of_piInvStratApp henv hpi)) hΓ

/-! ## Non-vacuity -/

/-- **The theorem fires non-degenerately, over every environment.**  `e₁ ≠ e₂` and `A ≠ B`
syntactically, so the conclusion is neither reflexivity nor the input re-indexed at its own
type; and the instance goes through the `sortDF` case, which uses **none** of the four
residuals. -/
theorem retypes_fires (henv : Ordered env)
    (hbeta : BetaRetype env U) (heta : EtaRetype env U)
    (hproof : ProofRetype env U) (hextra : ExtraRetype env U) :
    ∃ e₁ e₂ A B : VExpr, e₁ ≠ e₂ ∧ A ≠ B ∧
      env.IsDefEqStrong U [] e₁ e₂ A ∧ env.HasTypeStrong U [] e₁ B true ∧
      env.IsDefEqStrong U [] e₁ e₂ B := by
  have hz : (VLevel.zero).WF U := trivial
  have hi : (VLevel.imax .zero .zero).WF U := ⟨trivial, trivial⟩
  have heq : (VLevel.imax .zero .zero) ≈ VLevel.zero := VLevel.imax_zero
  refine ⟨.sort (.imax .zero .zero), .sort .zero, .sort (.succ (.imax .zero .zero)),
    .sort (.succ .zero), by simp, by simp, .sortDF hi hz heq,
    .base (.sort' hi hz heq), ?_⟩
  exact (IsDefEqStrong.retypes (Γ := []) henv hbeta heta hproof hextra
    (.sortDF hi hz heq) trivial) (.inl (.base (.sort' hi hz heq)))


end VEnv
end Lean4Lean

section Audit
open Lean4Lean.VEnv
#print axioms Lean4Lean.VEnv.HasTypeStrong.peelTo
#print axioms Lean4Lean.VEnv.IsDefEqStrong.retypes
#print axioms Lean4Lean.VEnv.HasTypeStrong.retype_of_conv
#print axioms Lean4Lean.VEnv.HasTypeStrong.retype_of_conv'
#print axioms Lean4Lean.VEnv.uniqStrong_of_piInvStratApp
#print axioms Lean4Lean.VEnv.betaRetype_of_uniqStrong
#print axioms Lean4Lean.VEnv.etaRetype_of_uniqStrong
#print axioms Lean4Lean.VEnv.proofRetype_of_uniqStrong
#print axioms Lean4Lean.VEnv.extraRetype_of_uniqStrong
#print axioms Lean4Lean.VEnv.retypes_of_piInvStratApp
#print axioms Lean4Lean.VEnv.retypes_fires
end Audit
