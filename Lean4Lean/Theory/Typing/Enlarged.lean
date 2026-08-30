import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.CycleConv

/-!
# The `IsDefEqU'` enlargement of `docs/backward-analysis.md` §5, prototyped and priced

`Theory/Typing/Basic.lean` makes `IsDefEq` **four-place**, `Γ ⊢ e₁ ≡ e₂ : A`, with the type
an index shared by every rule.  Composing two conversions *at different types* is therefore
not a rule but a theorem — `IsDefEq.uniq` — and `docs/backward-analysis.md` §5 proposes an
enlargement **(E)** that would make it a rule, on the claim that this removes `uniq`, and
hence `IsDefEqU.sort_inv` and `IsDefEqU.forallE_inv_stratified`, from `kernel_sound`'s cone.

This file is the prototype.  It does **not** edit `Basic.lean`; it defines a parallel
judgment `IsDefEqE` and proves, machine-checked, exactly which of the claims hold.

## What is proved here

* `IsDefEq.toE` — the enlargement really is an enlargement (every base derivation embeds).
* `IsDefEqE.retype` is the *single* added rule, and it carries a **typing premise** rather
  than being a bare closure.  §5's literal (E) — "conversion takes the untyped closure
  `IsDefEqU' Γ A B`" — is **not** what is prototyped here, because it loses regularity:
  see `IsDefEq.isType'` (`Theory/Typing/Lemmas.lean:869`), whose `defeqDF` case is
  `⟨_, h1.hasType.2⟩`, reading `IsType Γ B` straight off the `.sort u` index of the
  conversion premise.  Delete that index and the case can only be closed by
  `IsType.defeqU_l`, which is itself one of the twelve lemmas (E) exists to make free.
  **That is a circle, and it is why the rule must carry the typing premise.**
* Ten of the twelve `(E)`-family lemmas of `scripts/cone-measure.lean` become derivations
  with **no `VEnv.WF`, no `OnCtx`, and no appeal to `uniq`** (§ *The (E) family, free*).
  The remaining two need `IsTypeE Γ A`, i.e. regularity, and nothing else.
* `IsDefEqE.toIsDefEq` — **conservativity**: given `IsDefEq.uniq`, the enlargement adds
  nothing.  So (E) cannot make a provable statement unprovable, and it cannot introduce
  unsoundness that `uniq` would not already permit.  It also means the enlargement is
  *not* provably strict: a non-vacuity witness can show the new rule firing at a
  non-degenerate instance, and that is all it can show.
* `retype_fires` — the rule fires at `CycleConv.propLoopEnv`, which is proved `VEnv.WF`
  with provably non-terminating head reduction (`propLoop_headStep_not_wf`), on an
  instance whose two type indices are **syntactically distinct** terms.

## What is *not* proved here, and is the round's result

(E) does **not** remove `uniq` from `kernel_sound`'s cone.  See `docs/handoff-isdefequ.md`
for the measurement.  The three surviving consumers use `uniq` in a shape that is not
composition-at-different-types, so no amount of making composition a rule reaches them.
-/

namespace Lean4Lean
namespace VEnv

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEqE Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEqE Γ e1 e2 A
variable (env : VEnv) (uvars : Nat)

/-- **The enlarged judgment.**  `Theory/Typing/Basic.lean`'s `IsDefEq`, with one added rule.

`retype` is composition-at-different-types, as a rule: an equation may be re-indexed at any
*other* type of its left endpoint.  Everything `kernel_sound`'s cone currently spends
`IsDefEq.uniq` on in order to *compose* is an instance of it.

The premise `Γ ⊢ e₁ : B` is what §5's literal (E) drops, and dropping it is what breaks
regularity.  Here the second premise is a full derivation, so every induction over
`IsDefEqE` that needs a fact about `B` gets it from the second induction hypothesis. -/
inductive IsDefEqE : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | appDF :
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    Γ ⊢ e : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls
  | retype : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ : B → Γ ⊢ e₁ ≡ e₂ : B

end

/-- `HasType` for the enlarged judgment. -/
def HasTypeE (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  IsDefEqE env U Γ e e A

/-- `IsType` for the enlarged judgment. -/
def IsTypeE (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, env.HasTypeE U Γ A (.sort u)

/-- `IsDefEqU` for the enlarged judgment.  Note this is still the *derived* existential:
under `retype` it is already reflexive-symmetric-transitive on well-typed terms
(`IsDefEqUE.trans` below), which is what §5's literal (E) tried to obtain by fiat. -/
def IsDefEqUE (env : VEnv) (U : Nat) (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  ∃ A, env.IsDefEqE U Γ e₁ e₂ A

variable {env : VEnv} {U : Nat}

/-- **The enlargement is an enlargement.**  Every base derivation is an enlarged one. -/
theorem IsDefEq.toE : ∀ {Γ e₁ e₂ A}, env.IsDefEq U Γ e₁ e₂ A → env.IsDefEqE U Γ e₁ e₂ A := by
  intro Γ e₁ e₂ A H
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra h1 h2 h3

theorem HasType.toE {Γ e A} (H : env.HasType U Γ e A) : env.HasTypeE U Γ e A :=
  IsDefEq.toE H
theorem IsType.toE {Γ A} (H : env.IsType U Γ A) : env.IsTypeE U Γ A :=
  H.imp fun _ => IsDefEq.toE
theorem IsDefEqU.toE {Γ e₁ e₂} (H : env.IsDefEqU U Γ e₁ e₂) : env.IsDefEqUE U Γ e₁ e₂ :=
  H.imp fun _ => IsDefEq.toE

/-! ## The (E) family, free

The twelve declarations `scripts/cone-measure.lean` cuts as "the (E) family" are the ones
`docs/backward-analysis.md` §5 says become rules.  Ten of them are below, each with **no**
`VEnv.WF` hypothesis, **no** `OnCtx` hypothesis, and no appeal to `uniq`.  Compare
`Theory/Typing/UniqueTyping.lean:124–170`, where every one of them takes `henv` and `hΓ`
and goes through `IsDefEq.uniq`. -/

theorem IsDefEqE.hasType {Γ e1 e2 A} (H : env.IsDefEqE U Γ e1 e2 A) :
    env.HasTypeE U Γ e1 A ∧ env.HasTypeE U Γ e2 A := ⟨H.trans H.symm, H.symm.trans H⟩

theorem IsDefEqE.toU {Γ e1 e2 A} (H : env.IsDefEqE U Γ e1 e2 A) : env.IsDefEqUE U Γ e1 e2 :=
  ⟨_, H⟩

theorem IsDefEqUE.symm {Γ e₁ e₂} (h : env.IsDefEqUE U Γ e₁ e₂) : env.IsDefEqUE U Γ e₂ e₁ :=
  h.imp fun _ => (·.symm)

/-- `IsDefEq.trans_l` (`UniqueTyping.lean:135`) — there with `henv`, `hΓ` and `uniq`. -/
theorem IsDefEqE.trans_l {Γ e₁ e₂ e₃ A B}
    (h₁ : env.IsDefEqE U Γ e₁ e₂ A) (h₂ : env.IsDefEqE U Γ e₂ e₃ B) :
    env.IsDefEqE U Γ e₁ e₃ A := h₁.trans (h₂.retype h₁.hasType.2)

/-- `IsDefEq.trans_r` (`UniqueTyping.lean:131`). -/
theorem IsDefEqE.trans_r {Γ e₁ e₂ e₃ A B}
    (h₁ : env.IsDefEqE U Γ e₁ e₂ A) (h₂ : env.IsDefEqE U Γ e₂ e₃ B) :
    env.IsDefEqE U Γ e₁ e₃ B := (h₁.symm.retype h₂.hasType.1).symm.trans h₂

/-- `IsDefEq.transU_r` (`UniqueTyping.lean:139`). -/
theorem IsDefEqE.transU_r {Γ e₁ e₂ e₃ A}
    (h₁ : env.IsDefEqUE U Γ e₁ e₂) (h₂ : env.IsDefEqE U Γ e₂ e₃ A) :
    env.IsDefEqE U Γ e₁ e₃ A := let ⟨_, h₁⟩ := h₁; h₁.trans_r h₂

/-- `IsDefEq.transU_l` (`UniqueTyping.lean:143`). -/
theorem IsDefEqE.transU_l {Γ e₁ e₂ e₃ A}
    (h₁ : env.IsDefEqE U Γ e₁ e₂ A) (h₂ : env.IsDefEqUE U Γ e₂ e₃) :
    env.IsDefEqE U Γ e₁ e₃ A := let ⟨_, h₂⟩ := h₂; h₁.trans_l h₂

/-- `IsDefEqU.of_l` (`UniqueTyping.lean:155`) — **literally the new rule.** -/
theorem IsDefEqUE.of_l {Γ e₁ e₂ A}
    (h1 : env.IsDefEqUE U Γ e₁ e₂) (h2 : env.HasTypeE U Γ e₁ A) :
    env.IsDefEqE U Γ e₁ e₂ A := let ⟨_, h⟩ := h1; h.retype h2

/-- `IsDefEqU.of_r` (`UniqueTyping.lean:163`). -/
theorem IsDefEqUE.of_r {Γ e₁ e₂ A}
    (h1 : env.IsDefEqUE U Γ e₁ e₂) (h2 : env.HasTypeE U Γ e₂ A) :
    env.IsDefEqE U Γ e₁ e₂ A := (h1.symm.of_l h2).symm

/-- `HasType.defeqU_l` (`UniqueTyping.lean:157`). -/
theorem HasTypeE.defeqU_l {Γ e₁ e₂ A}
    (h1 : env.IsDefEqUE U Γ e₁ e₂) (h2 : env.HasTypeE U Γ e₁ A) :
    env.HasTypeE U Γ e₂ A := (h1.of_l h2).hasType.2

/-- `IsType.defeqU_l` (`UniqueTyping.lean:161`) — free, and this is the one that matters:
it is the step §5's literal (E) needs in order to prove its *own* regularity, and it is a
member of the family (E) exists to make free.  With the typing premise on the rule the
circle is cut, because `IsTypeE Γ A₁` **is** a typing of the equation's left endpoint. -/
theorem IsTypeE.defeqU_l {Γ A₁ A₂}
    (h1 : env.IsDefEqUE U Γ A₁ A₂) (h2 : env.IsTypeE U Γ A₁) :
    env.IsTypeE U Γ A₂ := let ⟨u, h2⟩ := h2; let ⟨_, h1⟩ := h1; ⟨u, (h1.retype h2).hasType.2⟩

/-- `IsDefEqU.trans` (`UniqueTyping.lean:167`). -/
theorem IsDefEqUE.trans {Γ e₁ e₂ e₃}
    (h1 : env.IsDefEqUE U Γ e₁ e₂) (h2 : env.IsDefEqUE U Γ e₂ e₃) :
    env.IsDefEqUE U Γ e₁ e₃ := let ⟨_, h1⟩ := h1; let ⟨_, h2⟩ := h2; ⟨_, h1.trans_l h2⟩

/-- `isDefEq_iff` (`UniqueTyping.lean:117`). -/
theorem isDefEqE_iff {Γ e₁ e₂ A} :
    env.IsDefEqE U Γ e₁ e₂ A ↔
      env.HasTypeE U Γ e₁ A ∧ env.HasTypeE U Γ e₂ A ∧ env.IsDefEqUE U Γ e₁ e₂ :=
  ⟨fun h => ⟨h.hasType.1, h.hasType.2, _, h⟩, fun ⟨h1, _, h3⟩ => h3.of_l h1⟩

/-! ### The two that are *not* free, and exactly what they owe

`IsDefEqU.defeqDF` and `HasType.defeqU_r` convert an equation along a conversion **between
its types**, so they need to know that the source type is a type.  That is regularity —
`IsDefEq.isType` — and nothing more: no `uniq`, no `sort_inv`.  Stated with the obligation
explicit, so the price is visible rather than hidden in an `henv`. -/

/-- `IsDefEqU.defeqDF` (`UniqueTyping.lean:147`), with `henv`/`hΓ`/`uniq` replaced by the
single hypothesis `IsTypeE Γ A`. -/
theorem IsDefEqUE.defeqDF {Γ e₁ e₂ A B} (hA : env.IsTypeE U Γ A)
    (h₁ : env.IsDefEqUE U Γ A B) (h₂ : env.IsDefEqE U Γ e₁ e₂ A) :
    env.IsDefEqE U Γ e₁ e₂ B :=
  let ⟨_, hA⟩ := hA; let ⟨_, h₁⟩ := h₁; .defeqDF (h₁.retype hA) h₂

/-- `HasType.defeqU_r` (`UniqueTyping.lean:165`), likewise. -/
theorem HasTypeE.defeqU_r {Γ e A₁ A₂} (hA : env.IsTypeE U Γ A₁)
    (h1 : env.IsDefEqUE U Γ A₁ A₂) (h2 : env.HasTypeE U Γ e A₁) :
    env.HasTypeE U Γ e A₂ := h1.defeqDF hA h2

/-! ## The obligation the enlargement creates, and the collapse test

The paragraphs above are the credit side.  This is the debit side, and it is the reason the
enlargement is **not** recommended as an in-place edit to `Basic.lean`.

Adding `retype` to `IsDefEq` forces a matching constructor in `IsDefEqStrong`
(`Theory/Typing/Strong.lean:18`), because `IsDefEq.strong`'s new case has
`IsDefEqStrong Γ e₁ e₂ A` and `IsDefEqStrong Γ e₁ e₁ B` and no way to reach
`IsDefEqStrong Γ e₁ e₂ B` — `IsDefEqStrong.defeqDF` wants `Γ ⊢ A ≡ B : .sort u`, which is
unique typing.  That forces one in `HasTypeStrong` too, because `IsDefEqStrong.hasType'`
(`Strong.lean:829`) must produce `HasTypeStrong Γ e₂ B` from `HasTypeStrong Γ e₂ A` and
`HasTypeStrong Γ e₁ B`, and `HasTypeStrong.defeq` wants the same conversion.  And that forces
one in `HasTypeStratified`, whose induction is what proves `IsDefEq.uniq`
(`Theory/Typing/UniqueTyping.lean:13`).

**So `uniq`'s own induction gains a case, and the case's two derivations are about two
different terms** — the node types `e₂`, its premise types `e₁`.  What that case needs is the
statement below.

`UniqAcross` is `uniq` again: `uniqU_of_uniqAcross` instantiates it at `e₁ := e₂` and gets
`uniqU` back, and `uniqAcross` derives it from `uniq`.  **The residual degenerates into the
target — the collapse test fails.**  An in-place `retype` therefore trades a proved `uniq`
(one `sorry`-backed input) for an unproved one. -/

/-- Unique typing *across a conversion*: the obligation the `retype` case of `uniq`'s
stratified induction creates. -/
def UniqAcross (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ e₁ e₂ A₀ A B}, OnCtx Γ (env.IsType U) → env.IsDefEq U Γ e₁ e₂ A₀ →
    env.HasType U Γ e₁ A → env.HasType U Γ e₂ B → env.IsDefEqU U Γ A B

/-- `UniqAcross` follows from `uniq` — so it is not a *new* obligation. -/
theorem uniqAcross (henv : VEnv.WF env) : UniqAcross env U := by
  intro Γ e₁ e₂ A₀ A B hΓ hc h1 h2
  exact (hc.symm.uniqU henv hΓ h1).symm.trans henv hΓ (hc.uniqU henv hΓ h2)

/-- **…and it implies `uniq` back**, by taking the conversion to be the first typing itself.
This is the collapse test, and it fails: the new case is the theorem it is a case of. -/
theorem uniqU_of_uniqAcross (H : UniqAcross env U) {Γ e₁ e₂ e₃ A B}
    (hΓ : OnCtx Γ (env.IsType U)) (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEqU U Γ A B := H hΓ h1 h1.hasType.1 h2.hasType.1

/-! ## Conservativity

Given `IsDefEq.uniq`, the enlargement collapses.  So (E) is safe in both directions: it
adds no conversions that `uniq` does not already justify, hence the model owes nothing new
*that it does not already owe for `uniq`* — and, in the other direction, it cannot rescue a
statement that is false, because the two relations coincide. -/

/-- **Conservativity of the enlargement, machine-checked.**  `IsDefEqE` collapses to
`IsDefEq` exactly at the `retype` rule, and exactly by `IsDefEq.uniq`. -/
theorem IsDefEqE.toIsDefEq (henv : VEnv.WF env) :
    ∀ {Γ e₁ e₂ A}, OnCtx Γ (env.IsType U) → env.IsDefEqE U Γ e₁ e₂ A →
      env.IsDefEq U Γ e₁ e₂ A := by
  intro Γ e₁ e₂ A hΓ H
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih1 ih2 => exact (ih1 hΓ).trans (ih2 hΓ)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ ih1 ih2 => exact .appDF (ih1 hΓ) (ih2 hΓ)
  | lamDF _ _ ih1 ih2 =>
    have h1 := ih1 hΓ
    exact .lamDF h1 (ih2 ⟨hΓ, _, h1.hasType.1⟩)
  | forallEDF _ _ ih1 ih2 =>
    have h1 := ih1 hΓ
    exact .forallEDF h1 (ih2 ⟨hΓ, _, h1.hasType.1⟩)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
  | beta _ _ ih1 ih2 =>
    have h2 := ih2 hΓ
    exact .beta (ih1 ⟨hΓ, h2.isType henv.ordered hΓ⟩) h2
  | eta _ ih => exact .eta (ih hΓ)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  | extra h1 h2 h3 => exact .extra h1 h2 h3
  | retype _ _ ih1 ih2 =>
    have h1 := ih1 hΓ
    exact IsDefEqU.defeqDF henv hΓ (h1.symm.uniqU henv hΓ (ih2 hΓ)) h1

/-- The relations coincide, given `uniq`. -/
theorem isDefEqE_iff_isDefEq (henv : VEnv.WF env) {Γ e₁ e₂ A}
    (hΓ : OnCtx Γ (env.IsType U)) :
    env.IsDefEqE U Γ e₁ e₂ A ↔ env.IsDefEq U Γ e₁ e₂ A :=
  ⟨IsDefEqE.toIsDefEq henv hΓ, IsDefEq.toE⟩

end VEnv

/-! ## The migration, exercised

The realistic migration is not this parallel judgment: it is adding the `retype` constructor
to `Basic.lean`'s `IsDefEq` in place, which leaves every *statement* in the tree unchanged
and adds one case to every induction over `IsDefEq`, `IsDefEqStrong`, `HasTypeStrong` and
`HasTypeStratified`.  The claim priced in `docs/handoff-isdefequ.md` §4 is that **every one
of those cases is mechanical**, for a structural reason: `retype` does not touch the
endpoints `e₁`, `e₂`, only the type index.  So

* a *congruence* induction (`mono`, `weakN`, `instN`, `instL`, an environment collapse)
  rebuilds the rule from its two induction hypotheses; and
* an *inversion* keyed on the shape of an endpoint (`sort_inv`, `forallE_inv`,
  `sort_forallE_inv`, `const_*_inv` — the whole `Injectivity.lean` family) returns the first
  induction hypothesis unchanged, exactly as it already does for `defeqDF`
  (`Injectivity.lean:836`, `| defeqDF _ _ _ _ ih => exact ih`).

Both shapes are exercised below rather than asserted.  `loop_conv_collapseE` is a real
endpoint-sensitive induction — its `extra` case must still inspect the rule's two sides —
and its `retype` case is one line. -/

/-- A congruence induction over the enlarged relation: `IsDefEq.mono`
(`Theory/Typing/Lemmas.lean:386`), ported.  The `retype` case is `.retype ih1 ih2`. -/
theorem VEnv.IsDefEqE.mono {env env' : VEnv} (henv : env ≤ env') {U Γ e1 e2 A}
    (H : env.IsDefEqE U Γ e1 e2 A) : env'.IsDefEqE U Γ e1 e2 A := by
  induction H with
  | bvar h => exact .bvar h
  | constDF h1 h2 h3 h4 h5 => exact .constDF (henv.1 h1) h2 h3 h4 h5
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra (henv.2 h1) h2 h3
  | retype _ _ ih1 ih2 => exact .retype ih1 ih2

/-- An induction with an endpoint-sensitive case: `CycleConv.loop_conv_collapse`, ported.
The `extra` case still has to look at the rule's endpoints; the `retype` case does not, and
is one line.  This is the shape every `Injectivity.lean` inversion has. -/
theorem loop_conv_collapseE {U Γ e₁ e₂ A} (H : loopEnv.IsDefEqE U Γ e₁ e₂ A) :
    loopEnv2.IsDefEqE U Γ e₁ e₂ A := by
  induction H with
  | bvar h => exact .bvar h
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | retype _ _ ih1 ih2 => exact .retype ih1 ih2
  | @extra df ls _ h1 _ h3 =>
    obtain rfl | rfl | h1 := h1
    · cases List.eq_nil_of_length_eq_zero h3
      exact VEnv.IsDefEq.toE (loop_defeq_without_rules ..).symm
    · cases List.eq_nil_of_length_eq_zero h3
      exact VEnv.IsDefEq.toE (loop_defeq_without_rules ..)
    · exact absurd h1 nofun

/-! ## Non-vacuity

`CycleConv.propLoopEnv` is one `.unsafeDef` step from the empty environment, is proved
`VEnv.WF` (`propLoopEnv_wf`) and has provably non-terminating weak-head reduction
(`propLoop_headStep_not_wf`).  It carries two constants `A B : Prop` with `A ≡ B`, so a
variable of type `.const A []` also has type `.const B []` — two **syntactically distinct**
types of one term, which is the situation `retype` exists for.

This is the strongest form of non-vacuity available: `isDefEqE_iff_isDefEq` above proves
the enlargement is *not* strict given `uniq`, so no witness can show `IsDefEqE` derives
something `IsDefEq` does not.  What the witness shows is that the rule fires at a
non-degenerate instance — distinct type indices, non-normalising environment — rather than
only where `A` and `B` are the same term. -/

open VEnv in
theorem propLoop_AB_defeq {U Γ} :
    propLoopEnv.IsDefEq U Γ (.const `A []) (.const `B []) (.sort .zero) :=
  .extra (df := propLoopA.toDefEq) (ls := []) propLoopEnv_defeqs_A nofun rfl

open VEnv in
/-- **`retype` fires at `propLoopEnv`**, on an instance whose two type indices,
`.const `A []` and `.const `B []`, are distinct terms. -/
theorem retype_fires :
    propLoopEnv.IsDefEqE 0 [.const `A []] (.bvar 0) (.bvar 0) (.const `B []) ∧
    (.const `A [] : VExpr) ≠ .const `B [] := by
  have hb : propLoopEnv.IsDefEqE 0 [.const `A []] (.bvar 0) (.bvar 0) (.const `A []) :=
    .bvar .zero
  have hc : propLoopEnv.IsDefEqE 0 [.const `A []] (.bvar 0) (.bvar 0) (.const `B []) :=
    .defeqDF (u := .zero) (IsDefEq.toE propLoop_AB_defeq) hb
  exact ⟨IsDefEqE.retype hb hc, by simp⟩

end Lean4Lean
