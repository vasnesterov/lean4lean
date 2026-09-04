import Lean4Lean.Theory.Typing.StructEtaPrice
import Lean4Lean.Theory.Typing.ParRedPropRefute
import Lean4Lean.Theory.Typing.EtaGuardLand

/-!
# Pricing the confluence-layer rebuild: is it one job with structure eta, or two?

Round of 2026-09-04.  This file is a **pricing** file: it establishes no new confluence
result and repairs nothing.  It answers one question with theorems instead of prose —

> Two central statements of `Theory/Typing/ChurchRosser.lean` are false as written
> (`NormalEq.descend`, `NormalEq.parRed`).  Structure eta must eventually enter the abstract
> relation.  **Is rebuilding the confluence layer over the extended relation
> `VEnv.IsDefEqSE` the same job as repairing the two false statements, or two jobs?**

**Answer: two jobs, and the file's §3–§5 are the machine-checked reason.**  The repair the two
false statements need is an extension of the *reduction* relation (a proof-replacement / `K⁺`
step); the eta job is an extension of the *conversion* relation.  Those are moves in opposite
directions, and §4 shows the eta extension is **provably inert** — pointwise equal to the old
relation — at the very environment where `descend` is refuted.  So re-erecting the layer over
`IsDefEqSE` leaves both refutations standing verbatim; it cannot be the repair.

## What each section is

* **§1** `CRSchema`, the confluence statement with its three relations abstracted, plus the
  anti-strawman check that it *is* `VEnv.ParRedStatement` on the nose, plus the transport
  lemma: pointwise-equal ingredients give the *same proposition*.
* **§2** The same for the descent: `DescentLamP` / `DescentOutP` / `DescendStatementP`, the
  layer's statements with the three relation ingredients abstracted, each checked equal to the
  real one by `rfl`.  This is where the "how relation-polymorphic is the layer?" question gets
  an answer: **three ingredients** — a conversion, a multi-step reduction, and a typing
  judgment — and nothing else.
* **§3** `IsDefEqSE` is **inert at a defeq-free environment**: the fourteenth constructor and
  the `extra` constructor are both dead there, so `IsDefEqSE = IsDefEq` pointwise.
* **§4** The same at the *layer* level: `NormalEqSE` (the conversion relation re-erected over
  `IsDefEqSE`, **with two structure-eta rules added**) and `ParRedSE` (the reduction relation
  re-erected, with a structure-eta reduction added) are pointwise equal to `NormalEq` /
  `ParRed` at a defeq-free environment.
* **§5** The verdict, transported: at `refEnv` (`Theory/Typing/DescendRefute.lean`) the
  re-erected descent statement is the **same proposition** as `DescendStatement refParams`, so
  `descend_uniq_sortUniq_not_all` refutes it unchanged.  Two jobs.
* **§6** The converse separation: the eta job's witnesses and the confluence job's witness are
  **disjoint**.  `refEnv` holds no structure at all (so the eta rule has nothing to do there),
  and the environments where eta fires (`MutField.bigEnv`) are not where either statement is
  refuted.
* **§7** Vacuity, per the brief: the transport is not a statement about a relation that relates
  nothing.  Reduction and non-trivial conversion both happen at `refEnv`.

## What this file does NOT claim

It does **not** claim `NormalEq.descend` is unconditionally false.  What is `sorryAx`-free is
`Lean4Lean.descend_uniq_sortUniq_not_all`, a **trilemma**:
`¬ (DescendStatement refParams ∧ refEnv.SortUniq 0 ∧ refEnv.UniqTyping 0)`.  The
unconditional form `Lean4Lean.not_descendStatement_of_wf` is `sorryAx`-tainted through
`IsDefEqU.forallE_inv_stratified`, and `DescendRefute.lean` says so itself
("satisfiability is therefore **open**, not settled").  Everything below is stated so that the
trilemma, not the tainted corollary, is what carries the weight.
-/

namespace Lean4Lean

open VExpr

/-! ## §1 The confluence statement, with its relations abstracted

`VEnv.ParRedStatement` mentions three relations: a conversion (`NormalEq`), a one-step
reduction (`ParRed`) and its reflexive-transitive closure (`ParRedS`).  Abstracting all three
turns "would the rebuilt layer's statement be a different proposition?" into a question with a
proof rather than an opinion. -/

/-- The confluence statement's shape.  `W` is the context well-formedness side condition, `N`
the conversion, `R` the one-step reduction, `RS` its closure. -/
def CRSchema (W : List VExpr → Prop)
    (N RS : List VExpr → VExpr → VExpr → Prop)
    (R : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ : List VExpr} {e₁ e₂ e₃ : VExpr}, W Γ → N Γ e₁ e₂ → R Γ e₂ e₃ →
    ∃ o, RS Γ e₁ o ∧ N Γ o e₃

namespace VEnv

section
variable [Params]
open Params

/-- **Anti-strawman check for §1.**  `CRSchema` at the real three relations is
`VEnv.ParRedStatement` — `NormalEq.parRed`'s statement — definitionally. -/
theorem crSchema_eq_parRedStatement :
    CRSchema (fun Γ => OnCtx Γ (IsType env univs)) NormalEq ParRedS ParRed
      = @ParRedStatement _ := rfl

end

end VEnv

/-- **Transport: pointwise-equal ingredients give the same proposition.**

This is the whole content of "the rebuilt layer's statement is/is not a different statement".
It is deliberately stated with `Iff`s rather than equalities, because the two relations being
compared are *different inductive types* (`NormalEq` and a re-erected `NormalEqSE`), so no
`rfl` is available and nothing but a pointwise equivalence can be had. -/
theorem crSchema_congr {W W' : List VExpr → Prop}
    {N N' RS RS' R R' : List VExpr → VExpr → VExpr → Prop}
    (hW : ∀ Γ, W Γ ↔ W' Γ)
    (hN : ∀ Γ a b, N Γ a b ↔ N' Γ a b)
    (hRS : ∀ Γ a b, RS Γ a b ↔ RS' Γ a b)
    (hR : ∀ Γ a b, R Γ a b ↔ R' Γ a b) :
    CRSchema W N RS R ↔ CRSchema W' N' RS' R' := by
  constructor
  · intro H _ _ _ _ hw hn hr
    obtain ⟨o, h1, h2⟩ := H ((hW _).2 hw) ((hN _ _ _).2 hn) ((hR _ _ _).2 hr)
    exact ⟨o, (hRS _ _ _).1 h1, (hN _ _ _).1 h2⟩
  · intro H _ _ _ _ hw hn hr
    obtain ⟨o, h1, h2⟩ := H ((hW _).1 hw) ((hN _ _ _).1 hn) ((hR _ _ _).1 hr)
    exact ⟨o, (hRS _ _ _).2 h1, (hN _ _ _).2 h2⟩

/-- **The negative form, which is the one the verdict uses.**  A refuted confluence statement
stays refuted under any *inert* change of ingredients — in particular under enlarging the
conversion relation by rules that cannot fire. -/
theorem not_crSchema_of_inert {W W' : List VExpr → Prop}
    {N N' RS RS' R R' : List VExpr → VExpr → VExpr → Prop}
    (hW : ∀ Γ, W Γ ↔ W' Γ)
    (hN : ∀ Γ a b, N Γ a b ↔ N' Γ a b)
    (hRS : ∀ Γ a b, RS Γ a b ↔ RS' Γ a b)
    (hR : ∀ Γ a b, R Γ a b ↔ R' Γ a b)
    (h : ¬ CRSchema W N RS R) : ¬ CRSchema W' N' RS' R' :=
  fun H => h ((crSchema_congr hW hN hRS hR).2 H)

/-! ## §2 The descent, with its relations abstracted

`VEnv.DescendStatement`'s ingredients, counted: a conversion (`NormalEq`), a multi-step
reduction (`ParRedS`), a typing judgment (`HasType env univs`), and the *syntactic* pieces
`Pattern.Matches` / `VLevel.WF` / `OnCtx`, which do not mention any of the three relations at
all.  So the layer is polymorphic in exactly **three** ingredients — that is the answer to "how
much of the statement changes when the relation changes", and it is `rfl`-checked below. -/

/-- `VEnv.DescentLam` with the three relation ingredients abstracted. -/
def DescentLamP (N RS H : List VExpr → VExpr → VExpr → Prop) (univs : Nat) :
    Nat → (Γ : List VExpr) → (q : Pattern) → VExpr → VExpr →
    (q.LPath → List VLevel) → (q.Path → VExpr) → Prop
  | 0, Γ, q, g, _, n1, n2 =>
    ∃ t n1' n, RS Γ g t ∧ q.Matches t n1' n ∧
      (∀ lp, List.Forall₂ (· ≈ ·) (n1' lp) (n1 lp)) ∧
      (∀ lp, ∀ l ∈ n1' lp, VLevel.WF univs l) ∧
      (∀ lp, ∀ l ∈ n1 lp, VLevel.WF univs l) ∧
      (∀ x, N Γ (n x) (n2 x))
  | k+1, Γ, q, g, g', n1, n2 =>
    ∃ A e B, RS Γ g (.lam A e) ∧ H Γ g' (.forallE A B) ∧
      DescentLamP N RS H univs k (A::Γ) (.var q) e (.app g'.lift (.bvar 0)) n1
        (fun x => x.elim (.bvar 0) fun y => (n2 y).lift)

/-- `VEnv.DescentOut`, likewise. -/
def DescentOutP (N RS H : List VExpr → VExpr → VExpr → Prop) (univs : Nat)
    (Γ : List VExpr) (q : Pattern) (g g' : VExpr)
    (n1 : q.LPath → List VLevel) (n2 : q.Path → VExpr) : Prop :=
  (∃ k, DescentLamP N RS H univs k Γ q g g' n1 n2) ∨
  (∃ P, H Γ P (.sort .zero) ∧ H Γ g P ∧ H Γ g' P)

/-- `Lean4Lean.DescendStatement`, likewise — and note the `NormalEq` premise is the *only*
negative occurrence of the conversion relation, which is why §5's transport needs an `Iff` and
not merely an implication. -/
def DescendStatementP (N RS H : List VExpr → VExpr → VExpr → Prop) (univs : Nat)
    (Ty : List VExpr → VExpr → Prop) : Prop :=
  ∀ (N₀ : Nat) {g : VExpr}, sizeOf g ≤ N₀ →
    ∀ {Γ : List VExpr} {q : Pattern} {g' : VExpr}
      {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
      OnCtx Γ Ty → N Γ g g' → q.Matches g' n1 n2 →
      DescentOutP N RS H univs Γ q g g' n1 n2

namespace VEnv

section
variable [Params]
open Params

/-- **Anti-strawman check for §2, part 1.**  `DescentLamP` at the real three ingredients is
`VEnv.DescentLam`, pointwise at every `k`. -/
theorem descentLamP_iff :
    ∀ (k : Nat) (Γ : List VExpr) (q : Pattern) (g g' : VExpr)
      (n1 : q.LPath → List VLevel) (n2 : q.Path → VExpr),
      DescentLamP NormalEq ParRedS (HasType env univs) univs k Γ q g g' n1 n2
        ↔ DescentLam k Γ q g g' n1 n2
  | 0, _, _, _, _, _, _ => Iff.rfl
  | k+1, Γ, q, g, g', n1, n2 => by
    simp only [DescentLamP, DescentLam]
    exact ⟨fun ⟨A, e, B, h1, h2, h3⟩ =>
        ⟨A, e, B, h1, h2, (descentLamP_iff k ..).1 h3⟩,
      fun ⟨A, e, B, h1, h2, h3⟩ => ⟨A, e, B, h1, h2, (descentLamP_iff k ..).2 h3⟩⟩

/-- **Anti-strawman check for §2, part 2.** -/
theorem descentOutP_iff {Γ : List VExpr} {q : Pattern} {g g' : VExpr}
    {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr} :
    DescentOutP NormalEq ParRedS (HasType env univs) univs Γ q g g' n1 n2
      ↔ DescentOut Γ q g g' n1 n2 :=
  or_congr (exists_congr fun k => descentLamP_iff k ..) Iff.rfl

end

end VEnv

/-- **Anti-strawman check for §2, part 3.**  `DescendStatementP` at the real ingredients is
`Lean4Lean.DescendStatement` — `NormalEq.descend`'s type, per
`Lean4Lean.descendStatement_holds`. -/
theorem descendStatementP_iff (I : VEnv.Params) :
    DescendStatementP (@VEnv.NormalEq I) (@VEnv.ParRedS I)
        (VEnv.HasType I.env I.univs) I.univs (VEnv.IsType I.env I.univs)
      ↔ DescendStatement I := by
  constructor
  · intro H N₀ _ hg _ _ _ _ _ hΓ hne hm
    exact VEnv.descentOutP_iff.1 (H N₀ hg hΓ hne hm)
  · intro H N₀ _ hg _ _ _ _ _ hΓ hne hm
    exact VEnv.descentOutP_iff.2 (H N₀ hg hΓ hne hm)

/-- `OnCtx` is congruent in its predicate.  (Not in `Theory/Typing/Lemmas.lean`; three lines.) -/
theorem onCtx_congr {P Q : List VExpr → VExpr → Prop} (h : ∀ Γ A, P Γ A ↔ Q Γ A) :
    ∀ Γ, OnCtx Γ P ↔ OnCtx Γ Q
  | [] => Iff.rfl
  | _::Γ => and_congr (onCtx_congr h Γ) (h ..)

/-- **The descent's transport lemma**, the §2 counterpart of `crSchema_congr`. -/
theorem descendStatementP_congr {N N' RS RS' H H' : List VExpr → VExpr → VExpr → Prop}
    {univs : Nat} {Ty Ty' : List VExpr → VExpr → Prop}
    (hN : ∀ Γ a b, N Γ a b ↔ N' Γ a b)
    (hRS : ∀ Γ a b, RS Γ a b ↔ RS' Γ a b)
    (hH : ∀ Γ a b, H Γ a b ↔ H' Γ a b)
    (hTy : ∀ Γ a, Ty Γ a ↔ Ty' Γ a) :
    DescendStatementP N RS H univs Ty ↔ DescendStatementP N' RS' H' univs Ty' := by
  have hlam : ∀ (k : Nat) Γ (q : Pattern) g g' n1 n2,
      DescentLamP N RS H univs k Γ q g g' n1 n2
        ↔ DescentLamP N' RS' H' univs k Γ q g g' n1 n2 := by
    intro k
    induction k with
    | zero =>
      intro Γ q g g' n1 n2
      simp only [DescentLamP]
      exact exists_congr fun t => exists_congr fun n1' => exists_congr fun n =>
        and_congr (hRS ..) (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
          (and_congr Iff.rfl (forall_congr' fun x => hN ..)))))
    | succ k ih =>
      intro Γ q g g' n1 n2
      simp only [DescentLamP]
      exact exists_congr fun A => exists_congr fun e => exists_congr fun B =>
        and_congr (hRS ..) (and_congr (hH ..) (ih ..))
  have hout : ∀ Γ (q : Pattern) g g' n1 n2,
      DescentOutP N RS H univs Γ q g g' n1 n2
        ↔ DescentOutP N' RS' H' univs Γ q g g' n1 n2 := by
    intro Γ q g g' n1 n2
    exact or_congr (exists_congr fun k => hlam k ..)
      (exists_congr fun P => and_congr (hH ..) (and_congr (hH ..) (hH ..)))
  constructor
  · intro H N₀ _ hg _ _ _ _ _ hΓ hne hm
    exact (hout ..).1 (H N₀ hg ((onCtx_congr (fun _ _ => hTy ..) _).2 hΓ)
      ((hN ..).2 hne) hm)
  · intro H N₀ _ hg _ _ _ _ _ hΓ hne hm
    exact (hout ..).2 (H N₀ hg ((onCtx_congr (fun _ _ => hTy ..) _).1 hΓ)
      ((hN ..).1 hne) hm)

/-! ## §3 The fourteenth constructor is inert at a defeq-free environment

`VEnv.IsStructureG.not_of_no_defeqs` (`Theory/Typing/EtaGuardLand.lean`, hole-free) says an
environment with no `defeqs` holds no structure: `IsStructureG.decl` puts the block's ι-rules
into the environment.  So at such an environment **both** the `extra` constructor and the new
`structEta` constructor are dead, and `IsDefEqSE` collapses onto `IsDefEq` pointwise.

This is not a curiosity.  It is the fact that separates the two jobs, because `refEnv` —
the witness against `NormalEq.descend` — is exactly such an environment
(`Lean4Lean.refEnv_no_defeqs`). -/

namespace VEnv

/-- The structure-eta *site*: `VEnv.StructEtaG`'s premises bundled, over the extended relation.
Bundling them is what makes §4's two new `NormalEqSE` rules and one new `ParRedSE` rule
readable, and it gives the inertness fact a single name. -/
structure StructEtaSite (env : VEnv) (univs : Nat) (Γ : List VExpr) (S : Lean.Name)
    (D : VInductDecl') (j : Nat) (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps : List VExpr) (e : VExpr) : Prop where
  isStruct : env.IsStructureG S D j T C
  indices : T.indices = []
  recFields : C.recFields = []
  nuvars : us.length = D.uvars
  levelWF : ∀ l ∈ us, l.WF univs
  np : ps.length = D.np
  args : env.HasArgsSE univs Γ (D.params.map (VExpr.instL us)) ps
  typed : env.IsDefEqSE univs Γ e e ((VExpr.const S us).mkApp ps)
  small : D.isLE = true ∨ ∀ k, k < C.fields.length →
    (C.fields.getD k default).lvl.inst us ≈ .zero

/-- **The site is unsatisfiable at a defeq-free environment.** -/
theorem StructEtaSite.not_of_no_defeqs {env : VEnv} {univs : Nat}
    (hd : ∀ df, ¬ env.defeqs df) {Γ S D j T C us ps e} :
    ¬ StructEtaSite env univs Γ S D j T C us ps e :=
  fun h => IsStructureG.not_of_no_defeqs hd h.isStruct

/-- `VEnv.IsDefEqU` over the extended relation; `ParRedSE.extra`'s `Check` obligation. -/
def IsDefEqSEU (env : VEnv) (U : Nat) (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  ∃ A, env.IsDefEqSE U Γ e₁ e₂ A

mutual

/-- **The fourteenth constructor is dead where there are no rules.**  Thirteen cases map
across one-for-one; `extra` dies on `hd`, `structEta` dies on
`IsStructureG.not_of_no_defeqs`. -/
theorem IsDefEqSE.toIsDefEq_of_no_defeqs {env : VEnv} {U : Nat} (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} (H : env.IsDefEqSE U Γ e₁ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ A :=
  match H with
  | .bvar h => .bvar h
  | .symm h => .symm (h.toIsDefEq_of_no_defeqs hd)
  | .trans h₁ h₂ => .trans (h₁.toIsDefEq_of_no_defeqs hd) (h₂.toIsDefEq_of_no_defeqs hd)
  | .sortDF h1 h2 h3 => .sortDF h1 h2 h3
  | .constDF h1 h2 h3 h4 h5 => .constDF h1 h2 h3 h4 h5
  | .appDF h₁ h₂ => .appDF (h₁.toIsDefEq_of_no_defeqs hd) (h₂.toIsDefEq_of_no_defeqs hd)
  | .lamDF h₁ h₂ => .lamDF (h₁.toIsDefEq_of_no_defeqs hd) (h₂.toIsDefEq_of_no_defeqs hd)
  | .forallEDF h₁ h₂ =>
    .forallEDF (h₁.toIsDefEq_of_no_defeqs hd) (h₂.toIsDefEq_of_no_defeqs hd)
  | .defeqDF h₁ h₂ => .defeqDF (h₁.toIsDefEq_of_no_defeqs hd) (h₂.toIsDefEq_of_no_defeqs hd)
  | .beta h₁ h₂ => .beta (h₁.toIsDefEq_of_no_defeqs hd) (h₂.toIsDefEq_of_no_defeqs hd)
  | .eta h => .eta (h.toIsDefEq_of_no_defeqs hd)
  | .proofIrrel h₁ h₂ h₃ =>
    .proofIrrel (h₁.toIsDefEq_of_no_defeqs hd) (h₂.toIsDefEq_of_no_defeqs hd)
      (h₃.toIsDefEq_of_no_defeqs hd)
  | .extra h1 _ _ => absurd h1 (hd _)
  | .structEta hS .. => absurd hS (IsStructureG.not_of_no_defeqs hd)

theorem HasArgsSE.toHasArgs_of_no_defeqs {env : VEnv} {U : Nat} (hd : ∀ df, ¬ env.defeqs df)
    {Γ As as : List VExpr} (H : env.HasArgsSE U Γ As as) : env.HasArgs U Γ As as :=
  match H with
  | .nil => .nil
  | .cons h t => .cons (h.toIsDefEq_of_no_defeqs hd) (t.toHasArgs_of_no_defeqs hd)

end

/-- **The collapse, as an `Iff`** — the direction the transport lemmas of §1–§2 consume.
`IsDefEq.toSE` is `Theory/Typing/StructEtaPrice.lean`'s embedding. -/
theorem isDefEqSE_iff_of_no_defeqs {env : VEnv} {U : Nat} (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ A : VExpr} :
    env.IsDefEqSE U Γ e₁ e₂ A ↔ env.IsDefEq U Γ e₁ e₂ A :=
  ⟨fun h => h.toIsDefEq_of_no_defeqs hd, IsDefEq.toSE⟩

/-- …and for the untyped form. -/
theorem isDefEqSEU_iff_of_no_defeqs {env : VEnv} {U : Nat} (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ : VExpr} :
    env.IsDefEqSEU U Γ e₁ e₂ ↔ env.IsDefEqU U Γ e₁ e₂ :=
  exists_congr fun _ => isDefEqSE_iff_of_no_defeqs hd

end VEnv

/-! ## §4 The whole confluence layer, re-erected — and inert at the same environments

This is the section the hypothesis under test needs.  `NormalEqSE` is `VEnv.NormalEq` with
every typing premise moved to `IsDefEqSE` **and two structure-eta rules added**; `ParRedSE` is
`VEnv.ParRed` likewise, with a structure-eta *reduction* added.  These are the relations the
rebuild would be over.

The two theorems that matter are `normalEqSE_iff_of_no_defeqs` and `parRedSE_iff_of_no_defeqs`:
at a defeq-free environment the re-erected relations are **pointwise equal to the old ones**.
Not "conservative over", not "contains" — equal. -/

namespace VEnv

section
variable [Params]
open Params

/-- `VEnv.HasType` over the extended relation. -/
def HasTypeSE (Γ : List VExpr) (e A : VExpr) : Prop := IsDefEqSE env univs Γ e e A

/-- **`VEnv.NormalEq` re-erected over `IsDefEqSE`, with structure eta.**  Constructors one to
nine are `NormalEq`'s verbatim with `HasType`/`IsDefEq` replaced by their `SE` forms;
`structEtaL`/`structEtaR` are the new pair, shaped after `etaL`/`etaR` — peel the η-expansion
on one side and continue. -/
inductive NormalEqSE : List VExpr → VExpr → VExpr → Prop where
  | refl : HasTypeSE Γ e A → NormalEqSE Γ e e
  | sortDF : l₁.WF univs → l₂.WF univs → l₁ ≈ l₂ → NormalEqSE Γ (.sort l₁) (.sort l₂)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) → (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
    NormalEqSE Γ (.const c ls) (.const c ls')
  | appDF :
    HasTypeSE Γ f₁ (.forallE A B) → HasTypeSE Γ f₂ (.forallE A B) →
    HasTypeSE Γ a₁ A → HasTypeSE Γ a₂ A →
    NormalEqSE Γ f₁ f₂ → NormalEqSE Γ a₁ a₂ →
    NormalEqSE Γ (.app f₁ a₁) (.app f₂ a₂)
  | lamDF :
    IsDefEqSE env univs Γ A A₁ (.sort u) → IsDefEqSE env univs Γ A A₂ (.sort u) →
    NormalEqSE (A::Γ) body₁ body₂ →
    NormalEqSE Γ (.lam A₁ body₁) (.lam A₂ body₂)
  | forallEDF :
    IsDefEqSE env univs Γ A A₁ (.sort u) → NormalEqSE Γ A₁ A₂ →
    HasTypeSE (A::Γ) B₁ (.sort v) → NormalEqSE (A::Γ) B₁ B₂ →
    NormalEqSE Γ (.forallE A₁ B₁) (.forallE A₂ B₂)
  | etaL :
    HasTypeSE Γ e' (.forallE A B) →
    NormalEqSE (A::Γ) e (.app e'.lift (.bvar 0)) →
    NormalEqSE Γ (.lam A e) e'
  | etaR :
    HasTypeSE Γ e' (.forallE A B) →
    NormalEqSE (A::Γ) (.app e'.lift (.bvar 0)) e →
    NormalEqSE Γ e' (.lam A e)
  | proofIrrel {p h h' : VExpr} :
    HasTypeSE Γ p (.sort .zero) → HasTypeSE Γ h p → HasTypeSE Γ h' p →
    NormalEqSE Γ h h'
  /-- **New.**  Peel a structure η-expansion on the left. -/
  | structEtaL :
    StructEtaSite env univs Γ S D j T C us ps e →
    NormalEqSE Γ (D.etaExpansionG T C us ps j e) e₂ →
    NormalEqSE Γ e e₂
  /-- **New.**  Peel a structure η-expansion on the right. -/
  | structEtaR :
    StructEtaSite env univs Γ S D j T C us ps e →
    NormalEqSE Γ e₁ (D.etaExpansionG T C us ps j e) →
    NormalEqSE Γ e₁ e

/-- **`VEnv.ParRed` re-erected**, with structure η as a reduction step — the shape a rebuilt
reduction relation has to have if the conversion relation gains the rule (otherwise the new
`NormalEqSE` rule has no reduct to descend to, which is `descend`'s original disease). -/
inductive ParRedSE : List VExpr → VExpr → VExpr → Prop where
  | bvar : ParRedSE Γ (.bvar i) (.bvar i)
  | sort : ParRedSE Γ (.sort u) (.sort u)
  | const : ParRedSE Γ (.const c ls) (.const c ls)
  | app : ParRedSE Γ f f' → ParRedSE Γ a a' → ParRedSE Γ (.app f a) (.app f' a')
  | lam : ParRedSE Γ A A' → ParRedSE (A::Γ) body body' →
    ParRedSE Γ (.lam A body) (.lam A' body')
  | forallE : ParRedSE Γ A A' → ParRedSE (A::Γ) B B' →
    ParRedSE Γ (.forallE A B) (.forallE A' B')
  | beta : ParRedSE (A::Γ) e₁ e₁' → ParRedSE Γ e₂ e₂' →
    ParRedSE Γ (.app (.lam A e₁) e₂) (e₁'.inst e₂')
  | extra {p : Pattern} {r : p.RHS × p.Check} {e : VExpr}
      {m1 : p.LPath → List VLevel} {m2 m2' : p.Path → VExpr} :
    Params.Pat p r → p.Matches e m1 m2 → r.2.OK (IsDefEqSEU env univs Γ) m1 m2 →
    (∀ a, ParRedSE Γ (m2 a) (m2' a)) → ParRedSE Γ e (r.1.apply m1 m2')
  /-- **New.**  Oriented as a **contraction**, `η e ⟶ e`; see `Theory/Typing/EtaOrient.lean`
  for why (rigidity at the atoms becomes unconditional, and the `sizeOf` measure kills the
  regress) and `Theory/Typing/CRSEScope.lean` §2/§4 for the two statements that pay for it.
  Flipped 2026-09-04; before that it read `ParRedSE Γ e (D.etaExpansionG T C us ps j e)`. -/
  | structEta :
    StructEtaSite env univs Γ S D j T C us ps e →
    ParRedSE Γ (D.etaExpansionG T C us ps j e) e

/-- The reflexive-transitive closure, as `VEnv.ParRedS` is. -/
def ParRedSES (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRedSE Γ)

/-- `HasTypeSE` is `HasType` at a defeq-free environment. -/
theorem hasTypeSE_iff_of_no_defeqs (hd : ∀ df, ¬ env.defeqs df) {Γ : List VExpr} {e A : VExpr} :
    HasTypeSE Γ e A ↔ HasType env univs Γ e A :=
  isDefEqSE_iff_of_no_defeqs hd

/-- **The re-erected conversion relation is the old one**, at a defeq-free environment.  Both
new rules die on `StructEtaSite.not_of_no_defeqs`; the other nine transport premise-by-premise
through §3. -/
theorem normalEqSE_iff_of_no_defeqs (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ : VExpr} :
    NormalEqSE Γ e₁ e₂ ↔ NormalEq Γ e₁ e₂ := by
  constructor
  · intro H
    induction H with
    | refl h => exact .refl (h.toIsDefEq_of_no_defeqs hd)
    | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
    | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
    | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
      exact .appDF (h1.toIsDefEq_of_no_defeqs hd) (h2.toIsDefEq_of_no_defeqs hd)
        (h3.toIsDefEq_of_no_defeqs hd) (h4.toIsDefEq_of_no_defeqs hd) ih1 ih2
    | lamDF h1 h2 _ ih =>
      exact .lamDF (h1.toIsDefEq_of_no_defeqs hd) (h2.toIsDefEq_of_no_defeqs hd) ih
    | forallEDF h1 _ h3 _ ih1 ih2 =>
      exact .forallEDF (h1.toIsDefEq_of_no_defeqs hd) ih1 (h3.toIsDefEq_of_no_defeqs hd) ih2
    | etaL h _ ih => exact .etaL (h.toIsDefEq_of_no_defeqs hd) ih
    | etaR h _ ih => exact .etaR (h.toIsDefEq_of_no_defeqs hd) ih
    | proofIrrel h1 h2 h3 =>
      exact .proofIrrel (h1.toIsDefEq_of_no_defeqs hd) (h2.toIsDefEq_of_no_defeqs hd)
        (h3.toIsDefEq_of_no_defeqs hd)
    | structEtaL hs _ _ => exact absurd hs (StructEtaSite.not_of_no_defeqs hd)
    | structEtaR hs _ _ => exact absurd hs (StructEtaSite.not_of_no_defeqs hd)
  · intro H
    induction H with
    | refl h => exact .refl h.toSE
    | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
    | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
    | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
      exact .appDF h1.toSE h2.toSE h3.toSE h4.toSE ih1 ih2
    | lamDF h1 h2 _ ih => exact .lamDF h1.toSE h2.toSE ih
    | forallEDF h1 _ h3 _ ih1 ih2 => exact .forallEDF h1.toSE ih1 h3.toSE ih2
    | etaL h _ ih => exact .etaL h.toSE ih
    | etaR h _ ih => exact .etaR h.toSE ih
    | proofIrrel h1 h2 h3 => exact .proofIrrel h1.toSE h2.toSE h3.toSE

/-- **The re-erected reduction relation is the old one**, at a defeq-free environment. -/
theorem parRedSE_iff_of_no_defeqs (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ : VExpr} :
    ParRedSE Γ e₁ e₂ ↔ ParRed Γ e₁ e₂ := by
  constructor
  · intro H
    induction H with
    | bvar => exact .bvar
    | sort => exact .sort
    | const => exact .const
    | app _ _ ih1 ih2 => exact .app ih1 ih2
    | lam _ _ ih1 ih2 => exact .lam ih1 ih2
    | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
    | beta _ _ ih1 ih2 => exact .beta ih1 ih2
    | extra r1 r2 r3 _ ih =>
      exact .extra r1 r2 (r3.map fun _ _ h => (isDefEqSEU_iff_of_no_defeqs hd).1 h) ih
    | structEta hs => exact absurd hs (StructEtaSite.not_of_no_defeqs hd)
  · intro H
    induction H with
    | bvar => exact .bvar
    | sort => exact .sort
    | const => exact .const
    | app _ _ ih1 ih2 => exact .app ih1 ih2
    | lam _ _ ih1 ih2 => exact .lam ih1 ih2
    | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
    | beta _ _ ih1 ih2 => exact .beta ih1 ih2
    | extra r1 r2 r3 _ ih =>
      exact .extra r1 r2 (r3.map fun _ _ h => (isDefEqSEU_iff_of_no_defeqs hd).2 h) ih

/-- …and so is its closure. -/
theorem parRedSES_iff_of_no_defeqs (hd : ∀ df, ¬ env.defeqs df)
    {Γ : List VExpr} {e₁ e₂ : VExpr} :
    ParRedSES Γ e₁ e₂ ↔ ParRedS Γ e₁ e₂ := by
  constructor
  · intro H
    induction H with
    | rfl => exact .rfl
    | tail _ h ih => exact ih.tail ((parRedSE_iff_of_no_defeqs hd).1 h)
  · intro H
    induction H with
    | rfl => exact .rfl
    | tail _ h ih => exact ih.tail ((parRedSE_iff_of_no_defeqs hd).2 h)

end

end VEnv

/-! ## §5 The verdict: the re-erection is not the repair

Both false statements are now transported to the re-erected layer, by two different and
deliberately independent routes.

* **`descend` (§5.1)** — by *inertness*.  At `refEnv` the re-erected statement is the **same
  proposition**, so the hole-free trilemma refutes it verbatim.
* **`parRed` (§5.2)** — by *porting the argument*.  The refutation uses only `appDF`,
  `proofIrrel`, `extra` and rigidity, all of which `NormalEqSE`/`ParRedSE` have verbatim.  So
  this route needs **no** hypothesis about the environment at all: the statement is false over
  the extended relation for exactly the reason it is false over the old one. -/

namespace VEnv

section
variable [Params]
open Params

/-- `VEnv.IsType` over the extended relation. -/
def IsTypeSE (Γ : List VExpr) (A : VExpr) : Prop := ∃ u, HasTypeSE Γ A (.sort u)

theorem isTypeSE_iff_of_no_defeqs (hd : ∀ df, ¬ env.defeqs df) {Γ : List VExpr} {A : VExpr} :
    IsTypeSE Γ A ↔ IsType env univs Γ A :=
  exists_congr fun _ => hasTypeSE_iff_of_no_defeqs hd

protected theorem ParRedSE.rfl : ∀ {Γ : List VExpr} {e : VExpr}, ParRedSE Γ e e
  | _, .bvar .. => .bvar
  | _, .sort .. => .sort
  | _, .const .. => .const
  | _, .app .. => .app ParRedSE.rfl ParRedSE.rfl
  | _, .lam .. => .lam ParRedSE.rfl ParRedSE.rfl
  | _, .forallE .. => .forallE ParRedSE.rfl ParRedSE.rfl

/-- `VEnv.parRedS_rigid` (`Theory/Typing/KCanonical.lean`) over the extended relation. -/
theorem parRedSES_rigid {Γ : List VExpr} {e o : VExpr}
    (hrig : ∀ o, ParRedSE Γ e o → o = e) (H : ParRedSES Γ e o) : o = e := by
  induction H with
  | rfl => rfl
  | tail _ h ih => cases ih; exact hrig _ h

end

end VEnv

/-! ### §5.1 `descend` — transported by inertness -/

/-- **`Lean4Lean.DescendStatement` re-erected over the extended relation.**  Every one of the
three relation ingredients, plus the context predicate, moved to its `SE` form. -/
def DescendStatementSE (I : VEnv.Params) : Prop :=
  DescendStatementP (@VEnv.NormalEqSE I) (@VEnv.ParRedSES I) (@VEnv.HasTypeSE I) I.univs
    (@VEnv.IsTypeSE I)

/-- **The re-erected descent statement is the same proposition, at a defeq-free environment.** -/
theorem descendStatementSE_iff_of_no_defeqs (I : VEnv.Params)
    (hd : ∀ df, ¬ I.env.defeqs df) :
    DescendStatementSE I ↔ DescendStatement I :=
  (descendStatementP_congr
      (fun _ _ _ => VEnv.normalEqSE_iff_of_no_defeqs hd)
      (fun _ _ _ => VEnv.parRedSES_iff_of_no_defeqs hd)
      (fun _ _ _ => VEnv.hasTypeSE_iff_of_no_defeqs hd)
      (fun _ _ => VEnv.isTypeSE_iff_of_no_defeqs hd)).trans
    (descendStatementP_iff I)

/-- **`NormalEq.descend`'s statement stays refuted when the layer is re-erected over
`VEnv.IsDefEqSE`** — the trilemma of `Lean4Lean.descend_uniq_sortUniq_not_all`, verbatim, with
`DescendStatement` replaced by its re-erected form.

**This is the machine-checked answer to (a): the two are different jobs.**  Adding structure eta
to the conversion relation does not touch the reason `descend` fails, because at `refEnv` the
added rule cannot fire at all — `refEnv` has no `defeqs`, hence no structure
(`VEnv.IsStructureG.not_of_no_defeqs`).  The repair `descend` needs is on the *reduction* side
(`Theory/Typing/ParRedMissing.lean`'s proof-replacement step, or `KEta.lean`'s `ParRedK`); the
eta job is on the *conversion* side.  Opposite directions. -/
theorem descendSE_uniq_sortUniq_not_all :
    ¬ (DescendStatementSE refParams ∧ refEnv.SortUniq 0 ∧ refEnv.UniqTyping 0) := fun ⟨h, hsu, huq⟩ =>
  descend_uniq_sortUniq_not_all
    ⟨(descendStatementSE_iff_of_no_defeqs refParams fun _ => refEnv_no_defeqs).1 h, hsu, huq⟩

/-! ### §5.2 `parRed` — transported by porting the argument -/

namespace VEnv

section
variable [Params]
open Params

/-- **`VEnv.ParRedStatement` re-erected**, as a `CRSchema` instance. -/
def ParRedStatementSE : Prop :=
  CRSchema (fun Γ => OnCtx Γ IsTypeSE) NormalEqSE ParRedSES ParRedSE

/-- **A registered rule with a `Prop`-typed major premise refutes the re-erected statement too.**

`VEnv.not_parRedStatement_of_propMajor` (`Theory/Typing/ParRedPropRefute.lean`) ported line for
line.  Note what is *not* used: no hypothesis on `env.defeqs`, no inertness, nothing about
structures.  The four moves the proof makes — `NormalEqSE.appDF`, `NormalEqSE.proofIrrel`,
`ParRedSE.extra`, rigidity — are all available in the extended relation verbatim, which is
precisely why the eta extension is irrelevant to this defect. -/
theorem not_parRedStatementSE_of_propMajor
    {Γ : List VExpr} {p₁ p₂ : Pattern}
    {r : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f a b A B : VExpr} {m1 m2}
    (hΓ : OnCtx Γ IsTypeSE)
    (r1 : Params.Pat (.app p₁ p₂) r)
    (r2 : (Pattern.app p₁ p₂).Matches (.app f b) m1 m2)
    (r3 : r.2.OK (IsDefEqSEU env univs Γ) m1 m2)
    (hf : HasTypeSE Γ f (.forallE A B))
    (hA : HasTypeSE Γ A (.sort .zero))
    (ha : HasTypeSE Γ a A) (hb : HasTypeSE Γ b A)
    (hrig : ∀ o, ParRedSE Γ (.app f a) o → o = .app f a)
    (hne : ¬ NormalEqSE Γ (.app f a) (Pattern.RHS.apply m1 m2 r.1)) :
    ¬ ParRedStatementSE := by
  intro H
  have h1 : NormalEqSE Γ (.app f a) (.app f b) :=
    .appDF hf hf ha hb (.refl hf) (.proofIrrel hA ha hb)
  have h2 : ParRedSE Γ (.app f b) (Pattern.RHS.apply m1 m2 r.1) :=
    .extra r1 r2 r3 fun _ => ParRedSE.rfl
  obtain ⟨o, ho, hno⟩ := H hΓ h1 h2
  cases parRedSES_rigid hrig ho
  exact hne hno

end

end VEnv

/-! ## §6 The two jobs' witnesses are disjoint

§5 says the eta extension does not repair the confluence defects.  §6 says the converse: the
environments where the eta rule has anything to do are **not** the environments where the
confluence statements are refuted.  The two facts together are what "two jobs" means. -/

namespace VEnv

/-- **Where the eta rule can fire, there are rules; where there are no rules, it cannot.**
This is `StructEtaSite.not_of_no_defeqs` read as a dichotomy, and it is the reason §5.1 works. -/
theorem exists_defeq_of_structEtaSite {env : VEnv} {univs Γ S D j T C us ps e}
    (h : StructEtaSite env univs Γ S D j T C us ps e) : ∃ df, env.defeqs df := by
  by_contra hc
  exact StructEtaSite.not_of_no_defeqs (fun df hdf => hc ⟨df, hdf⟩) h

end VEnv

/-- **At `refEnv` — the witness against `descend` — there is no structure at all**, so the eta
job has nothing to do there. -/
theorem refEnv_no_structEtaSite {univs Γ S D j T C us ps e} :
    ¬ VEnv.StructEtaSite refEnv univs Γ S D j T C us ps e :=
  VEnv.StructEtaSite.not_of_no_defeqs fun _ => refEnv_no_defeqs

/-- The same at `VEnv.ncPropEnv`, the brief's other ready-made well-formed environment. -/
theorem ncPropEnv_no_structEtaSite {univs Γ S D j T C us ps e} :
    ¬ VEnv.StructEtaSite VEnv.ncPropEnv univs Γ S D j T C us ps e :=
  VEnv.StructEtaSite.not_of_no_defeqs fun _ h => h

/-- …and hence the extended relation *is* the old relation at both of them. -/
theorem refEnv_isDefEqSE_iff {U Γ e₁ e₂ A} :
    refEnv.IsDefEqSE U Γ e₁ e₂ A ↔ refEnv.IsDefEq U Γ e₁ e₂ A :=
  VEnv.isDefEqSE_iff_of_no_defeqs fun _ => refEnv_no_defeqs

theorem ncPropEnv_isDefEqSE_iff {U Γ e₁ e₂ A} :
    VEnv.ncPropEnv.IsDefEqSE U Γ e₁ e₂ A ↔ VEnv.ncPropEnv.IsDefEq U Γ e₁ e₂ A :=
  VEnv.isDefEqSE_iff_of_no_defeqs fun _ h => h

/-! ## §7 Vacuity: the transport is not about a relation that relates nothing

`docs/vacuity-ledger.md` §0, applied here.  A confluence statement true only where no reduction
happens is worthless, and an inertness result about a relation that relates nothing is worthless
too.  Both are checked at `refEnv`, which is `VEnv.WF` (`Lean4Lean.refEnv_wf`). -/

/-- **`NormalEqSE` relates two distinct terms at `refEnv`** — `Lean4Lean.refNormalEq`'s pair,
transported.  So §5.1's inertness is not inertness of an empty relation. -/
theorem refEnv_normalEqSE_fires : @VEnv.NormalEqSE refParams refCtx refG refG' :=
  (@VEnv.normalEqSE_iff_of_no_defeqs refParams (fun _ => refEnv_no_defeqs) _ _ _).2 refNormalEq

/-- **`ParRedSE` performs a real reduction at `refEnv`**, with distinct endpoints: a β-step.
`refEnv` has no `defeqs`, so this is the *only* kind of step available there — which is exactly
why it has to be exhibited rather than assumed. -/
theorem refEnv_parRedSE_beta :
    @VEnv.ParRedSE refParams refCtx
      (.app (.lam (.const `P []) (.bvar 0)) (.const `D [])) (.const `D []) := by
  let i : VEnv.Params := refParams
  exact @VEnv.ParRedSE.beta i _ _ _ _ _ _ VEnv.ParRedSE.rfl VEnv.ParRedSE.rfl

/-- …and the two endpoints of that step are different terms, so the reduction is not the
identity. -/
theorem refEnv_parRedSE_beta_nontrivial :
    (VExpr.app (.lam (.const `P []) (.bvar 0)) (.const `D [])) ≠ (VExpr.const `D []) := by
  intro h; cases h

/-- **`ParRedSES` is likewise non-trivial**, so §4's closure transport is not about the
identity relation either. -/
theorem refEnv_parRedSES_beta :
    @VEnv.ParRedSES refParams refCtx
      (.app (.lam (.const `P []) (.bvar 0)) (.const `D [])) (.const `D []) :=
  .tail .rfl refEnv_parRedSE_beta

/-! ## §8 The axiom sweep, inline

`docs/handoff-confluence.md` §6.3: the axiom sweep is a design instrument, not a formality, and
`KDescend.lean` asserted "`sorry`-free" three times about a declaration that carried `sorryAx`.
So every declaration of this file is swept here, in the file, where the claim cannot go stale.

Expected: everything is `sorryAx`-free.  The one place a hole could enter is
`descendSE_uniq_sortUniq_not_all`, which composes with `Lean4Lean.descend_uniq_sortUniq_not_all`
— itself hole-free — and **not** with `not_descendStatement_of_wf`, which is tainted.  That
choice is deliberate and the sweep is what proves it was honoured. -/

#print axioms Lean4Lean.VEnv.crSchema_eq_parRedStatement
#print axioms Lean4Lean.crSchema_congr
#print axioms Lean4Lean.not_crSchema_of_inert
#print axioms Lean4Lean.VEnv.descentLamP_iff
#print axioms Lean4Lean.VEnv.descentOutP_iff
#print axioms Lean4Lean.descendStatementP_iff
#print axioms Lean4Lean.onCtx_congr
#print axioms Lean4Lean.descendStatementP_congr
#print axioms Lean4Lean.VEnv.StructEtaSite.not_of_no_defeqs
#print axioms Lean4Lean.VEnv.IsDefEqSE.toIsDefEq_of_no_defeqs
#print axioms Lean4Lean.VEnv.HasArgsSE.toHasArgs_of_no_defeqs
#print axioms Lean4Lean.VEnv.isDefEqSE_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.isDefEqSEU_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.hasTypeSE_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.normalEqSE_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.parRedSE_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.parRedSES_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.isTypeSE_iff_of_no_defeqs
#print axioms Lean4Lean.VEnv.ParRedSE.rfl
#print axioms Lean4Lean.VEnv.parRedSES_rigid
#print axioms Lean4Lean.descendStatementSE_iff_of_no_defeqs
#print axioms Lean4Lean.descendSE_uniq_sortUniq_not_all
#print axioms Lean4Lean.VEnv.not_parRedStatementSE_of_propMajor
#print axioms Lean4Lean.VEnv.exists_defeq_of_structEtaSite
#print axioms Lean4Lean.refEnv_no_structEtaSite
#print axioms Lean4Lean.ncPropEnv_no_structEtaSite
#print axioms Lean4Lean.refEnv_isDefEqSE_iff
#print axioms Lean4Lean.ncPropEnv_isDefEqSE_iff
#print axioms Lean4Lean.refEnv_normalEqSE_fires
#print axioms Lean4Lean.refEnv_parRedSE_beta
#print axioms Lean4Lean.refEnv_parRedSE_beta_nontrivial
#print axioms Lean4Lean.refEnv_parRedSES_beta

end Lean4Lean
