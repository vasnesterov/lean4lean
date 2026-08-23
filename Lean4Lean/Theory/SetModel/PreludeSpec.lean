import Lean4Lean.Theory.SetModel.Cnst
import Lean4Lean.Theory.SetModel.Definability

/-!
# What the `.induct` oracle owes the standard axioms

**These are statements, not theorems.** Nothing here is proved, and nothing here
is assumed: each is a `Prop`-valued definition, so this file is a specification
that the inductive interpretation will have to meet, written down before that
interpretation is built rather than after.

## Why this file exists

`Theory/Consistency.lean` insists the prelude pin the *genuine* declarations of
`Eq`, `Iff` and `Nonempty` rather than constants of the right type, because the
standard axioms are sound only for the standard meanings of those names. That
same fact reappears on the model side, and it is sharper than it looks: the
three standard axioms' obligations are **not** statements about the universe
hierarchy, they are statements about the denotations of three inductives.

| primitive | constants in its type |
|---|---|
| `Quot` | — |
| `Quot.mk` | `Quot` |
| `Quot.lift` | `Eq`, `Quot` |
| `Quot.ind` | `Quot`, `Quot.mk` |
| `quotDefEq` (its `type`) | `Eq` |
| `propext` | `Iff`, `Eq` |
| `Classical.choice` | `Nonempty` |
| `Quot.sound` | `Eq`, `Quot`, `Quot.mk` |

`Quot` is the only primitive whose type mentions nothing else.

So `propext`'s obligation is *not* `propext_of_mem_UProp` — "truth values are
extensional", proved in `SetModel/Universe.lean`. That is the core of the
argument but not its content: the content is `IffSpec` and `EqSpec` below, and
`propext_of_mem_UProp` is what will be used to *prove* `IffSpec`.

## How the applications unfold

Each specification is stated on `M.cnst` applied by the model's internal
function application `‘`, and that is the right form: `interp` sends
`.app f a` to `⟦f⟧ ρ ‘ ⟦a⟧ ρ` unless `f` is a proof, and none of the partial
applications here is one. `Eq α a : α → Prop` has sort `imax u 1 = max u 1 ≥ 1`,
and likewise for the others, so every application is the value branch.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open scoped Classical

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`Eq`.**  `Eq.{u} : ∀ (α : Sort u) (a : α) (b : α), Prop` — in
`eqIndDecl` the first two arguments are parameters and the third is the index,
so the denotation is a three-fold internal function.

A `Prop` denotes a member of `℘{•}`, so the only question is which of the two
truth values, and the answer is set-theoretic equality of the two elements.

*Level check.*  At `u.eval = 0` the domain `α` is a member of `UProp`, hence a
subset of `{•}`, so `a` and `b` are both `•` and the equation says `{•}` — which
is right, since a `Prop` has at most one proof.  No side condition is needed. -/
def EqSpec (M : ModelData V) (u : VLevel) : Prop :=
  ∀ α ∈ U M.κ (u.eval M.ls), ∀ a ∈ α, ∀ b ∈ α,
    (((M.cnst ``Eq [u]) ‘ α) ‘ a) ‘ b = (if a = b then ({pt} : V) else ∅)

/-- **`Iff`.**  `Iff : Prop → Prop → Prop`, with no universe parameters
(`iffIndDecl.uvars = 0`), so the denotation is indexed by the empty level list.

`Iff p q` is inhabited exactly when `p` and `q` are the same truth value, and
since both are members of `℘{•} = {∅, {•}}` that is exactly `p = q`.  This is
the statement that carries propositional extensionality; proving it is where
`propext_of_mem_UProp` is spent. -/
def IffSpec (M : ModelData V) : Prop :=
  ∀ p ∈ (UProp : V), ∀ q ∈ (UProp : V),
    ((M.cnst ``Iff []) ‘ p) ‘ q = (if p = q then ({pt} : V) else ∅)

/-- **`Nonempty`.**  `Nonempty.{u} : ∀ (α : Sort u), Prop`.

Note that this one is a genuine *squash*: `Nonempty.intro` takes a field
`val : α` which is not a proof, so the stage-built inductive would be a set of
tuples, and the `Prop`-valued interpretation has to collapse it to a truth
value.  That is sound precisely because `nonemptyIndDecl.isLE = false` — it is a
small eliminator, so nothing can be read back out.  Contrast `Eq` and `Iff`,
which are large eliminators and are collapsed too, but harmlessly, because they
are subsingletons to begin with. -/
def NonemptySpec (M : ModelData V) (u : VLevel) : Prop :=
  ∀ α ∈ U M.κ (u.eval M.ls),
    (M.cnst ``Nonempty [u]) ‘ α = (if α = ∅ then (∅ : V) else ({pt} : V))

/-! ## What each axiom consumes

**`propext : ∀ {a b : Prop}, (a ↔ b) → a = b`.**  Its obligation is
`• ∈ ⟦propext's type⟧ ∅`, which by `pt_mem_interp_forallE_prop` reduces to: for
all `a b ∈ UProp` and every `h ∈ ⟦a ↔ b⟧`, `• ∈ ⟦@Eq Prop a b⟧`.  `IffSpec`
turns the existence of `h` into `a = b`; `EqSpec (.succ .zero)` — note the
level, since `@Eq` here is applied at `α := Prop = Sort 0`, which lives in
`Sort 1` — then gives `{•}`.  The instance needed is `α := UProp`, which is a
member of `U κ 1` by `U_mem_succ`.

**`Classical.choice : {α : Sort u} → Nonempty α → α`.**  By
`mkLam_mem_interp_forallE`, a definable function taking `α ∈ U κ u` and a proof
to an element of `α`.  `NonemptySpec` turns the proof's existence into `α ≠ ∅`,
and `exists_choiceFunction_mem_U` supplies the selection.  This is the one
axiom whose obligation needs the chain — it is `i < n` and `𝗔𝗖`.

**`Quot.sound`** additionally needs the `Quot` interpretation, so it is not
specified here; it belongs with `Quot`.

## Status of each statement

All three are believed true and none needed a side condition, which is worth
recording explicitly because the check was the point of writing them down.  The
level analysis in `EqSpec`'s docstring is the only place a degenerate case had
to be inspected, and it comes out consistent rather than needing a guard.

**And all three are now *witnessed*, below.**  That is not decoration.  A
specification nothing has had to satisfy is exactly the shape that can be
quietly unsatisfiable, and a development that discharges obligations *against*
it is then conditional on nothing.  `Quot.lift`'s and `quotDefEq`'s obligations
are stated against `EqSpec`, so until something met it, that whole cone rested
on an unexamined hypothesis.  It is met, jointly, by an explicit `ModelData`.
-/

/-! ## The specifications are satisfiable

The witness is deliberately built **without** a `LevelAssign`: that structure
was itself found unsatisfiable once and repaired, so building the prelude
witnesses on top of it would reproduce the hole this section exists to close.
Everything below needs only `κ`, `ls`, and `𝗭𝗙`.

The witness is also checked to *do work*.  Each specification's value is an
`if`, and a witness that only ever exercised one branch would say very little;
`eqFn_refl`/`eqFn_distinct` and their analogues pin both branches at concrete
instances. -/

section Witness

/-! ### Internal sequences, without a `LevelAssign`

The raw form of `interpCtx_domain`'s conclusion. -/

/-- `ρ` is an internal sequence of length `n`. -/
def IsSeq (ρ : V) (n : ℕ) : Prop := IsFunction ρ ∧ domain ρ = ((n : ℕ) : V)

theorem isSeq_empty : IsSeq (∅ : V) 0 := ⟨IsFunction.empty, by simp [zero_def]⟩

theorem IsSeq.snoc' {ρ v : V} {n : ℕ} (h : IsSeq ρ n) : IsSeq (snoc ρ v) (n + 1) := by
  obtain ⟨hfun, hdom⟩ := h
  have hni : domain ρ ∉ domain ρ := mem_irrefl _
  refine ⟨IsFunction.insert ρ _ v hni, ?_⟩
  rw [snoc, domain_insert, hdom]
  simp [num_succ_def, succ]

theorem IsSeq.read_lt {ρ v : V} {n j : ℕ} (h : IsSeq ρ n) (hj : j < n) :
    (snoc ρ v) ‘ ((j : ℕ) : V) = ρ ‘ ((j : ℕ) : V) :=
  snoc_value_lt h.1 (by rw [h.2]; exact ofNat_mem_ofNat hj)

theorem IsSeq.read_top {ρ v : V} {n : ℕ} (h : IsSeq ρ n) :
    (snoc ρ v) ‘ ((n : ℕ) : V) = v := by rw [← h.2]; exact snoc_value_top h.1

/-! ### `Eq` -/

theorem eqFibB_definable :
    ℒₛₑₜ-function₂[V] (fun ρ b ↦ if ρ ‘ ((1 : ℕ) : V) = b then ({pt} : V) else ∅) := by
  suffices ℒₛₑₜ-relation₃[V]
      (fun T ρ b ↦ T = if ρ ‘ ((1 : ℕ) : V) = b then ({pt} : V) else ∅) by exact this
  have e : ∀ T ρ b : V,
      (T = if ρ ‘ ((1 : ℕ) : V) = b then ({pt} : V) else ∅) ↔
        ∀ z, z ∈ T ↔ (z = pt ∧ ρ ‘ ((1 : ℕ) : V) = b) := by
    intro T ρ b
    rw [mem_ext_iff]
    by_cases h : ρ ‘ ((1 : ℕ) : V) = b
    · rw [if_pos h]; simp_all
    · rw [if_neg h]; simp_all
  simp only [e]
  definability

/-- The innermost λ: the truth value of `a = b`, with `a` read at index 1 and
the carrier at index 0.  Environment-passing, as `SetModel/Definability.lean`
requires — capturing `α` would break the composition one layer up. -/
noncomputable def eqFibB : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _)
    (fun ρ b ↦ if ρ ‘ ((1 : ℕ) : V) = b then ({pt} : V) else ∅) eqFibB_definable

theorem eqFibB_definable₁ : ℒₛₑₜ-function₁[V] (eqFibB (V := V)) := mkLam_definable _ _ _ _

noncomputable def eqFibA : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _)
    (fun ρ a ↦ eqFibB (snoc ρ a))
    (by have := eqFibB_definable₁ (V := V); definability)

theorem eqFibA_definable₁ : ℒₛₑₜ-function₁[V] (eqFibA (V := V)) := mkLam_definable _ _ _ _

/-- **`Eq`'s denotation at universe index `i`** — three nested λs. -/
noncomputable def eqFn (κ : ℕ → V) (i : ℕ) : V :=
  mkLam (fun _ ↦ U κ i) (by definability) (fun ρ α ↦ eqFibA (snoc ρ α))
    (by have := eqFibA_definable₁ (V := V); definability) ∅

theorem eqFn_value {κ : ℕ → V} {i : ℕ} {α a b : V}
    (hα : α ∈ U κ i) (ha : a ∈ α) (hb : b ∈ α) :
    (((eqFn κ i) ‘ α) ‘ a) ‘ b = (if a = b then ({pt} : V) else ∅) := by
  have hs1 : IsSeq (snoc (∅ : V) α) 1 := isSeq_empty.snoc'
  have h0 : (snoc (∅ : V) α) ‘ ((0 : ℕ) : V) = α := isSeq_empty.read_top
  have h0' : (snoc (snoc (∅ : V) α) a) ‘ ((0 : ℕ) : V) = α :=
    (hs1.read_lt (by omega)).trans h0
  have h1 : (snoc (snoc (∅ : V) α) a) ‘ ((1 : ℕ) : V) = a := hs1.read_top
  have v1 : (eqFn κ i) ‘ α = eqFibA (snoc ∅ α) := by unfold eqFn; exact mkLam_value hα
  have v2 : (eqFibA (snoc (∅ : V) α)) ‘ a = eqFibB (snoc (snoc ∅ α) a) := by
    unfold eqFibA; exact mkLam_value (by rw [h0]; exact ha)
  have v3 : (eqFibB (snoc (snoc (∅ : V) α) a)) ‘ b
      = if (snoc (snoc (∅ : V) α) a) ‘ ((1 : ℕ) : V) = b then ({pt} : V) else ∅ := by
    unfold eqFibB; exact mkLam_value (by rw [h0']; exact hb)
  rw [v1, v2, v3, h1]

/-! ### `Iff` -/

theorem iffFibQ_definable :
    ℒₛₑₜ-function₂[V] (fun ρ q ↦ if ρ ‘ ((0 : ℕ) : V) = q then ({pt} : V) else ∅) := by
  suffices ℒₛₑₜ-relation₃[V]
      (fun T ρ q ↦ T = if ρ ‘ ((0 : ℕ) : V) = q then ({pt} : V) else ∅) by exact this
  have e : ∀ T ρ q : V,
      (T = if ρ ‘ ((0 : ℕ) : V) = q then ({pt} : V) else ∅) ↔
        ∀ z, z ∈ T ↔ (z = pt ∧ ρ ‘ ((0 : ℕ) : V) = q) := by
    intro T ρ q
    rw [mem_ext_iff]
    by_cases h : ρ ‘ ((0 : ℕ) : V) = q
    · rw [if_pos h]; simp_all
    · rw [if_neg h]; simp_all
  simp only [e]
  definability

noncomputable def iffFibQ : V → V :=
  mkLam (fun _ ↦ (UProp : V)) (by definability)
    (fun ρ q ↦ if ρ ‘ ((0 : ℕ) : V) = q then ({pt} : V) else ∅) iffFibQ_definable

theorem iffFibQ_definable₁ : ℒₛₑₜ-function₁[V] (iffFibQ (V := V)) := mkLam_definable _ _ _ _

/-- **`Iff`'s denotation** — no universe parameters, two nested λs over
`UProp`. -/
noncomputable def iffFn : V :=
  mkLam (fun _ ↦ (UProp : V)) (by definability) (fun ρ p ↦ iffFibQ (snoc ρ p))
    (by have := iffFibQ_definable₁ (V := V); definability) ∅

theorem iffFn_value {p q : V} (hp : p ∈ (UProp : V)) (hq : q ∈ (UProp : V)) :
    ((iffFn : V) ‘ p) ‘ q = (if p = q then ({pt} : V) else ∅) := by
  have h0 : (snoc (∅ : V) p) ‘ ((0 : ℕ) : V) = p := isSeq_empty.read_top
  have v1 : (iffFn : V) ‘ p = iffFibQ (snoc ∅ p) := by unfold iffFn; exact mkLam_value hp
  have v2 : (iffFibQ (snoc (∅ : V) p)) ‘ q
      = if (snoc (∅ : V) p) ‘ ((0 : ℕ) : V) = q then ({pt} : V) else ∅ := by
    unfold iffFibQ; exact mkLam_value hq
  rw [v1, v2, h0]

/-! ### `Nonempty` -/

theorem nonemptyFib_definable :
    ℒₛₑₜ-function₂[V] (fun (_ α : V) ↦ if α = ∅ then (∅ : V) else ({pt} : V)) := by
  suffices ℒₛₑₜ-relation₃[V]
      (fun T (_ α : V) ↦ T = if α = ∅ then (∅ : V) else ({pt} : V)) by exact this
  have e : ∀ T α : V, (T = if α = ∅ then (∅ : V) else ({pt} : V)) ↔
      ∀ z, z ∈ T ↔ (z = pt ∧ ¬ α = ∅) := by
    intro T α
    rw [mem_ext_iff]
    by_cases h : α = ∅
    · rw [if_pos h]; simp_all
    · rw [if_neg h]; simp_all
  simp only [e]
  definability

/-- **`Nonempty`'s denotation at universe index `i`** — a genuine squash: the
stage-built inductive would be a set of tuples, and this collapses it to a truth
value.  Sound because `Nonempty` is a small eliminator. -/
noncomputable def nonemptyFn (κ : ℕ → V) (i : ℕ) : V :=
  mkLam (fun _ ↦ U κ i) (by definability)
    (fun _ α ↦ if α = ∅ then (∅ : V) else ({pt} : V)) nonemptyFib_definable ∅

theorem nonemptyFn_value {κ : ℕ → V} {i : ℕ} {α : V} (hα : α ∈ U κ i) :
    (nonemptyFn κ i) ‘ α = (if α = ∅ then (∅ : V) else ({pt} : V)) := by
  unfold nonemptyFn; exact mkLam_value hα

/-! ### The joint witness

One `ModelData` meeting all three at once.  Stating them separately would leave
open the failure mode that has bitten this development three times: each
conjunct fine alone, the conjunction unsatisfiable. -/

/-- The assignment: `Eq`, `Iff` and `Nonempty` get their intended denotations
and every other name gets `∅`. -/
noncomputable def preludeWitness (κ : ℕ → V) (ls : List ℕ) : ModelData V where
  κ := κ
  ls := ls
  cnst := fun n us ↦
    if n = ``Eq then (match us with | [w] => eqFn κ (w.eval ls) | _ => ∅)
    else if n = ``Iff then (match us with | [] => (iffFn : V) | _ => ∅)
    else if n = ``Nonempty then (match us with | [w] => nonemptyFn κ (w.eval ls) | _ => ∅)
    else ∅

theorem preludeWitness_eq (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    EqSpec (preludeWitness κ ls) u := fun _ hα _ ha _ hb ↦ eqFn_value hα ha hb

theorem preludeWitness_iff (κ : ℕ → V) (ls : List ℕ) :
    IffSpec (preludeWitness κ ls) := fun _ hp _ hq ↦ iffFn_value hp hq

theorem preludeWitness_nonempty (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    NonemptySpec (preludeWitness κ ls) u := fun _ hα ↦ nonemptyFn_value hα

/-- **The audit's conclusion: the three prelude specifications are jointly
satisfiable**, at every universe level and over an arbitrary chain and level
valuation. -/
theorem preludeSpec_satisfiable (κ : ℕ → V) (ls : List ℕ) :
    ∃ M : ModelData V, M.κ = κ ∧ M.ls = ls ∧
      (∀ u, EqSpec M u) ∧ IffSpec M ∧ (∀ u, NonemptySpec M u) :=
  ⟨preludeWitness κ ls, rfl, rfl, preludeWitness_eq κ ls,
    preludeWitness_iff κ ls, preludeWitness_nonempty κ ls⟩

/-! ### The witness does work: both branches fire

A witness whose `if` only ever took one branch would be nearly content-free. -/

/-- The `then` branch, at the bottom universe, where it is the *only* branch:
`U κ 0 = ℘{•}`, so every element of every carrier is `•`. -/
theorem eqFn_refl (κ : ℕ → V) : (((eqFn κ 0) ‘ ({pt} : V)) ‘ pt) ‘ pt = ({pt} : V) := by
  rw [eqFn_value (by rw [U_zero]; exact mem_UProp_iff.2 (by simp))
    (mem_singleton_iff.2 rfl) (mem_singleton_iff.2 rfl), if_pos rfl]

theorem empty_ne_singleton_pt : (∅ : V) ≠ ({pt} : V) :=
  fun h ↦ absurd (h ▸ mem_singleton_iff.2 (rfl : (pt : V) = pt)) (by simp)

/-- The `else` branch, at a level where two distinct elements exist: `UProp`
itself is a member of `U κ 1` and holds both `∅` and `{•}`. -/
theorem eqFn_distinct {n : ℕ} {κ : ℕ → V} (hκ : IsInaccessibleChain n κ) (h1 : 0 < n) :
    (((eqFn κ 1) ‘ (UProp : V)) ‘ ∅) ‘ ({pt} : V) = ∅ := by
  have hm : (UProp : V) ∈ U κ 1 := U_mem_succ hκ h1
  rw [eqFn_value hm (mem_UProp_iff.2 (by simp)) (mem_UProp_iff.2 (by simp)),
    if_neg empty_ne_singleton_pt]

theorem iffFn_same : ((iffFn : V) ‘ ∅) ‘ ∅ = ({pt} : V) := by
  rw [iffFn_value (mem_UProp_iff.2 (by simp)) (mem_UProp_iff.2 (by simp)), if_pos rfl]

theorem iffFn_diff : ((iffFn : V) ‘ ∅) ‘ ({pt} : V) = ∅ := by
  rw [iffFn_value (mem_UProp_iff.2 (by simp)) (mem_UProp_iff.2 (by simp)),
    if_neg empty_ne_singleton_pt]

theorem nonemptyFn_empty (κ : ℕ → V) : (nonemptyFn κ 0) ‘ (∅ : V) = ∅ := by
  rw [nonemptyFn_value (κ := κ) (i := 0) (by rw [U_zero]; exact mem_UProp_iff.2 (by simp)),
    if_pos rfl]

theorem nonemptyFn_inhabited (κ : ℕ → V) :
    (nonemptyFn κ 0) ‘ ({pt} : V) = ({pt} : V) := by
  rw [nonemptyFn_value (κ := κ) (i := 0)
    (by rw [U_zero]; exact mem_UProp_iff.2 (by simp)), if_neg]
  exact fun h ↦ empty_ne_singleton_pt h.symm

end Witness

end Lean4Lean.SetModel
