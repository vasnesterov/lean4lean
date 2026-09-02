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


/-! ### The two recursor values the witness needs

`eqIndDecl` and `iffIndDecl` are **large** eliminators, so their recursors' types are not
propositions at an instantiation with a nonzero elimination universe and the assignment cannot
give them `•`.  The values it must give instead are built here, from `mkLam`/`mkForallType`/
`mkForallProp` and the three denotations above and nothing else.  They were developed in
`EqRecLarge.lean` §§1--3 and `IffRecLarge.lean` §§1--3 and are **relocated** here so that
`preludeWitness` -- which `PreludeOracle.lean` uses byte for byte as its oracle -- can mention
them; see `docs/handoff-setmodel.md` §22.5 for the measurement that this needs no new import. -/

-- from `EqRecLarge.lean` §1
section Combinators

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mkFamUnion_ext {G G' : V → V} {hG : ℒₛₑₜ-function₁[V] G} {hG' : ℒₛₑₜ-function₁[V] G'}
    {F F' : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {hF' : ℒₛₑₜ-function₂[V] F'}
    {ρ ρ' : V} (hdom : G' ρ' = G ρ) (h : ∀ v ∈ G ρ, F' ρ' v = F ρ v) :
    mkFamUnion G' hG' F' hF' ρ' = mkFamUnion G hG F hF ρ := by
  rw [mem_ext_iff]
  intro y
  rw [mem_mkFamUnion_iff, mem_mkFamUnion_iff, hdom]
  exact exists_congr fun v ↦ and_congr_right fun hv ↦ by rw [h v hv]

/-- **`mkForallType` is determined by its domain set and its fibres on it.**  The analogue of
`UnitAudit.mkLam_ext`, and the lemma that lets the oracle's own spelling of the motive's type
be identified with `interp`'s. -/
theorem mkForallType_ext {G G' : V → V} {hG : ℒₛₑₜ-function₁[V] G} {hG' : ℒₛₑₜ-function₁[V] G'}
    {F F' : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {hF' : ℒₛₑₜ-function₂[V] F'}
    {ρ ρ' : V} (hdom : G' ρ' = G ρ) (h : ∀ v ∈ G ρ, F' ρ' v = F ρ v) :
    mkForallType G' hG' F' hF' ρ' = mkForallType G hG F hF ρ := by
  have hFU : mkFamUnion G' hG' F' hF' ρ' = mkFamUnion G hG F hF ρ :=
    mkFamUnion_ext (hG := hG) (hG' := hG') (hF := hF) (hF' := hF') hdom h
  rw [mem_ext_iff]
  intro f
  rw [mem_mkForallType_iff, mem_mkForallType_iff, hFU, hdom]
  refine and_congr_right fun _ ↦ forall_congr' fun v ↦ imp_congr_right fun hv ↦ ?_
  rw [h v hv]

end Combinators

-- from `EqRecLarge.lean` §2
section Definable

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `ρ ↦ E ‘ (ρ ‘ i) ‘ (ρ ‘ j) ‘ (ρ ‘ k)` — the shape of `⟦Eq α a b⟧` read out of a valuation. -/
theorem eqAt_definable (E : V) (i j k : ℕ) :
    ℒₛₑₜ-function₁[V]
      (fun ρ ↦ ((E ‘ (ρ ‘ ((i : ℕ) : V))) ‘ (ρ ‘ ((j : ℕ) : V))) ‘ (ρ ‘ ((k : ℕ) : V))) := by
  definability

theorem eqAt_definable₂ (E : V) (i j k : ℕ) :
    ℒₛₑₜ-function₂[V]
      (fun (ρ _ : V) ↦
        ((E ‘ (ρ ‘ ((i : ℕ) : V))) ‘ (ρ ‘ ((j : ℕ) : V))) ‘ (ρ ‘ ((k : ℕ) : V))) := by
  definability

/-- `ρ ↦ (ρ ‘ i) ‘ (ρ ‘ j) ‘ •` — the shape of `⟦motive a (Eq.refl α a)⟧`. -/
theorem minAt_definable (i j : ℕ) :
    ℒₛₑₜ-function₁[V]
      (fun ρ ↦ ((ρ ‘ ((i : ℕ) : V)) ‘ (ρ ‘ ((j : ℕ) : V))) ‘ (pt : V)) := by
  definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem const_definable₂ (X : V) : ℒₛₑₜ-function₂[V] (fun (_ _ : V) ↦ X) := by definability

end Definable

-- from `EqRecLarge.lean` §3
section Value

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- The `motive` binder's domain, spelled **without** `interp`: `Π x ∈ α, Π w ∈ ⟦Eq α a x⟧, U κ nu`.
Read at `snoc (snoc ∅ α) a`. -/
noncomputable def motSet (κ : ℕ → V) (nu nv : ℕ) : V → V :=
  mkForallType (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _)
    (fun ρ x ↦
      mkForallType
        (fun σ ↦ (((eqFn κ nv) ‘ (σ ‘ ((0 : ℕ) : V))) ‘ (σ ‘ ((1 : ℕ) : V))) ‘ (σ ‘ ((2 : ℕ) : V)))
        (eqAt_definable _ 0 1 2) (fun _ _ ↦ U κ nu) (const_definable₂ _) (snoc ρ x))
    (by
      have := mkForallType_definable
        (V := V)
        (fun σ ↦ (((eqFn κ nv) ‘ (σ ‘ ((0 : ℕ) : V))) ‘ (σ ‘ ((1 : ℕ) : V))) ‘ (σ ‘ ((2 : ℕ) : V)))
        (eqAt_definable _ 0 1 2) (fun _ _ ↦ U κ nu) (const_definable₂ _)
      definability)

theorem motSet_definable (κ : ℕ → V) (nu nv : ℕ) : ℒₛₑₜ-function₁[V] (motSet κ nu nv) :=
  mkForallType_definable _ _ _ _

/-- Layer 6: `λ (h : Eq α a b), m`. -/
noncomputable def lamH (κ : ℕ → V) (nv : ℕ) : V → V :=
  mkLam
    (fun ρ ↦ (((eqFn κ nv) ‘ (ρ ‘ ((0 : ℕ) : V))) ‘ (ρ ‘ ((1 : ℕ) : V))) ‘ (ρ ‘ ((4 : ℕ) : V)))
    (eqAt_definable _ 0 1 4) (fun ρ _ ↦ ρ ‘ ((3 : ℕ) : V)) (value_definable₂ _)

theorem lamH_definable (κ : ℕ → V) (nv : ℕ) : ℒₛₑₜ-function₁[V] (lamH κ nv) :=
  mkLam_definable _ _ _ _

/-- Layer 5: `λ (b : α), λ (h : Eq α a b), m`. -/
noncomputable def lamB (κ : ℕ → V) (nv : ℕ) : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _) (fun ρ b ↦ lamH κ nv (snoc ρ b))
    (by have := lamH_definable (V := V) κ nv; definability)

theorem lamB_definable (κ : ℕ → V) (nv : ℕ) : ℒₛₑₜ-function₁[V] (lamB κ nv) :=
  mkLam_definable _ _ _ _

/-- Layer 4: `λ (m : motive a (Eq.refl α a)), …`.  Its domain is `(f ‘ a) ‘ •`, which is what
`EqZeroAudit.interp_minTyE_val` computes the minor premise's type to be. -/
noncomputable def lamM (κ : ℕ → V) (nv : ℕ) : V → V :=
  mkLam (fun ρ ↦ ((ρ ‘ ((2 : ℕ) : V)) ‘ (ρ ‘ ((1 : ℕ) : V))) ‘ (pt : V)) (minAt_definable 2 1)
    (fun ρ m ↦ lamB κ nv (snoc ρ m)) (by have := lamB_definable (V := V) κ nv; definability)

theorem lamM_definable (κ : ℕ → V) (nv : ℕ) : ℒₛₑₜ-function₁[V] (lamM κ nv) :=
  mkLam_definable _ _ _ _

/-- Layer 3: `λ (motive : ∀ x : α, Eq α a x → Sort u), …`. -/
noncomputable def lamF (κ : ℕ → V) (nu nv : ℕ) : V → V :=
  mkLam (motSet κ nu nv) (motSet_definable κ nu nv) (fun ρ f ↦ lamM κ nv (snoc ρ f))
    (by have := lamM_definable (V := V) κ nv; definability)

theorem lamF_definable (κ : ℕ → V) (nu nv : ℕ) : ℒₛₑₜ-function₁[V] (lamF κ nu nv) :=
  mkLam_definable _ _ _ _

/-- Layer 2: `λ (a : α), …`. -/
noncomputable def lamA (κ : ℕ → V) (nu nv : ℕ) : V → V :=
  mkLam (fun ρ ↦ ρ ‘ ((0 : ℕ) : V)) (value_definable _) (fun ρ a ↦ lamF κ nu nv (snoc ρ a))
    (by have := lamF_definable (V := V) κ nu nv; definability)

theorem lamA_definable (κ : ℕ → V) (nu nv : ℕ) : ℒₛₑₜ-function₁[V] (lamA κ nu nv) :=
  mkLam_definable _ _ _ _

/-- **The value the oracle must hand `Eq.rec` once the elimination universe is not `Prop`.**
`nu` is `u.eval ls`, `nv` is `v.eval ls`. -/
noncomputable def eqRecFn (κ : ℕ → V) (nu nv : ℕ) : V :=
  mkLam (fun _ ↦ U κ nv) (by definability) (fun ρ α ↦ lamA κ nu nv (snoc ρ α))
    (by have := lamA_definable (V := V) κ nu nv; definability) ∅

end Value

-- from `IffRecLarge.lean` §1
section Combinators

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- **`mkForallProp` is determined by its domain set and its fibres on it.** -/
theorem mkForallProp_ext {G G' : V → V} {hG : ℒₛₑₜ-function₁[V] G} {hG' : ℒₛₑₜ-function₁[V] G'}
    {F F' : V → V → V} {hF : ℒₛₑₜ-function₂[V] F} {hF' : ℒₛₑₜ-function₂[V] F'}
    {ρ ρ' : V} (hdom : G' ρ' = G ρ) (h : ∀ v ∈ G ρ, F' ρ' v = F ρ v) :
    mkForallProp G' hG' F' hF' ρ' = mkForallProp G hG F hF ρ := by
  rw [mem_ext_iff]
  intro z
  rw [mem_mkForallProp_iff, mem_mkForallProp_iff, hdom]
  exact and_congr_right fun _ ↦ forall_congr' fun v ↦ imp_congr_right fun hv ↦ by rw [h v hv]

end Combinators

-- from `IffRecLarge.lean` §2
section Definable

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `ρ ↦ I ‘ (ρ ‘ i) ‘ (ρ ‘ j)` — the shape of `⟦Iff a b⟧` read out of a valuation. -/
theorem iffAt_definable (I : V) (i j : ℕ) :
    ℒₛₑₜ-function₁[V] (fun ρ ↦ (I ‘ (ρ ‘ ((i : ℕ) : V))) ‘ (ρ ‘ ((j : ℕ) : V))) := by
  definability

/-- `ρ ↦ (ρ ‘ i) ‘ •` — the shape of `⟦motive (Iff.intro a b mp mpr)⟧`: the constructor
application is a proof, so `interp` discards all four arguments and the motive is applied to `•`. -/
theorem appPt_definable₂ (i : ℕ) :
    ℒₛₑₜ-function₂[V] (fun (ρ _ : V) ↦ (ρ ‘ ((i : ℕ) : V)) ‘ (pt : V)) := by definability

/-- `ρ ↦ (ρ ‘ i) ‘ • ‘ •` — the innermost layer's body: the minor premise applied to the two
field values, both of which are `•`. -/
theorem minAppPt_definable₂ (i : ℕ) :
    ℒₛₑₜ-function₂[V] (fun (ρ _ : V) ↦ ((ρ ‘ ((i : ℕ) : V)) ‘ (pt : V)) ‘ (pt : V)) := by
  definability

end Definable

-- from `IffRecLarge.lean` §3
section Value

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- `⟦a → b⟧` written **without** `interp`: the impredicative `∀` from `ρ ‘ i` to `ρ ‘ j`.
`i = 0, j = 1` is `mp`'s type read at `snoc³ ∅ a b f`; `i = 1, j = 0` is `mpr`'s. -/
noncomputable def impSet (i j : ℕ) : V → V :=
  mkForallProp (fun ρ ↦ ρ ‘ ((i : ℕ) : V)) (value_definable _)
    (fun ρ _ ↦ ρ ‘ ((j : ℕ) : V)) (value_definable₂ _)

theorem impSet_definable (i j : ℕ) : ℒₛₑₜ-function₁[V] (impSet (V := V) i j) :=
  mkForallProp_definable _ _ _ _

/-- **The minor premise's domain, as the oracle spells it**: `Π mp ∈ ⟦a → b⟧, Π mpr ∈ ⟦b → a⟧,
f ‘ •`.  Read at `snoc³ ∅ a b f`.  Two nested `mkForallType`s whose *domains* are `mkForallProp`s
— the shape with no counterpart in `EqRecLarge.lean`. -/
noncomputable def minSet : V → V :=
  mkForallType (impSet 0 1) (impSet_definable 0 1)
    (fun ρ mp ↦
      mkForallType (impSet 1 0) (impSet_definable 1 0)
        (fun σ _ ↦ (σ ‘ ((2 : ℕ) : V)) ‘ (pt : V)) (appPt_definable₂ 2) (snoc ρ mp))
    (by
      have := mkForallType_definable (V := V) (impSet 1 0) (impSet_definable 1 0)
        (fun σ _ ↦ (σ ‘ ((2 : ℕ) : V)) ‘ (pt : V)) (appPt_definable₂ 2)
      definability)

theorem minSet_definable : ℒₛₑₜ-function₁[V] (minSet (V := V)) :=
  mkForallType_definable _ _ _ _

/-- The motive binder's domain, spelled without `interp`: `Π x ∈ ⟦Iff a b⟧, U κ nu`.  **One**
`mkForallType`, not `Eq`'s nested pair, because `iffIndDecl` has no index.  Read at
`snoc² ∅ a b`. -/
noncomputable def motSetI (κ : ℕ → V) (nu : ℕ) : V → V :=
  mkForallType (fun ρ ↦ ((iffFn : V) ‘ (ρ ‘ ((0 : ℕ) : V))) ‘ (ρ ‘ ((1 : ℕ) : V)))
    (iffAt_definable _ 0 1) (fun _ _ ↦ U κ nu) (const_definable₂ _)

theorem motSetI_definable (κ : ℕ → V) (nu : ℕ) : ℒₛₑₜ-function₁[V] (motSetI (V := V) κ nu) :=
  mkForallType_definable _ _ _ _

/-- Layer 5: `λ (h : Iff a b), min • •`. -/
noncomputable def lamHI : V → V :=
  mkLam (fun ρ ↦ ((iffFn : V) ‘ (ρ ‘ ((0 : ℕ) : V))) ‘ (ρ ‘ ((1 : ℕ) : V)))
    (iffAt_definable _ 0 1)
    (fun ρ _ ↦ ((ρ ‘ ((3 : ℕ) : V)) ‘ (pt : V)) ‘ (pt : V)) (minAppPt_definable₂ 3)

theorem lamHI_definable : ℒₛₑₜ-function₁[V] (lamHI (V := V)) := mkLam_definable _ _ _ _

/-- Layer 4: `λ (min : ∀ mp mpr, motive (Iff.intro a b mp mpr)), λ h, min • •`. -/
noncomputable def lamNI : V → V :=
  mkLam minSet minSet_definable (fun ρ m ↦ lamHI (snoc ρ m))
    (by have := lamHI_definable (V := V); definability)

theorem lamNI_definable : ℒₛₑₜ-function₁[V] (lamNI (V := V)) := mkLam_definable _ _ _ _

/-- Layer 3: `λ (motive : Iff a b → Sort u), …`. -/
noncomputable def lamFI (κ : ℕ → V) (nu : ℕ) : V → V :=
  mkLam (motSetI κ nu) (motSetI_definable κ nu) (fun ρ f ↦ lamNI (snoc ρ f))
    (by have := lamNI_definable (V := V); definability)

theorem lamFI_definable (κ : ℕ → V) (nu : ℕ) : ℒₛₑₜ-function₁[V] (lamFI (V := V) κ nu) :=
  mkLam_definable _ _ _ _

/-- Layer 2: `λ (b : Prop), …`.  Its domain is `U κ 0`, **not** `U κ n`: both of `Iff.rec`'s
parameters range over `Prop`. -/
noncomputable def lamBI (κ : ℕ → V) (nu : ℕ) : V → V :=
  mkLam (fun _ ↦ U κ 0) (by definability) (fun ρ b ↦ lamFI κ nu (snoc ρ b))
    (by have := lamFI_definable (V := V) κ nu; definability)

theorem lamBI_definable (κ : ℕ → V) (nu : ℕ) : ℒₛₑₜ-function₁[V] (lamBI (V := V) κ nu) :=
  mkLam_definable _ _ _ _

/-- **The value the oracle must hand `Iff.rec` once the elimination universe is not `Prop`.**
`nu` is `u.eval ls`; there is no second level, because `iffIndDecl.recUvars = 1`. -/
noncomputable def iffRecFn (κ : ℕ → V) (nu : ℕ) : V :=
  mkLam (fun _ ↦ U κ 0) (by definability) (fun ρ a ↦ lamBI κ nu (snoc ρ a))
    (by have := lamBI_definable (V := V) κ nu; definability) ∅

end Value

section RecVals
variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]

/-- **`Eq.rec`'s entry, both level slices in one value** (`EqRecLarge.lean` §9, relocated).  `•` on
the `Prop` branch, where the recursor's type *is* a proposition; `eqRecFn` otherwise. -/
noncomputable def eqRecVal (κ : ℕ → V) (ls : List ℕ) : List VLevel → V
  | [u, v] => if u.eval ls = 0 then (pt : V) else eqRecFn κ (u.eval ls) (v.eval ls)
  | _ => ∅

/-- **`Iff.rec`'s entry, both level slices in one value** (`IffRecLarge.lean` §13, relocated).
One level, not two, because `iffIndDecl.recUvars = 1`. -/
noncomputable def iffRecVal (κ : ℕ → V) (ls : List ℕ) : List VLevel → V
  | [u] => if u.eval ls = 0 then (pt : V) else iffRecFn κ (u.eval ls)
  | _ => ∅

theorem eqRecVal_pair (κ : ℕ → V) (ls : List ℕ) (u v : VLevel) :
    eqRecVal (V := V) κ ls [u, v]
      = if u.eval ls = 0 then (pt : V) else eqRecFn κ (u.eval ls) (v.eval ls) := rfl

theorem iffRecVal_single (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    iffRecVal (V := V) κ ls [u] = if u.eval ls = 0 then (pt : V) else iffRecFn κ (u.eval ls) :=
  rfl

end RecVals
/-! ### The joint witness

One `ModelData` meeting all three at once.  Stating them separately would leave
open the failure mode that has bitten this development three times: each
conjunct fine alone, the conjunction unsatisfiable. -/

/-- The assignment: `Eq`, `Iff` and `Nonempty` get their intended denotations, the two large
eliminators `Eq.rec` and `Iff.rec` get the values §"the two recursor values" builds, and every
other name gets `∅`.

**Why the cascade branches on `n` alone**, with each arm a *function* of `us`, rather than the
more obvious `fun n us ↦ if … then …`: in the applied form, an *untaken* arm's body mentions `us`,
so a `rfl` between two instances at different level lists makes the kernel compare
`eqRecVal κ ls us` with `eqRecVal κ ls us'` before it reduces the `ite` — and that descent into
`eqRecFn`'s six `mkLam` layers costs ≈4·10⁵ heartbeats, twice the default budget, so the
declaration elaborates, prints clean axioms, and is then refused with `(kernel) deterministic
timeout`.  In this form no untaken arm mentions `us`, the comparison is syntactic, and every cell
below is `rfl` again.  Measured in `docs/handoff-setmodel.md` §22. -/
noncomputable def preludeWitness (κ : ℕ → V) (ls : List ℕ) : ModelData V where
  κ := κ
  ls := ls
  cnst := fun n ↦
    if n = ``Eq then (fun us ↦ match us with | [w] => eqFn κ (w.eval ls) | _ => ∅)
    else if n = ``Iff then (fun us ↦ match us with | [] => (iffFn : V) | _ => ∅)
    else if n = ``Nonempty then (fun us ↦ match us with | [w] => nonemptyFn κ (w.eval ls) | _ => ∅)
    else if n = ``Eq.rec then eqRecVal κ ls
    else if n = ``Iff.rec then iffRecVal κ ls
    else fun _ ↦ ∅

/-- **The pre-repair assignment, preserved as a negative control.**  Identical to
`preludeWitness` except that `Eq.rec` and `Iff.rec` fall through to `∅ = •`.  It is kept because
the theorems that give the repair its content are of the form "the repaired value is in the
interpretation of the recursor's type and *this* one is not"; repairing `preludeWitness` in place
would otherwise delete the object those theorems discriminate against.  It meets all three
specifications (`preludeWitnessPt_eq`/`_iff`/`_nonempty`) and agrees with `preludeWitness` at all
three type-formers (`preludeWitness_agree_Eq`/`_Iff`/`_Nonempty`, all `rfl`), so it differs *only*
at the two recursor cells. -/
noncomputable def preludeWitnessPt (κ : ℕ → V) (ls : List ℕ) : ModelData V where
  κ := κ
  ls := ls
  cnst := fun n ↦
    if n = ``Eq then (fun us ↦ match us with | [w] => eqFn κ (w.eval ls) | _ => ∅)
    else if n = ``Iff then (fun us ↦ match us with | [] => (iffFn : V) | _ => ∅)
    else if n = ``Nonempty then (fun us ↦ match us with | [w] => nonemptyFn κ (w.eval ls) | _ => ∅)
    else fun _ ↦ ∅

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

/-! ### The assignment's cells, all `rfl`

Every one of these is what a downstream file needs in order to rewrite `interp_const`'s output.
They are `rfl` at the η-contracted shape; at the applied shape the sixth would need an arm lemma
and a `rw` (see `docs/handoff-setmodel.md` §22.4). -/

theorem preludeWitness_cnst_Eq (κ : ℕ → V) (ls : List ℕ) (w : VLevel) :
    (preludeWitness κ ls).cnst ``Eq [w] = eqFn κ (w.eval ls) := rfl

theorem preludeWitness_cnst_Iff (κ : ℕ → V) (ls : List ℕ) :
    (preludeWitness κ ls).cnst ``Iff [] = (iffFn : V) := rfl

theorem preludeWitness_cnst_Nonempty (κ : ℕ → V) (ls : List ℕ) (w : VLevel) :
    (preludeWitness κ ls).cnst ``Nonempty [w] = nonemptyFn κ (w.eval ls) := rfl

theorem preludeWitness_cnst_eqRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitness κ ls).cnst ``Eq.rec us = eqRecVal κ ls us := rfl

theorem preludeWitness_cnst_iffRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitness κ ls).cnst ``Iff.rec us = iffRecVal κ ls us := rfl

theorem preludeWitness_cnst_neRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitness κ ls).cnst ``Nonempty.rec us = (pt : V) := rfl

/-- **The congruence the `Eq` type-former cell needs, with the degenerate branch by `rfl`.**  This
is the proof that hits `(kernel) deterministic timeout` if the cascade is written in the applied
shape. -/
theorem preludeWitness_congr_Eq (κ : ℕ → V) (ls : List ℕ) {us us' : List VLevel}
    (hd : List.Forall₂ (· ≈ ·) us us') :
    (preludeWitness κ ls).cnst ``Eq us = (preludeWitness κ ls).cnst ``Eq us' := by
  rcases hd with _ | ⟨h, ht⟩
  · rfl
  rcases ht with _ | ⟨h2, ht2⟩
  · rw [preludeWitness_cnst_Eq, preludeWitness_cnst_Eq, VLevel.equiv_def.mp h ls]
  · rfl

/-- `∅` off the five names the assignment sets.  The `Eq.rec`/`Iff.rec` hypotheses are the two the
repair forces, and `PreludeOracle.lean`'s one consumer can supply them. -/
theorem preludeWitness_cnst_empty (κ : ℕ → V) (ls : List ℕ) {m : Name}
    (h1 : m ≠ ``Eq) (h2 : m ≠ ``Iff) (h3 : m ≠ ``Nonempty)
    (h4 : m ≠ ``Eq.rec) (h5 : m ≠ ``Iff.rec) (us : List VLevel) :
    (preludeWitness κ ls).cnst m us = (∅ : V) := by
  simp [preludeWitness, h1, h2, h3, h4, h5]

/-! ### The negative control, and that it is a legitimate one -/

theorem preludeWitnessPt_eq (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    EqSpec (preludeWitnessPt κ ls) u := fun _ hα _ ha _ hb ↦ eqFn_value hα ha hb

theorem preludeWitnessPt_iff (κ : ℕ → V) (ls : List ℕ) :
    IffSpec (preludeWitnessPt κ ls) := fun _ hp _ hq ↦ iffFn_value hp hq

theorem preludeWitnessPt_nonempty (κ : ℕ → V) (ls : List ℕ) (u : VLevel) :
    NonemptySpec (preludeWitnessPt κ ls) u := fun _ hα ↦ nonemptyFn_value hα

theorem preludeWitnessPt_cnst_eqRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessPt κ ls).cnst ``Eq.rec us = (pt : V) := by
  simp [preludeWitnessPt, pt]

theorem preludeWitnessPt_cnst_iffRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessPt κ ls).cnst ``Iff.rec us = (pt : V) := by
  simp [preludeWitnessPt, pt]

theorem preludeWitnessPt_cnst_neRec (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitnessPt κ ls).cnst ``Nonempty.rec us = (pt : V) := by
  simp [preludeWitnessPt, pt]

theorem preludeWitness_agree_Eq (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitness κ ls).cnst ``Eq us = (preludeWitnessPt κ ls).cnst ``Eq us := rfl

theorem preludeWitness_agree_Iff (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitness κ ls).cnst ``Iff us = (preludeWitnessPt κ ls).cnst ``Iff us := rfl

theorem preludeWitness_agree_Nonempty (κ : ℕ → V) (ls : List ℕ) (us : List VLevel) :
    (preludeWitness κ ls).cnst ``Nonempty us = (preludeWitnessPt κ ls).cnst ``Nonempty us := rfl

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
