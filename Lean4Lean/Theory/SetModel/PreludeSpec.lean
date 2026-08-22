import Lean4Lean.Theory.SetModel.Cnst

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
-/

end Lean4Lean.SetModel
