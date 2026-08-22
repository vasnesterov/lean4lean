import Lean4Lean.Theory.Typing.Env

/-!
# Statement of consistency for Lean's type theory

This file states (without proof) that the abstract type theory implemented by
`VEnv`/`VDecl.WF` is consistent: no environment built from the standard prelude
by axiom-free declaration steps types an inhabitant of `∀ p : Prop, p`.

## Design notes, for review

* "Lean TT" here means: the pure declaration steps (`def`, `opaque`, `example`,
  `mutualDef`, `induct`, `quot`) over the *standard prelude*, which consists of
  the genuine declarations of `Eq`, `Iff`, `Nonempty` plus the three standard
  axioms `propext`, `Quot.sound`, `Classical.choice`. This matches the theory
  studied in Carneiro's *The Type Theory of Lean* (2019).

* The prelude must pin the actual inductive *declarations* of `Eq`, `Iff` and
  `Nonempty`, not merely constants of the right type: the standard axioms are
  sound only for the standard meanings of these names (e.g. `propext` over a
  nonstandard `Eq` proves `False`).

* Arbitrary further `.axiom` steps are excluded by `VDecl.isAxiomFree`;
  everything else is allowed, since well-formedness (`VDecl.WF`) already
  requires each added declaration to typecheck.

* The false proposition is `∀ p : Prop, p` rather than a declared `False`
  constant, so that consistency does not depend on which inductives the
  environment happens to declare.

* The `.induct` case of `VDecl.WF` is `VInductDecl'.WF` / `VEnv.addInduct'`
  (`Lean4Lean.Theory.Inductive.Decl`), so the three prelude inductives below are
  given in the structured form that carries their parameter/index/field
  telescopes. Each is checked against Lean's own declaration by an
  `example … := rfl` immediately after it, so this file failing to build *is*
  that check failing.
-/

namespace Lean4Lean

open VExpr (mkPi)

/-! ## The standard prelude

The three inductive declarations are `VInductDecl'` literals: the flat
`VInductDecl` that used to live here stored only the block's closed types, from
which the recursor's telescopes are not recoverable (the kernel `whnf`s at every
step of the pi-spine). See `Lean4Lean/Theory/Inductive/Decl.lean` §"Why a
structured record", and `Theory/Inductive/DeclExamples.lean` for the same shape
validated on `Eq`, `Nat`, `Acc` and a mutual block. -/

/-- The declaration of `Eq` as an inductive type:
`inductive Eq.{u} {α : Sort u} (a : α) : α → Prop` with constructor `Eq.refl`.
`α` and `a` are the two parameters; the third argument is an index. -/
def eqIndDecl : VInductDecl' where
  uvars := 1
  params := [.sort (.param 0), .bvar 0]
  lvl := .zero
  isLE := true
  types := [{
    name := ``Eq
    type := mkPi [.sort (.param 0), .bvar 0, .bvar 1] (.sort .zero)
    indices := [.bvar 1]
    ctors := [{
      name := ``Eq.refl
      params := [.sort (.param 0), .bvar 0]
      fields := []
      args := [.bvar 0] }] }]

example : (vconst(type_of% @Eq)).uvars = eqIndDecl.uvars := rfl
example : (vconst(type_of% @Eq)).type = (eqIndDecl.types.getD 0 default).type := rfl
example : (eqIndDecl.types.getD 0 default).type
    = (eqIndDecl.types.getD 0 default).canonType eqIndDecl := rfl
example : (vconst(type_of% @Eq.refl)).type
    = ((eqIndDecl.types.getD 0 default).ctors.getD 0 default).type eqIndDecl 0 := rfl
example : (vconst(type_of% @Eq.rec)).uvars = eqIndDecl.recUvars := rfl

/-- The declaration of `Iff` as an inductive type (a structure, i.e. a
one-constructor inductive; its projections are definable, so they are not part
of the prelude). Both propositions are parameters, and there are no indices. -/
def iffIndDecl : VInductDecl' where
  uvars := 0
  params := [.sort .zero, .sort .zero]
  lvl := .zero
  isLE := true
  types := [{
    name := ``Iff
    type := mkPi [.sort .zero, .sort .zero] (.sort .zero)
    indices := []
    ctors := [{
      name := ``Iff.intro
      params := [.sort .zero, .sort .zero]
      fields :=
        -- `mp : a → b` over `[b, a]`, then `mpr : b → a` over `[mp, b, a]`
        [{ type := .forallE (.bvar 1) (.bvar 1), lvl := .zero, recArg := none },
         { type := .forallE (.bvar 1) (.bvar 3), lvl := .zero, recArg := none }]
      args := [] }] }]

example : (vconst(type_of% @Iff)).uvars = iffIndDecl.uvars := rfl
example : (vconst(type_of% @Iff)).type = (iffIndDecl.types.getD 0 default).type := rfl
example : (iffIndDecl.types.getD 0 default).type
    = (iffIndDecl.types.getD 0 default).canonType iffIndDecl := rfl
example : (vconst(type_of% @Iff.intro)).type
    = ((iffIndDecl.types.getD 0 default).ctors.getD 0 default).type iffIndDecl 0 := rfl
example : (vconst(type_of% @Iff.rec)).uvars = iffIndDecl.recUvars := rfl

/-- The declaration of `Nonempty` as an inductive type.  Unlike `Eq` and `Iff`
this is *not* a large eliminator: its single constructor's single field `val : α`
is not a proof and does not occur among the constructor's result indices (there
are none), so `Nonempty.rec` eliminates only into `Prop`. -/
def nonemptyIndDecl : VInductDecl' where
  uvars := 1
  params := [.sort (.param 0)]
  lvl := .zero
  isLE := false
  types := [{
    name := ``Nonempty
    type := mkPi [.sort (.param 0)] (.sort .zero)
    indices := []
    ctors := [{
      name := ``Nonempty.intro
      params := [.sort (.param 0)]
      fields := [{ type := .bvar 0, lvl := .param 0, recArg := none }]
      args := [] }] }]

example : (vconst(type_of% @Nonempty)).uvars = nonemptyIndDecl.uvars := rfl
example : (vconst(type_of% @Nonempty)).type = (nonemptyIndDecl.types.getD 0 default).type := rfl
example : (nonemptyIndDecl.types.getD 0 default).type
    = (nonemptyIndDecl.types.getD 0 default).canonType nonemptyIndDecl := rfl
example : (vconst(type_of% @Nonempty.intro)).type
    = ((nonemptyIndDecl.types.getD 0 default).ctors.getD 0 default).type nonemptyIndDecl 0 := rfl
example : (vconst(type_of% @Nonempty.rec)).uvars = nonemptyIndDecl.recUvars := rfl

/-- The axiom `propext : ∀ {a b : Prop}, (a ↔ b) → a = b`. -/
def propextConst : VConstVal :=
  { toVConstant := vconst(type_of% @propext), name := ``propext }

/-- The axiom `Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
r a b → Quot.mk r a = Quot.mk r b`. -/
def quotSoundConst : VConstVal :=
  { toVConstant := vconst(type_of% @Quot.sound), name := ``Quot.sound }

/-- The axiom `Classical.choice : ∀ {α : Sort u}, Nonempty α → α`. -/
def choiceConst : VConstVal :=
  { toVConstant := vconst(type_of% @Classical.choice), name := ``Classical.choice }

/-- The standard prelude of Lean's type theory, in chronological order:
the inductive types `Eq`, `Iff`, `Nonempty`, the quotient primitives, and the
three standard axioms. These are exactly the axioms of the theory studied in
Carneiro (2019); every further environment extension must be axiom-free. -/
def leanPrelude : List VDecl := [
  .induct eqIndDecl,
  .induct iffIndDecl,
  .axiom propextConst,
  .induct nonemptyIndDecl,
  .axiom choiceConst,
  .quot,
  .axiom quotSoundConst]

/-! ## Consistency -/

/-- A declaration step other than `.axiom`. All other steps are conservative:
`VDecl.WF` requires them to typecheck, and (by the intended metatheory) they
cannot introduce inconsistency over the standard prelude. -/
def VDecl.isAxiomFree : VDecl → Prop
  | .axiom _ => False
  | _ => True

/-- The canonical false proposition `∀ p : Prop, p`, as a `VExpr`.
An environment is inconsistent iff this type is inhabited; unlike a declared
`False` constant, it is available in every environment. -/
def falseProp : VExpr := vexpr(∀ p : Prop, p)

/-- `env.Consistent`: no closed term of type `∀ p : Prop, p`. -/
def VEnv.Consistent (env : VEnv) : Prop :=
  ¬∃ e, env.HasType 0 [] e falseProp

/-- `env` is a standard Lean environment: obtained from the standard prelude by
well-formed, axiom-free declaration steps. (`VEnv.WF'` lists declarations with
the most recent first, so the prelude is the reversed suffix.) -/
def VEnv.LeanWF (env : VEnv) : Prop :=
  ∃ ds : List VDecl, VEnv.WF' (ds ++ leanPrelude.reverse) env ∧
    ∀ d ∈ ds, d.isAxiomFree

/-- Consistency of Lean's type theory: no standard Lean environment proves
`∀ p : Prop, p`. This is the Lean-side of the equiconsistency with
ZFC + {there exist `n` inaccessible cardinals | `n < ω`}. -/
def leanTTConsistent : Prop := ∀ env : VEnv, env.LeanWF → env.Consistent

end Lean4Lean
