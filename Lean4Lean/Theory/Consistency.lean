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

* KNOWN STATEMENT GAPS (tracked): the `.induct` case of `VDecl.WF` uses
  `VInductDecl.WF` and `VEnv.addInduct`, which are currently `sorry`-backed
  definitions in `Lean4Lean.Theory.Inductive`. Until they are defined, the
  meaning of the prelude's inductive steps (and hence of this statement) is
  incomplete.
-/

namespace Lean4Lean

/-! ## The standard prelude -/

/-- The declaration of `Eq` as an inductive type:
`inductive Eq : {α : Sort u} → α → α → Prop` with constructor `Eq.refl`. -/
def eqIndDecl : VInductDecl where
  uvars := 1
  nparams := 2
  types := [{
    toVConstant := vconst(type_of% @Eq)
    name := ``Eq
    ctors := [{ toVConstant := vconst(type_of% @Eq.refl), name := ``Eq.refl }] }]

/-- The declaration of `Iff` as an inductive type (a structure, i.e. a
one-constructor inductive; its projections are definable, so they are not part
of the prelude). -/
def iffIndDecl : VInductDecl where
  uvars := 0
  nparams := 2
  types := [{
    toVConstant := vconst(type_of% @Iff)
    name := ``Iff
    ctors := [{ toVConstant := vconst(type_of% @Iff.intro), name := ``Iff.intro }] }]

/-- The declaration of `Nonempty` as an inductive type. -/
def nonemptyIndDecl : VInductDecl where
  uvars := 1
  nparams := 1
  types := [{
    toVConstant := vconst(type_of% @Nonempty)
    name := ``Nonempty
    ctors := [{ toVConstant := vconst(type_of% @Nonempty.intro), name := ``Nonempty.intro }] }]

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
