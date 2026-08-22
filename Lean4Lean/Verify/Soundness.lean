import Lean4Lean.Environment
import Foundation.FirstOrder.SetTheory.InaccessibleCardinal

/-!
# Main theorem: soundness of the lean4lean kernel relative to ZFC + ω inaccessibles

This file states the end-to-end guarantee about the *executable* checker
`Lean4Lean.addDecl`: if a sequence of declarations — the standard prelude
followed by axiom-free declarations — is accepted by the checker and produces
an environment containing a safe proof of `∀ p : Prop, p`, then the
first-order theory `ZFC + {"≥ n inaccessible cardinals" | n ∈ ω}` is
inconsistent. Contrapositive: **if that set theory is consistent, the checker
never certifies `False`**.

The statement mentions only the checker itself, upstream `Lean.Declaration`/
`Kernel.Environment` data, the concrete prelude below, and Foundation's
first-order provability. The abstract type theory (`Lean4Lean.Theory`) is
proof machinery, not part of this statement.

The converse (`kernel_complete`) certifies tightness of the assumption; only
`kernel_sound` is the binding goal.

## Design notes, for review

* The prelude is given by explicit `Declaration` literals and pins the genuine
  declarations of `Eq`, `Iff`, `Nonempty` together with the three standard
  axioms and the quotient extension. Pinning the inductives, not just the
  axioms' type shapes, is essential: `propext` over a nonstandard `Eq` would
  honestly prove `False`. Two `#eval` build-time checks below verify (a) the
  literals match this toolchain's actual declarations up to α-equivalence,
  and (b) the checker accepts the prelude from the empty environment — so the
  theorem's hypotheses are satisfiable.
* Further `axiomDecl`s are excluded; everything else (definitions, theorems,
  inductives, mutual/unsafe/partial declarations) is allowed, since the
  checker validates them.
* The `False` witness must be a *safe* constant (`unsafe`/`partial`
  declarations are exempt from the logical guarantee by design), with no
  universe parameters and literally the type `∀ p : Prop, p` — sufficient by
  the extension argument: any environment proving `False` in another form
  extends by one definition to one containing this literal form.
* `fuel` is universally quantified: fuel exhaustion is a rejection, so more
  fuel only enlarges the accepted set.
-/

namespace Lean4Lean

open Lean Kernel
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## The standard prelude, as explicit declarations -/

/-- `Eq`, exactly as declared by this toolchain's core library. -/
def eqDecl : Declaration :=
  .inductDecl [`u_1] 2
    [{ name := ``Eq
       type := .forallE `α (.sort (.param `u_1))
         (.forallE `a (.bvar 0) (.forallE `b (.bvar 1) (.sort .zero) .default) .default)
         .implicit
       ctors := [{
         name := ``Eq.refl
         type := .forallE `α (.sort (.param `u_1))
           (.forallE `a (.bvar 0)
             (.app (.app (.app (.const ``Eq [.param `u_1]) (.bvar 1)) (.bvar 0)) (.bvar 0))
             .default)
           .implicit }] }]
    false

/-- `Iff`, exactly as declared by this toolchain's core library. -/
def iffDecl : Declaration :=
  .inductDecl [] 2
    [{ name := ``Iff
       type := .forallE `a (.sort .zero) (.forallE `b (.sort .zero) (.sort .zero) .default)
         .default
       ctors := [{
         name := ``Iff.intro
         type := .forallE `a (.sort .zero)
           (.forallE `b (.sort .zero)
             (.forallE `mp (.forallE `h (.bvar 1) (.bvar 1) .default)
               (.forallE `mpr (.forallE `h (.bvar 1) (.bvar 3) .default)
                 (.app (.app (.const ``Iff []) (.bvar 3)) (.bvar 2)) .default)
               .default)
             .implicit)
           .implicit }] }]
    false

/-- `Nonempty`, exactly as declared by this toolchain's core library. -/
def nonemptyDecl : Declaration :=
  .inductDecl [`u] 1
    [{ name := ``Nonempty
       type := .forallE `α (.sort (.param `u)) (.sort .zero) .default
       ctors := [{
         name := ``Nonempty.intro
         type := .forallE `α (.sort (.param `u))
           (.forallE `val (.bvar 0) (.app (.const ``Nonempty [.param `u]) (.bvar 1)) .default)
           .implicit }] }]
    false

/-- The axiom `propext`. -/
def propextDecl : Declaration :=
  .axiomDecl {
    name := ``propext
    levelParams := []
    type := .forallE `a (.sort .zero)
      (.forallE `b (.sort .zero)
        (.forallE `h (.app (.app (.const ``Iff []) (.bvar 1)) (.bvar 0))
          (.app (.app (.app (.const ``Eq [.succ .zero]) (.sort .zero)) (.bvar 2)) (.bvar 1))
          .default)
        .implicit)
      .implicit
    isUnsafe := false }

/-- The axiom `Quot.sound`. -/
def quotSoundDecl : Declaration :=
  .axiomDecl {
    name := ``Quot.sound
    levelParams := [`u]
    type := .forallE `α (.sort (.param `u))
      (.forallE `r (.forallE `a (.bvar 0) (.forallE `b (.bvar 1) (.sort .zero) .default) .default)
        (.forallE `a (.bvar 1)
          (.forallE `b (.bvar 2)
            (.forallE `h (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
              (.app
                (.app
                  (.app (.const ``Eq [.param `u])
                    (.app (.app (.const ``Quot [.param `u]) (.bvar 4)) (.bvar 3)))
                  (.app (.app (.app (.const ``Quot.mk [.param `u]) (.bvar 4)) (.bvar 3)) (.bvar 2)))
                (.app (.app (.app (.const ``Quot.mk [.param `u]) (.bvar 4)) (.bvar 3)) (.bvar 1)))
              .default)
            .implicit)
          .implicit)
        .implicit)
      .implicit
    isUnsafe := false }

/-- The axiom `Classical.choice`. -/
def choiceDecl : Declaration :=
  .axiomDecl {
    name := ``Classical.choice
    levelParams := [`u]
    type := .forallE `α (.sort (.param `u))
      (.forallE `h (.app (.const ``Nonempty [.param `u]) (.bvar 0)) (.bvar 1) .default)
      .implicit
    isUnsafe := false }

/-- The standard prelude: the inductive types `Eq`, `Iff`, `Nonempty`, the
quotient extension, and the three standard axioms, in dependency order. -/
def stdPrelude : List Declaration :=
  [eqDecl, iffDecl, propextDecl, .quotDecl, quotSoundDecl, nonemptyDecl, choiceDecl]

/-! ## Reachability and the False witness -/

/-- Run the checker on a list of declarations from the empty environment,
stopping at the first rejection. -/
def foldAddDecl (fuel : FuelConfig) (ds : List Declaration) :
    Except Kernel.Exception Kernel.Environment :=
  ds.foldlM (fun env d => addDecl env d (check := true) (fuel := fuel))
    (Kernel.Environment.empty `main)

/-- `d` declares no axiom. Everything else — definitions, theorems, opaques,
inductives, mutual blocks, `unsafe`/`partial` declarations — is permitted. -/
def Declaration.IsAxiomFree : Declaration → Prop
  | .axiomDecl _ => False
  | _ => True

/-- The canonical false proposition `∀ p : Prop, p`, as a kernel expression. -/
def falseExpr : Expr := .forallE `p (.sort .zero) (.bvar 0) .default

/-- The environment contains a safe, universe-monomorphic constant whose type
is literally `∀ p : Prop, p`. -/
def ContainsSafeProofOfFalse (env : Kernel.Environment) : Prop :=
  ∃ (n : Name) (ci : ConstantInfo), env.find? n = some ci ∧
    ci.isUnsafe = false ∧ ci.isPartial = false ∧
    ci.levelParams = [] ∧ ci.type = falseExpr

/-! ## The main theorem -/

/-- **Soundness of the lean4lean kernel relative to ZFC + ω-many inaccessible
cardinals.** If the checker, starting from the empty environment, accepts the
standard prelude followed by any axiom-free declarations and thereby certifies
a safe proof of `∀ p : Prop, p`, then
`ZFC + {"there exist at least n inaccessible cardinals" | n ∈ ω}` derives `⊥`.

Contrapositive: if that set theory is consistent, the checker never certifies
`False`. -/
theorem kernel_sound (ds : List Declaration) (fuel : FuelConfig)
    (env : Kernel.Environment)
    (hok : foldAddDecl fuel (stdPrelude ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
    (hfalse : ContainsSafeProofOfFalse env) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 := by
  sorry

/-- Tightness of the assumption (converse of `kernel_sound`): an inconsistency
of ZFC + ω-many inaccessibles can be compiled to a declaration sequence that
the checker accepts and that certifies `False`. Not part of the binding goal. -/
theorem kernel_complete (h : Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰) :
    ∃ (ds : List Declaration) (fuel : FuelConfig) (env : Kernel.Environment),
      foldAddDecl fuel (stdPrelude ++ ds) = .ok env ∧
      (∀ d ∈ ds, Declaration.IsAxiomFree d) ∧ ContainsSafeProofOfFalse env := by
  sorry

/-! ## Build-time adequacy checks

These run during elaboration and fail the build on regression. They are
tests, not proofs: the theorem statements above do not depend on them. -/

/- The prelude literals match this toolchain's actual core declarations
(levels, parameter counts, constructors, and types up to α-equivalence). -/
#eval show CoreM Unit from do
  let env ← getEnv
  let checkInd (d : Declaration) : CoreM Unit := do
    let .inductDecl lps np [t] false := d | throwError "bad literal shape"
    let some (.inductInfo v) := env.find? t.name | throwError "missing {t.name}"
    unless v.levelParams = lps ∧ v.numParams = np ∧ v.type.eqv t.type do
      throwError "mismatch at {t.name}"
    unless v.ctors.length = t.ctors.length do throwError "ctor count {t.name}"
    for c in t.ctors do
      let some (.ctorInfo cv) := env.find? c.name | throwError "missing {c.name}"
      unless cv.type.eqv c.type do throwError "mismatch at {c.name}"
  let checkAx (d : Declaration) : CoreM Unit := do
    let .axiomDecl v := d | throwError "bad literal shape"
    let some (.axiomInfo av) := env.find? v.name | throwError "missing {v.name}"
    unless av.levelParams = v.levelParams ∧ av.type.eqv v.type ∧ !av.isUnsafe do
      throwError "mismatch at {v.name}"
  checkInd eqDecl; checkInd iffDecl; checkInd nonemptyDecl
  checkAx propextDecl; checkAx quotSoundDecl; checkAx choiceDecl
  IO.println "stdPrelude matches the toolchain's core declarations ✓"

/- The checker accepts the prelude, so `kernel_sound`'s hypotheses are
satisfiable. -/
#eval show CoreM Unit from do
  match foldAddDecl {} stdPrelude with
  | .ok _ => IO.println "stdPrelude accepted by addDecl ✓"
  | .error _ => throwError "stdPrelude rejected by addDecl"

end Lean4Lean
