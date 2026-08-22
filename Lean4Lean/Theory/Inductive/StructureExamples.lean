import Lean4Lean.Theory.Inductive.Structure
import Lean4Lean.Theory.Meta

/-!
# Validation of the projection encoding

Every check below is an `example … := rfl`, so this file failing to build *is* the test
failing.  Same idiom and same ground truth as `DeclExamples.lean`: `vexpr(…)` /
`vconst(…)` elaborate a *real* Lean term and translate it to `VExpr`, so Lean's own
elaborator fixes argument order, implicit arguments, de Bruijn indices and universe
levels, and `VInductDecl'.projTerm` is compared against that.

Four structures, chosen for what they exercise:

* `Prod` — universe-polymorphic, two non-dependent fields;
* `Sigma` — a **dependent** second field, so the motive must project its own binder;
* `And` — a **`Prop` structure with `Prop` fields** and `uvars = 0`, reaching large
  elimination through `LECond`'s second disjunct.  This is the case where `projCore`'s
  choice of elimination level meets `inferProj`'s `isProp dom` guard (F17);
* `Subtype` — `Type`-valued with a dependent `Prop` field.

Each block validates the `VInductDecl'` record itself against Lean (`type_of% @Prod`,
`@Prod.mk`, `@Prod.rec`) before validating the projection, so a mismatch is localised.

The recursor prepends a fresh elimination universe at index 0 (F10) while Lean numbers
universes by order of first appearance, which puts the block's own universes first;
`swap01`/`rot3` bridge the two numberings and are pure renamings.
-/

-- the `vexpr(…)` binders are only there to fix the de Bruijn context
set_option linter.unusedVariables false

namespace Lean4Lean
namespace StructureExamples

open VExpr

/-- Recursor numbering `(elim, u)` → Lean's `(u, elim)`. -/
def swap01 (e : VExpr) : VExpr := e.instL [.param 1, .param 0]
/-- Recursor numbering `(elim, u, v)` → Lean's `(u, v, elim)`. -/
def rot3 (e : VExpr) : VExpr := e.instL [.param 2, .param 0, .param 1]

/-! ## `Prod` — universe-polymorphic, two non-dependent fields -/

def prodParams : List VExpr := [.sort (.succ (.param 0)), .sort (.succ (.param 1))]

def prodMk : VIndCtor where
  name := ``Prod.mk
  params := prodParams
  fields :=
    [{ type := .bvar 1, lvl := .succ (.param 0), recArg := none },
     { type := .bvar 1, lvl := .succ (.param 1), recArg := none }]
  args := []

def prodType : VIndType where
  name := ``Prod
  type := mkPi prodParams (.sort (.max (.succ (.param 0)) (.succ (.param 1))))
  indices := []
  ctors := [prodMk]

def prodDecl : VInductDecl' where
  uvars := 2
  params := prodParams
  lvl := .max (.succ (.param 0)) (.succ (.param 1))
  isLE := true
  types := [prodType]

-- the declaration record, against Lean
example : prodType.type = prodType.canonType prodDecl := rfl
example : prodType.canonType prodDecl = (vconst(type_of% @Prod)).type := rfl
example : (vconst(type_of% @Prod)).uvars = prodDecl.uvars := rfl
example : prodMk.type prodDecl 0 = (vconst(type_of% @Prod.mk)).type := rfl
example : prodDecl.recUvars = (vconst(type_of% @Prod.rec)).uvars := rfl
example : rot3 (prodDecl.recType 0) = (vconst(type_of% @Prod.rec)).type := rfl
example : rot3 (mkPi (prodDecl.atRecTele prodDecl.params) (prodDecl.motiveType 0)) =
    vexpr(∀ (α : Type u) (β : Type v), α × β → Sort w) := rfl
-- `IsStructure.noRec`
example : prodMk.recFields = [] := rfl

/-- The context `α β (p : α × β)`, so that `α = .bvar 2`, `β = .bvar 1`, `p = .bvar 0`. -/
def prodCtx : List VExpr :=
  prodParams ++ [(VExpr.const ``Prod [.param 0, .param 1]).mkApp [.bvar 1, .bvar 0]]

example : mkLams prodCtx
    (prodDecl.projTerm prodType prodMk [.param 0, .param 1] [.bvar 2, .bvar 1] [] 0 (.bvar 0)) =
    vexpr(fun (α : Type u) (β : Type v) (p : α × β) =>
      @Prod.rec α β (fun _ => α) (fun a b => a) p) := rfl
example : mkLams prodCtx
    (prodDecl.projTerm prodType prodMk [.param 0, .param 1] [.bvar 2, .bvar 1] [] 1 (.bvar 0)) =
    vexpr(fun (α : Type u) (β : Type v) (p : α × β) =>
      @Prod.rec α β (fun _ => β) (fun a b => b) p) := rfl

/-! ## `Sigma` — a genuinely dependent second field -/

def sigmaParams : List VExpr :=
  [.sort (.succ (.param 0)), .forallE (.bvar 0) (.sort (.succ (.param 1)))]

def sigmaMk : VIndCtor where
  name := ``Sigma.mk
  params := sigmaParams
  fields :=
    [{ type := .bvar 1, lvl := .succ (.param 0), recArg := none },
     { type := (VExpr.bvar 1).app (.bvar 0), lvl := .succ (.param 1), recArg := none }]
  args := []

def sigmaType : VIndType where
  name := ``Sigma
  type := mkPi sigmaParams (.sort (.max (.succ (.param 0)) (.succ (.param 1))))
  indices := []
  ctors := [sigmaMk]

def sigmaDecl : VInductDecl' where
  uvars := 2
  params := sigmaParams
  lvl := .max (.succ (.param 0)) (.succ (.param 1))
  isLE := true
  types := [sigmaType]

example : sigmaType.type = sigmaType.canonType sigmaDecl := rfl
example : sigmaType.canonType sigmaDecl = (vconst(type_of% @Sigma)).type := rfl
example : sigmaMk.type sigmaDecl 0 = (vconst(type_of% @Sigma.mk)).type := rfl
example : rot3 (sigmaDecl.recType 0) = (vconst(type_of% @Sigma.rec)).type := rfl
example : sigmaMk.recFields = [] := rfl

def sigmaCtx : List VExpr :=
  sigmaParams ++ [(VExpr.const ``Sigma [.param 0, .param 1]).mkApp [.bvar 1, .bvar 0]]

example : mkLams sigmaCtx
    (sigmaDecl.projTerm sigmaType sigmaMk [.param 0, .param 1] [.bvar 2, .bvar 1] [] 0 (.bvar 0)) =
    vexpr(fun (α : Type u) (β : α → Type v) (p : Sigma β) =>
      @Sigma.rec α β (fun _ => α) (fun a b => a) p) := rfl

/-- **The dependent case.**  `(p : Sigma β).2 : β p.1`, so the motive has to contain the
*first* projection of its own bound major premise.  This is the clause that mirrors
`inferProj`'s `r := b.instantiate1 (.proj I_name i struct)`. -/
example : mkLams sigmaCtx
    (sigmaDecl.projTerm sigmaType sigmaMk [.param 0, .param 1] [.bvar 2, .bvar 1] [] 1 (.bvar 0)) =
    vexpr(fun (α : Type u) (β : α → Type v) (p : Sigma β) =>
      @Sigma.rec α β (fun x => β (@Sigma.rec α β (fun _ => α) (fun a b => a) x))
        (fun a b => b) p) := rfl

/-! ## `And` — a `Prop` structure with `Prop` fields (`uvars = 0`) -/

def andIntro : VIndCtor where
  name := ``And.intro
  params := [.sort .zero, .sort .zero]
  fields :=
    [{ type := .bvar 1, lvl := .zero, recArg := none },
     { type := .bvar 1, lvl := .zero, recArg := none }]
  args := []

def andType : VIndType where
  name := ``And
  type := mkPi [.sort .zero, .sort .zero] (.sort .zero)
  indices := []
  ctors := [andIntro]

def andDecl : VInductDecl' where
  uvars := 0
  params := [.sort .zero, .sort .zero]
  lvl := .zero
  isLE := true
  types := [andType]

example : andType.canonType andDecl = (vconst(type_of% @And)).type := rfl
example : andIntro.type andDecl 0 = (vconst(type_of% @And.intro)).type := rfl
example : andDecl.recUvars = (vconst(type_of% @And.rec)).uvars := rfl
example : andDecl.recType 0 = (vconst(type_of% @And.rec)).type := rfl
example : andIntro.recFields = [] := rfl

/-- `And : Prop` is not `IsNeverZero`, so large elimination goes through `LECond`'s second
disjunct: one type, one constructor, every field's level `≈ 0`.  That `And.rec` really is
large-eliminating is what makes the `Prop`-structure projections below well-typed. -/
example : andDecl.LECond := .inr ⟨andType, rfl, .inr ⟨andIntro, rfl, by
  rintro (_|_|i) F h <;> simp_all [andIntro] <;> subst h <;> exact .refl _⟩⟩

def andCtx : List VExpr :=
  [.sort .zero, .sort .zero, (VExpr.const ``And []).mkApp [.bvar 1, .bvar 0]]

example : mkLams andCtx
    (andDecl.projTerm andType andIntro [] [.bvar 2, .bvar 1] [] 0 (.bvar 0)) =
    vexpr(fun (a b : Prop) (h : a ∧ b) => @And.rec a b (fun _ => a) (fun l r => l) h) := rfl
example : mkLams andCtx
    (andDecl.projTerm andType andIntro [] [.bvar 2, .bvar 1] [] 1 (.bvar 0)) =
    vexpr(fun (a b : Prop) (h : a ∧ b) => @And.rec a b (fun _ => b) (fun l r => r) h) := rfl

/-! ## `Subtype` — `Type`-valued, with a dependent `Prop` field -/

def subtypeParams : List VExpr := [.sort (.param 0), .forallE (.bvar 0) (.sort .zero)]

def subtypeMk : VIndCtor where
  name := ``Subtype.mk
  params := subtypeParams
  fields :=
    [{ type := .bvar 1, lvl := .param 0, recArg := none },
     { type := (VExpr.bvar 1).app (.bvar 0), lvl := .zero, recArg := none }]
  args := []

def subtypeType : VIndType where
  name := ``Subtype
  type := mkPi subtypeParams (.sort (.max (.succ .zero) (.param 0)))
  indices := []
  ctors := [subtypeMk]

def subtypeDecl : VInductDecl' where
  uvars := 1
  params := subtypeParams
  lvl := .max (.succ .zero) (.param 0)
  isLE := true
  types := [subtypeType]

example : subtypeType.canonType subtypeDecl = (vconst(type_of% @Subtype)).type := rfl
example : subtypeMk.type subtypeDecl 0 = (vconst(type_of% @Subtype.mk)).type := rfl
example : swap01 (subtypeDecl.recType 0) = (vconst(type_of% @Subtype.rec)).type := rfl
example : subtypeMk.recFields = [] := rfl

def subtypeCtx : List VExpr :=
  subtypeParams ++ [(VExpr.const ``Subtype [.param 0]).mkApp [.bvar 1, .bvar 0]]

example : mkLams subtypeCtx
    (subtypeDecl.projTerm subtypeType subtypeMk [.param 0] [.bvar 2, .bvar 1] [] 0 (.bvar 0)) =
    vexpr(fun (α : Sort u) (p : α → Prop) (s : Subtype p) =>
      @Subtype.rec α p (fun _ => α) (fun v h => v) s) := rfl

/-- A dependent `Prop` field: `(s : Subtype p).property : p s.val`. -/
example : mkLams subtypeCtx
    (subtypeDecl.projTerm subtypeType subtypeMk [.param 0] [.bvar 2, .bvar 1] [] 1 (.bvar 0)) =
    vexpr(fun (α : Sort u) (p : α → Prop) (s : Subtype p) =>
      @Subtype.rec α p (fun x => p (@Subtype.rec α p (fun _ => α) (fun v h => v) x))
        (fun v h => h) s) := rfl

end StructureExamples
end Lean4Lean
