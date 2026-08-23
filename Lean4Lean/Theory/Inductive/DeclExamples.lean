import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Inductive.Structure
import Lean4Lean.Theory.Meta

/-!
# Validation of the inductive specification

Every check below is an `example … := rfl`, so this file failing to build *is* the test
failing.

The ground truth is Lean's own kernel: `vconst(type_of% @Eq.rec)` elaborates the real
`Eq.rec`, translates it to a `VExpr`, and compares it with `eqDecl.recType 0`.  Nothing
about the recursor construction is taken on trust.

Four blocks are covered:

* `Eq` — indices, a large-eliminating `Prop`, no fields;
* `Nat` — no parameters, a recursive field, two constructors;
* `Acc` — parameters *and* indices, a higher-order recursive field with `ξ`-binders and a
  nontrivial `π`, and `LECond`'s second disjunct;
* `Tree'`/`Forest'` — a genuine two-type mutual block with three constructors, one with
  two recursive fields, exercising the motive/minor threading and `ihTypes`' `s` offset.

## Conventions

Motives, minor premises and induction hypotheses are open terms, so each is compared
after being closed off by the very telescope the specification says it lives over
(`minorPreCtx`, `minorFieldCtx`).  That makes the *context* part of the assertion.

The recursor prepends a fresh elimination universe at index 0 (F10), so the block's own
universes shift up by one (`selfLvls`).  Lean numbers universes by order of first
appearance, which puts the block's universe first.  `swap01` bridges the two; it is a pure
renaming, and it is applied only where a universe actually occurs.

**Before adding a block with two or more universe parameters, read this.**  `vconst(type_of% X)`
numbers universes by order of first appearance *in `X`'s own type*, and that order is not
stable across the declarations of one block.  For a two-universe `LvlWit'.{u, v}` one gets
`LvlWit'` numbered `[v, u]` (the index `Sort v` comes first), `LvlWit'.mk` numbered `[u, v]`
(its first field is `Sort u`), and `LvlWit'.rec` numbered `[v, u, elim]` — three *different*
renamings needed in one block, none of them `swap01`.  Every block below has at most one
universe parameter, so **this convention has never been exercised**; the checks passing is
not evidence that it works.  Either give each comparison its own renaming, or pick a
declaration whose universes appear in the same order everywhere (which is what `LvlWit`
below does, by using a single parameter).
-/

-- the `vexpr(…)` binders are only there to fix the de Bruijn context
set_option linter.unusedVariables false

namespace Lean4Lean
namespace InductiveDeclExamples

open VExpr

/-- Rename `.param 0 ↔ .param 1`: the recursor's `(elim, u)` numbering vs. Lean's
order-of-appearance `(u, elim)` numbering. -/
def swap01 (e : VExpr) : VExpr := e.instL [.param 1, .param 0]

/-- The context motive `t` lives over: `params ++ motives<t`. -/
def motiveCtx (D : VInductDecl') (t : Nat) : List VExpr :=
  D.atRecTele D.params ++ D.motives.take t

/-- The context minor premise `q` lives over: `params ++ motives ++ minors<q`. -/
def minorPreCtx (D : VInductDecl') (q : Nat) : List VExpr :=
  D.atRecTele D.params ++ D.motives ++ D.minors.take q

/-- The context of minor `q`'s induction-hypothesis telescope: the above, plus the
constructor's fields. -/
def minorFieldCtx (D : VInductDecl') (q : Nat) (C : VIndCtor) : List VExpr :=
  minorPreCtx D q ++ liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type)))

/-! ## `Eq` -/

/-- `Eq.{u} : ∀ (α : Sort u) (a b : α), Prop`, with `α, a` parameters and `b` an index. -/
def eqRefl : VIndCtor where
  name := ``Eq.refl
  params := [.sort (.param 0), .bvar 0]
  fields := []
  args := [.bvar 0]

def eqType : VIndType where
  name := ``Eq
  type := mkPi [.sort (.param 0), .bvar 0, .bvar 1] (.sort .zero)
  indices := [.bvar 1]
  ctors := [eqRefl]

def eqDecl : VInductDecl' where
  uvars := 1
  params := [.sort (.param 0), .bvar 0]
  lvl := .zero
  isLE := true
  types := [eqType]

example : eqDecl.np = 2 := rfl
example : eqDecl.nm = 1 := rfl
example : eqDecl.nmin = 1 := rfl
example : eqDecl.ctorsAll = [(0, eqRefl)] := rfl
example : eqDecl.recUvars = 2 := rfl
example : eqDecl.elimLvl = .param 0 := rfl
example : eqDecl.selfLvls = [.param 1] := rfl
example : eqDecl.allNames = [``Eq, ``Eq.refl, ``Eq.rec] := rfl

-- the stored type really is the canonical one, and it is the real `Eq`
example : eqType.type = eqType.canonType eqDecl := rfl
example : eqType.canonType eqDecl = (vconst(type_of% @Eq)).type := rfl
example : (vconst(type_of% @Eq)).uvars = eqDecl.uvars := rfl

-- the derived constructor type is the real `Eq.refl`
example : eqRefl.type eqDecl 0 = (vconst(type_of% @Eq.refl)).type := rfl

-- the motive and the minor premise, closed off by their contexts
example : swap01 (mkPi (motiveCtx eqDecl 0) (eqDecl.motiveType 0)) =
    vexpr(∀ (α : Sort u) (a : α), (b : α) → a = b → Sort v) := rfl
example : swap01 (mkPi (minorPreCtx eqDecl 0) (eqDecl.minorType 0 0 eqRefl)) =
    vexpr(∀ (α : Sort u) (a : α) (motive : (b : α) → a = b → Sort v),
      motive a (Eq.refl a)) := rfl

-- **the recursor type, against Lean's own `Eq.rec`**
example : swap01 (eqDecl.recType 0) = (vconst(type_of% @Eq.rec)).type := rfl
example : eqDecl.recUvars = (vconst(type_of% @Eq.rec)).uvars := rfl

-- the ι-rule
example : eqDecl.iotaCtx eqRefl = minorFieldCtx eqDecl eqDecl.nmin eqRefl := rfl
example : eqDecl.ihValues eqRefl = [] := rfl
example : swap01 (eqDecl.iotaLam 0 eqRefl) =
    vexpr(fun (α : Sort u) (a : α) (motive : (b : α) → a = b → Sort v)
      (refl : motive a (Eq.refl a)) => refl) := rfl
example : swap01 (mkLams (eqDecl.iotaCtx eqRefl) (eqDecl.iotaLhs 0 eqRefl)) =
    vexpr(fun (α : Sort u) (a : α) (motive : (b : α) → a = b → Sort v)
      (refl : motive a (Eq.refl a)) => @Eq.rec α a motive refl a (Eq.refl a)) := rfl
example : swap01 (mkPi (eqDecl.iotaCtx eqRefl) (eqDecl.iotaType 0 eqRefl)) =
    vexpr(∀ (α : Sort u) (a : α) (motive : (b : α) → a = b → Sort v),
      motive a (Eq.refl a) → motive a (Eq.refl a)) := rfl

example : (eqDecl.iotaRule 0 0 eqRefl).uvars = 2 := rfl
example : (eqDecl.iotaRule 0 0 eqRefl).lhs
    = mkLams (eqDecl.iotaCtx eqRefl) (eqDecl.iotaLhs 0 eqRefl) := rfl
example : (eqDecl.iotaRule 0 0 eqRefl).type
    = mkPi (eqDecl.iotaCtx eqRefl) (eqDecl.iotaType 0 eqRefl) := rfl
example : eqDecl.iotaRules = [eqDecl.iotaRule 0 0 eqRefl] := rfl

/-- `Eq : Prop` is not `IsNeverZero`, so large elimination goes through `LECond`'s second
disjunct: one type, one constructor, no fields. -/
example : eqDecl.LECond :=
  .inr ⟨eqType, rfl, .inr ⟨eqRefl, rfl, by intro i F h; simp [eqRefl] at h⟩⟩

/-! ## `Nat` -/

def natZero : VIndCtor where
  name := ``Nat.zero
  params := []
  fields := []
  args := []

def natSucc : VIndCtor where
  name := ``Nat.succ
  params := []
  fields := [{ type := .const ``Nat [], lvl := .succ .zero,
               recArg := some { binders := [], idx := 0, args := [] } }]
  args := []

def natDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := true
  types := [{
    name := ``Nat
    type := .sort (.succ .zero)
    indices := []
    ctors := [natZero, natSucc] }]

example : natDecl.np = 0 := rfl
example : natDecl.nm = 1 := rfl
example : natDecl.nmin = 2 := rfl
example : natDecl.recUvars = 1 := rfl
example : natDecl.selfLvls = [] := rfl
example : natDecl.ctorsAll = [(0, natZero), (0, natSucc)] := rfl
example : natSucc.recFields = [(0, { binders := [], idx := 0, args := [] })] := rfl

example : (natDecl.types[0]!).type = (natDecl.types[0]!).canonType natDecl := rfl
example : (natDecl.types[0]!).canonType natDecl = (vconst(type_of% Nat)).type := rfl
example : natZero.type natDecl 0 = (vconst(type_of% @Nat.zero)).type := rfl
example : natSucc.type natDecl 0 = (vconst(type_of% @Nat.succ)).type := rfl

example : natDecl.motiveType 0 = vexpr(Nat → Sort u) := rfl
example : mkPi (minorPreCtx natDecl 0) (natDecl.minorType 0 0 natZero) =
    vexpr(∀ (motive : Nat → Sort u), motive Nat.zero) := rfl
example : mkPi (minorFieldCtx natDecl 1 natSucc) ((natDecl.ihTypes 1 natSucc)[0]!) =
    vexpr(∀ (motive : Nat → Sort u) (mz : motive Nat.zero) (n : Nat), motive n) := rfl
example : mkPi (minorPreCtx natDecl 1) (natDecl.minorType 1 0 natSucc) =
    vexpr(∀ (motive : Nat → Sort u) (mz : motive Nat.zero),
      (n : Nat) → motive n → motive n.succ) := rfl

-- **the recursor type, against Lean's own `Nat.rec`**
example : natDecl.recType 0 = (vconst(type_of% @Nat.rec)).type := rfl
example : natDecl.recUvars = (vconst(type_of% @Nat.rec)).uvars := rfl

-- the ι-rules: `Nat.rec mz ms Nat.zero ≡ mz`,
-- `Nat.rec mz ms (Nat.succ n) ≡ ms n (Nat.rec mz ms n)`
example : natDecl.ihValues natZero = [] := rfl
example : natDecl.iotaLam 0 natZero =
    vexpr(fun (motive : Nat → Sort u) (mz : motive Nat.zero)
      (ms : (n : Nat) → motive n → motive n.succ) => mz) := rfl
example : mkLams (natDecl.iotaCtx natZero) (natDecl.iotaLhs 0 natZero) =
    vexpr(fun (motive : Nat → Sort u) (mz : motive Nat.zero)
      (ms : (n : Nat) → motive n → motive n.succ) =>
      @Nat.rec motive mz ms Nat.zero) := rfl

example : mkLams (natDecl.iotaCtx natSucc) ((natDecl.ihValues natSucc)[0]!) =
    vexpr(fun (motive : Nat → Sort u) (mz : motive Nat.zero)
      (ms : (n : Nat) → motive n → motive n.succ) (n : Nat) =>
      @Nat.rec motive mz ms n) := rfl
example : natDecl.iotaLam 1 natSucc =
    vexpr(fun (motive : Nat → Sort u) (mz : motive Nat.zero)
      (ms : (n : Nat) → motive n → motive n.succ) (n : Nat) =>
      ms n (@Nat.rec motive mz ms n)) := rfl
example : mkLams (natDecl.iotaCtx natSucc) (natDecl.iotaLhs 0 natSucc) =
    vexpr(fun (motive : Nat → Sort u) (mz : motive Nat.zero)
      (ms : (n : Nat) → motive n → motive n.succ) (n : Nat) =>
      @Nat.rec motive mz ms n.succ) := rfl
example : mkPi (natDecl.iotaCtx natSucc) (natDecl.iotaType 0 natSucc) =
    vexpr(∀ (motive : Nat → Sort u) (mz : motive Nat.zero)
      (ms : (n : Nat) → motive n → motive n.succ),
      (n : Nat) → motive n.succ) := rfl

/-! ## `Acc` -/

/-- `∀ (y : α), r y x → Acc α r y`, the recursive field of `Acc.intro`; in the context
`[x, r, α]` the binders are `[α, r y x]` and the index is `y`. -/
def accIntroRec : VIndRecArg where
  binders := [.bvar 2, ((VExpr.bvar 2).app (.bvar 0)).app (.bvar 1)]
  idx := 0
  args := [.bvar 1]

def accIntro : VIndCtor where
  name := ``Acc.intro
  params := [.sort (.param 0), mkPi [.bvar 0, .bvar 1] (.sort .zero)]
  fields :=
    [{ type := .bvar 1, lvl := .param 0, recArg := none },
     { type := mkPi accIntroRec.binders
         ((VExpr.const ``Acc [.param 0]).mkApp [.bvar 4, .bvar 3, .bvar 1])
       lvl := .zero
       recArg := some accIntroRec }]
  args := [.bvar 1]

def accType : VIndType where
  name := ``Acc
  type := mkPi [.sort (.param 0), mkPi [.bvar 0, .bvar 1] (.sort .zero), .bvar 1]
    (.sort .zero)
  indices := [.bvar 1]
  ctors := [accIntro]

/-- `Acc.{u} : ∀ (α : Sort u) (r : α → α → Prop), α → Prop`. -/
def accDecl : VInductDecl' where
  uvars := 1
  params := [.sort (.param 0), mkPi [.bvar 0, .bvar 1] (.sort .zero)]
  lvl := .zero
  isLE := true
  types := [accType]

example : accDecl.np = 2 := rfl
example : accDecl.nm = 1 := rfl
example : accDecl.nmin = 1 := rfl
example : accDecl.recUvars = 2 := rfl
example : accIntro.recFields = [(1, accIntroRec)] := rfl

example : accType.type = accType.canonType accDecl := rfl
example : accType.canonType accDecl = (vconst(type_of% @Acc)).type := rfl
example : accIntro.type accDecl 0 = (vconst(type_of% @Acc.intro)).type := rfl
-- the recursive field's stored type is, on the nose, its canonical form
example : (accIntro.fields[1]!).type = accIntroRec.canonType accDecl 1 := rfl

example : swap01 (mkPi (motiveCtx accDecl 0) (accDecl.motiveType 0)) =
    vexpr(∀ (α : Sort u) (r : α → α → Prop), (x : α) → Acc r x → Sort v) := rfl
example : swap01 (mkPi (minorFieldCtx accDecl 0 accIntro)
      ((accDecl.ihTypes 0 accIntro)[0]!)) =
    vexpr(∀ (α : Sort u) (r : α → α → Prop) (motive : (x : α) → Acc r x → Sort v)
      (x : α) (h : ∀ y, r y x → Acc r y),
      (y : α) → (hy : r y x) → motive y (h y hy)) := rfl
example : swap01 (mkPi (minorPreCtx accDecl 0) (accDecl.minorType 0 0 accIntro)) =
    vexpr(∀ (α : Sort u) (r : α → α → Prop) (motive : (x : α) → Acc r x → Sort v),
      (x : α) → (h : ∀ y, r y x → Acc r y) →
        ((y : α) → (hy : r y x) → motive y (h y hy)) →
        motive x (Acc.intro x h)) := rfl

-- **the recursor type, against Lean's own `Acc.rec`**
example : swap01 (accDecl.recType 0) = (vconst(type_of% @Acc.rec)).type := rfl
example : accDecl.recUvars = (vconst(type_of% @Acc.rec)).uvars := rfl

-- the ι-rule
example : swap01 (mkLams (accDecl.iotaCtx accIntro) ((accDecl.ihValues accIntro)[0]!)) =
    vexpr(fun (α : Sort u) (r : α → α → Prop) (motive : (x : α) → Acc r x → Sort v)
      (ih : (x : α) → (h : ∀ y, r y x → Acc r y) →
        ((y : α) → (hy : r y x) → motive y (h y hy)) → motive x (Acc.intro x h))
      (x : α) (h : ∀ y, r y x → Acc r y) =>
      fun (y : α) (hy : r y x) => @Acc.rec α r motive ih y (h y hy)) := rfl

example : swap01 (accDecl.iotaLam 0 accIntro) =
    vexpr(fun (α : Sort u) (r : α → α → Prop) (motive : (x : α) → Acc r x → Sort v)
      (ih : (x : α) → (h : ∀ y, r y x → Acc r y) →
        ((y : α) → (hy : r y x) → motive y (h y hy)) → motive x (Acc.intro x h))
      (x : α) (h : ∀ y, r y x → Acc r y) =>
      ih x h (fun (y : α) (hy : r y x) => @Acc.rec α r motive ih y (h y hy))) := rfl

example : swap01 (mkLams (accDecl.iotaCtx accIntro) (accDecl.iotaLhs 0 accIntro)) =
    vexpr(fun (α : Sort u) (r : α → α → Prop) (motive : (x : α) → Acc r x → Sort v)
      (ih : (x : α) → (h : ∀ y, r y x → Acc r y) →
        ((y : α) → (hy : r y x) → motive y (h y hy)) → motive x (Acc.intro x h))
      (x : α) (h : ∀ y, r y x → Acc r y) =>
      @Acc.rec α r motive ih x (Acc.intro x h)) := rfl

/-- `Acc : Prop` again needs `LECond`'s second disjunct.  Field 0 (`x`) is *not* a proof,
but it occurs among the constructor's result indices; field 1 (`h`) is a proof. -/
example : accDecl.LECond := by
  refine .inr ⟨accType, rfl, .inr ⟨accIntro, rfl, ?_⟩⟩
  rintro (_ | _ | i) F h
  · exact .inr (.head _)
  · exact .inl (by simp [accIntro] at h; subst h; rfl)
  · simp [accIntro] at h

/-! ## A two-type mutual block -/

mutual
inductive Tree' where
  | node : Forest' → Tree'
inductive Forest' where
  | nil : Forest'
  | cons : Tree' → Forest' → Forest'
end

def treeNode : VIndCtor where
  name := ``Tree'.node
  params := []
  fields := [{ type := .const ``Forest' [], lvl := .succ .zero,
               recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

def forestNil : VIndCtor where
  name := ``Forest'.nil
  params := []
  fields := []
  args := []

def forestCons : VIndCtor where
  name := ``Forest'.cons
  params := []
  fields :=
    [{ type := .const ``Tree' [], lvl := .succ .zero,
       recArg := some { binders := [], idx := 0, args := [] } },
     { type := .const ``Forest' [], lvl := .succ .zero,
       recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

def mutDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := true
  types :=
    [{ name := ``Tree', type := .sort (.succ .zero), indices := [], ctors := [treeNode] },
     { name := ``Forest', type := .sort (.succ .zero), indices := [],
       ctors := [forestNil, forestCons] }]

example : mutDecl.nm = 2 := rfl
example : mutDecl.nmin = 3 := rfl
example : mutDecl.ctorsAll = [(0, treeNode), (1, forestNil), (1, forestCons)] := rfl
example : mutDecl.recUvars = 1 := rfl
example : mutDecl.allNames =
    [``Tree', ``Forest',
     ``Tree'.node, ``Forest'.nil, ``Forest'.cons,
     ``Tree'.rec, ``Forest'.rec] := rfl
example : mutDecl.allConsts.map (·.2) =
    [⟨0, vexpr(Type)⟩, ⟨0, vexpr(Type)⟩,
     ⟨0, treeNode.type mutDecl 0⟩, ⟨0, forestNil.type mutDecl 1⟩,
     ⟨0, forestCons.type mutDecl 1⟩,
     ⟨1, mutDecl.recType 0⟩, ⟨1, mutDecl.recType 1⟩] := rfl

example : treeNode.type mutDecl 0 = (vconst(type_of% @Tree'.node)).type := rfl
example : forestNil.type mutDecl 1 = (vconst(type_of% @Forest'.nil)).type := rfl
example : forestCons.type mutDecl 1 = (vconst(type_of% @Forest'.cons)).type := rfl

example : mutDecl.motives = [vexpr(Tree' → Sort u), vexpr(Forest' → Sort u)] := rfl

example : mkPi (minorPreCtx mutDecl 0) (mutDecl.minorType 0 0 treeNode) =
    vexpr(∀ (m1 : Tree' → Sort u) (m2 : Forest' → Sort u),
      (f : Forest') → m2 f → m1 (Tree'.node f)) := rfl
example : mkPi (minorPreCtx mutDecl 1) (mutDecl.minorType 1 1 forestNil) =
    vexpr(∀ (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)), m2 Forest'.nil) := rfl
example : mkPi (minorFieldCtx mutDecl 2 forestCons) ((mutDecl.ihTypes 2 forestCons)[0]!) =
    vexpr(∀ (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil)
      (t : Tree') (f : Forest'), m1 t) := rfl
example : mkPi (minorFieldCtx mutDecl 2 forestCons ++ (mutDecl.ihTypes 2 forestCons).take 1)
      ((mutDecl.ihTypes 2 forestCons)[1]!) =
    vexpr(∀ (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil)
      (t : Tree') (f : Forest') (ih0 : m1 t), m2 f) := rfl
example : mkPi (minorPreCtx mutDecl 2) (mutDecl.minorType 2 1 forestCons) =
    vexpr(∀ (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil),
      (t : Tree') → (f : Forest') → m1 t → m2 f → m2 (Forest'.cons t f)) := rfl

-- **both recursor types, against Lean's own mutual recursors**
example : mutDecl.recType 0 = (vconst(type_of% @Tree'.rec)).type := rfl
example : mutDecl.recType 1 = (vconst(type_of% @Forest'.rec)).type := rfl

-- the ι-rules of the mutual block
example : mutDecl.iotaLam 0 treeNode =
    vexpr(fun (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil)
      (e2 : (t : Tree') → (f : Forest') → m1 t → m2 f → m2 (Forest'.cons t f))
      (f : Forest') => e0 f (@Forest'.rec m1 m2 e0 e1 e2 f)) := rfl
example : mkLams (mutDecl.iotaCtx treeNode) (mutDecl.iotaLhs 0 treeNode) =
    vexpr(fun (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil)
      (e2 : (t : Tree') → (f : Forest') → m1 t → m2 f → m2 (Forest'.cons t f))
      (f : Forest') => @Tree'.rec m1 m2 e0 e1 e2 (Tree'.node f)) := rfl

example : mutDecl.iotaLam 1 forestNil =
    vexpr(fun (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil)
      (e2 : (t : Tree') → (f : Forest') → m1 t → m2 f → m2 (Forest'.cons t f)) => e1) := rfl
example : mkLams (mutDecl.iotaCtx forestNil) (mutDecl.iotaLhs 1 forestNil) =
    vexpr(fun (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil)
      (e2 : (t : Tree') → (f : Forest') → m1 t → m2 f → m2 (Forest'.cons t f)) =>
      @Forest'.rec m1 m2 e0 e1 e2 Forest'.nil) := rfl

example : mutDecl.iotaLam 2 forestCons =
    vexpr(fun (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil)
      (e2 : (t : Tree') → (f : Forest') → m1 t → m2 f → m2 (Forest'.cons t f))
      (t : Tree') (f : Forest') =>
      e2 t f (@Tree'.rec m1 m2 e0 e1 e2 t) (@Forest'.rec m1 m2 e0 e1 e2 f)) := rfl
example : mkLams (mutDecl.iotaCtx forestCons) (mutDecl.iotaLhs 1 forestCons) =
    vexpr(fun (m1 : Tree' → Sort u) (m2 : Forest' → Sort u)
      (e0 : (f : Forest') → m2 f → m1 (Tree'.node f)) (e1 : m2 Forest'.nil)
      (e2 : (t : Tree') → (f : Forest') → m1 t → m2 f → m2 (Forest'.cons t f))
      (t : Tree') (f : Forest') =>
      @Forest'.rec m1 m2 e0 e1 e2 (Forest'.cons t f)) := rfl

/-! ## `addInduct'` bookkeeping -/

example : (VEnv.empty.addIndTypes natDecl).isSome := rfl
example : (VEnv.empty.addInduct' natDecl).isSome := rfl
example : (VEnv.empty.addInduct' mutDecl).isSome := rfl
example : (VEnv.empty.addInduct' accDecl).isSome := rfl
example : (VEnv.empty.addInduct' eqDecl).isSome := rfl

/-! ## `atRec`: the block-to-recursor universe renumbering -/

example : eqDecl.atRecTele eqDecl.params = [.sort (.param 1), .bvar 0] := rfl
example : natDecl.atRecTele natDecl.params = [] := rfl
example : accDecl.atRecTele accDecl.params
    = [.sort (.param 1), mkPi [.bvar 0, .bvar 1] (.sort .zero)] := rfl
-- `atRec_tyApp` on the nose
example : eqDecl.atRec (eqDecl.tyApp 0 0 [.bvar 0]) = eqDecl.tyApp' 0 0 [.bvar 0] := rfl
example : accDecl.atRec (accDecl.tyApp 0 2 [.bvar 1]) = accDecl.tyApp' 0 2 [.bvar 1] := rfl
-- for a `uvars = 0` block it is the identity on the recursor construction's inputs
example : mutDecl.atRecTele (treeNode.fields.map (·.type)) = [.const ``Forest' []] := rfl

/-! ## Staging bookkeeping -/

example : eqDecl.allNames.Nodup := by decide
example : natDecl.allNames.Nodup := by decide
example : accDecl.allNames.Nodup := by decide
example : mutDecl.allNames.Nodup := by decide

example : natDecl.typeConsts = [(``Nat, ⟨0, vexpr(Type)⟩)] := rfl
example : natDecl.ctorConsts =
    [(``Nat.zero, ⟨0, vconst(type_of% @Nat.zero).type⟩),
     (``Nat.succ, ⟨0, vconst(type_of% @Nat.succ).type⟩)] := rfl
example : natDecl.recConsts = [(``Nat.rec, ⟨1, vconst(type_of% @Nat.rec).type⟩)] := rfl

-- `mem_ctorsAll` on the mutual block: `Forest'.cons` is the `q = 2` constructor of type 1
example : ∃ T, mutDecl.types[1]? = some T ∧ forestCons ∈ T.ctors :=
  VInductDecl'.mem_ctorsAll (D := mutDecl) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

-- the accessors, concretely
example (env : VEnv) (h : VEnv.empty.addInduct' natDecl = some env) :
    env.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addInduct'_types h (.head _)

example (env : VEnv) (h : VEnv.empty.addInduct' natDecl = some env) :
    env.constants ``Nat.succ = some ⟨0, natSucc.type natDecl 0⟩ :=
  VEnv.addInduct'_ctors h (.tail _ (.head _))

example (env : VEnv) (h : VEnv.empty.addInduct' natDecl = some env) :
    env.constants (Lean.mkRecName ``Nat) = some ⟨1, natDecl.recType 0⟩ :=
  VEnv.addInduct'_recs h (.head _)

example (env : VEnv) (h : VEnv.empty.addInduct' mutDecl = some env) :
    env.constants ``Forest'.cons = some ⟨0, forestCons.type mutDecl 1⟩ :=
  VEnv.addInduct'_ctors h (.tail _ (.tail _ (.head _)))

example (env : VEnv) (h : VEnv.empty.addInduct' mutDecl = some env) :
    env.constants (Lean.mkRecName ``Forest') = some ⟨1, mutDecl.recType 1⟩ :=
  VEnv.addInduct'_recs h (.tail _ (.head _))

-- a name the block does not declare is untouched
example (env : VEnv) (h : VEnv.empty.addInduct' natDecl = some env) :
    env.constants ``List = none :=
  VEnv.addInduct'_constants_of_not_mem h (by decide)

-- the ι-rules are all present
example (env : VEnv) (h : VEnv.empty.addInduct' mutDecl = some env) :
    env.defeqs (mutDecl.iotaRule 1 2 forestCons) :=
  VEnv.addInduct'_defeqs h _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-! ## The recursor chain: shapes consumed by `tyApp'_hasType` / `motiveType_isType`

`HasType.appBVars₂` concludes at the term `f.mkApp (bvars (|Bs| + m) |As| ++ bvars 0 |Bs|)`.
These check that `tyApp'` really is that term, at the offsets `motiveType` and `recType`
use -- i.e. that D1's statement is about the construction and not about a near miss. -/

-- `Acc`: parameters at offset `ni + t = 1 + 0`, the single index at offset 0
example : accDecl.tyApp' 0 (accType.indices.length + 0) (bvars 0 accType.indices.length)
    = (VExpr.const ``Acc accDecl.selfLvls).mkApp
        (bvars (accType.indices.length + 0) (accDecl.atRecTele accDecl.params).length
          ++ bvars 0 (accDecl.atRecTele accType.indices).length) := rfl

-- `Eq`: same, one parameter block of length 2
example : eqDecl.tyApp' 0 (eqType.indices.length + 0) (bvars 0 eqType.indices.length)
    = (VExpr.const ``Eq eqDecl.selfLvls).mkApp
        (bvars (eqType.indices.length + 0) (eqDecl.atRecTele eqDecl.params).length
          ++ bvars 0 (eqDecl.atRecTele eqType.indices).length) := rfl

-- the mutual block exercises `m = t = 1`: motive 2's major premise sits one binder
-- above motive 1
example : mutDecl.motiveType 1 = .forallE (mutDecl.tyApp' 1 (0 + 1) []) (.sort mutDecl.elimLvl) :=
  rfl
example : mutDecl.tyApp' 1 (0 + 1) []
    = (VExpr.const ``Forest' mutDecl.selfLvls).mkApp
        (bvars (0 + 1) (mutDecl.atRecTele mutDecl.params).length ++ bvars 0 0) := rfl

-- `motiveType`'s telescope decomposition, as `IsType.mkPi` sees it
example : accDecl.motiveType 0
    = mkPi (liftTele 0 (accDecl.atRecTele accType.indices))
        (.forallE (accDecl.tyApp' 0 (accType.indices.length + 0)
          (bvars 0 accType.indices.length)) (.sort accDecl.elimLvl)) := rfl

-- `onCtxMotives` iterates over exactly `D.motives`
example : (List.range mutDecl.nm).map mutDecl.motiveType = mutDecl.motives := rfl
example : (List.range 1).map mutDecl.motiveType = mutDecl.motives.take 1 := rfl

-- `elimLvl_wf`, concretely
example : eqDecl.elimLvl.WF eqDecl.recUvars := by decide
example : natDecl.elimLvl.WF natDecl.recUvars := by decide
example : accDecl.elimLvl.WF accDecl.recUvars := by decide
example : mutDecl.elimLvl.WF mutDecl.recUvars := by decide

-- `getD_types`
example : mutDecl.types.getD 1 default = mutDecl.types[1]! := rfl

/-! ### D4's missing premise, validated as a *statement*

D4 must type `motive_{r.idx} π (fieldᵢ x)`, which needs each `π_u` typed against
`I_{r.idx}`'s index telescope.  That telescope, moved into the context
`ξ.reverse ++ (fields<i).reverse ++ params.reverse` where the parameters sit `|ξ| + i`
binders up, is `liftTele (|ξ| + i) T'.indices`.  These check that it lines up with what
`Lookup` actually assigns to `r.args` -- i.e. that the proposed `args_ty` premise is the
right statement, not a guess. -/

-- `Acc.intro`'s recursive field: `h : ∀ y, r y x → Acc α r y`, so `π = [y]` and the index
-- type is `α`, which in `[r y x, α, x, r, α]` is `.bvar 4` -- exactly `Lookup … 1`.
example : liftTele (accIntroRec.binders.length + 1) accType.indices = [VExpr.bvar 4] := rfl
example : accIntroRec.args = [VExpr.bvar 1] := rfl
-- and the constructor's own result indices: `x : α`, `α` is `.bvar 3` in `[h, x, r, α]`
example : liftTele accIntro.fields.length accType.indices = [VExpr.bvar 3] := rfl
example : accIntro.args = [VExpr.bvar 1] := rfl
-- `Eq.refl`: `a : α`, and `α` is `.bvar 1` in `[a, α]`
example : liftTele eqRefl.fields.length eqType.indices = [VExpr.bvar 1] := rfl
example : eqRefl.args = [VExpr.bvar 0] := rfl
-- index-free blocks: the premise is vacuous
example : liftTele natSucc.fields.length (natDecl.types[0]!).indices = [] := rfl
example : liftTele forestCons.fields.length (mutDecl.types[1]!).indices = [] := rfl

/-! ### `HasArgs.bvars` and the `bvars_add₃` split used by `ihValues` / E1–E5

`HasArgs.bvars` feeds `mkApp'` the telescope `liftTele (k + |As|) As`.  For the parameter
block that is a no-op (parameters are closed), which is what makes the recursor's spines
simple; for the index block it genuinely shifts. -/

example : liftTele 5 (accDecl.atRecTele accDecl.params) = accDecl.atRecTele accDecl.params := rfl
example : liftTele 5 (eqDecl.atRecTele eqDecl.params) = eqDecl.atRecTele eqDecl.params := rfl
-- the index telescope is not closed, so it does move
example : liftTele 3 (accDecl.atRecTele accType.indices) = [VExpr.bvar 4] := rfl
example : liftTele 2 (accDecl.atRecTele accType.indices) = [VExpr.bvar 3] := rfl

/-- `ihValues` applies `I_{r.idx}.rec` to three consecutive variable blocks -- parameters,
motives, minors.  They are contiguous in the context, so `bvars_add₃` collapses them into a
single spine for the concatenated telescope; without that, `mkApp'` would need three
separate `HasArgs`.  Checked on `Acc` (`nxi = nf = 2`) and on the mutual block
(`nxi = 0`, `nf = 1`). -/
example : bvars (2 + 2 + (accDecl.nm + accDecl.nmin)) accDecl.np
      ++ bvars (2 + 2 + accDecl.nmin) accDecl.nm ++ bvars (2 + 2) accDecl.nmin
    = bvars (2 + 2) (accDecl.np + accDecl.nm + accDecl.nmin) := rfl

example : bvars (0 + 1 + (mutDecl.nm + mutDecl.nmin)) mutDecl.np
      ++ bvars (0 + 1 + mutDecl.nmin) mutDecl.nm ++ bvars (0 + 1) mutDecl.nmin
    = bvars (0 + 1) (mutDecl.np + mutDecl.nm + mutDecl.nmin) := rfl

example : bvars (0 + 1 + (natDecl.nm + natDecl.nmin)) natDecl.np
      ++ bvars (0 + 1 + natDecl.nmin) natDecl.nm ++ bvars (0 + 1) natDecl.nmin
    = bvars (0 + 1) (natDecl.np + natDecl.nm + natDecl.nmin) := rfl

-- and the corresponding telescope really is the concatenation `recType` binds
example : mutDecl.recType 0 = mkPi (mutDecl.atRecTele mutDecl.params ++ mutDecl.motives
      ++ mutDecl.minors ++ liftTele (mutDecl.nm + mutDecl.nmin)
        (mutDecl.atRecTele (mutDecl.types[0]!).indices))
    (.forallE (mutDecl.tyApp' 0 (0 + mutDecl.nmin + mutDecl.nm) (bvars 0 0))
      ((VExpr.bvar (1 + 0 + mutDecl.nmin + (mutDecl.nm - 1 - 0))).mkApp
        (bvars 1 0 ++ [.bvar 0]))) := rfl

/-! ### The D4 offset cross-check, instantiated

`VInductDecl'.ih_param_offset` says the two independent routes to the block's parameters
inside an induction hypothesis land on the same de Bruijn offset.  Instantiated below; the
companion `rfl`s pin the concrete numbers, and the `ihTypes` checks earlier in this file
already confirmed by comparison with a `vexpr` that the motive index really names the
motive (`.bvar 4` is `motive` for `Acc`, `.bvar 5` is `m2` for `Forest'.cons`). -/

-- `Acc.intro`'s recursive field: `nxi = 2, i = 1, s = 0, nf = 2, q = 0, nm = 1`
example : accIntroRec.binders.length + 1 + (accDecl.nm + 0)
      + (accIntro.fields.length - 1 + 0)
    = accIntroRec.binders.length + 0 + accIntro.fields.length + 0 + accDecl.nm :=
  VInductDecl'.ih_param_offset (by decide)
-- parameters at 5, motive `r.idx` at 4
example : (accIntroRec.binders.length + 0 + accIntro.fields.length + 0 + accDecl.nm,
      accIntroRec.binders.length + 0 + accIntro.fields.length + 0
        + (accDecl.nm - 1 - accIntroRec.idx)) = (5, 4) := rfl

-- `Forest'.cons`'s *second* recursive field, the `s ≠ 0` case:
-- `nxi = 0, i = 1, s = 1, nf = 2, q = 2, nm = 2`
example : 0 + 1 + (mutDecl.nm + 2) + (forestCons.fields.length - 1 + 1)
    = 0 + 1 + forestCons.fields.length + 2 + mutDecl.nm :=
  VInductDecl'.ih_param_offset (by decide)
-- parameters at 7 (vacuous, `np = 0`), motive `1` at 5
example : (0 + 1 + forestCons.fields.length + 2 + mutDecl.nm,
      0 + 1 + forestCons.fields.length + 2 + (mutDecl.nm - 1 - 1)) = (7, 5) := rfl

/-! ### The telescope identification, checked against a hand computation

For `Acc.intro`'s recursive field: `X = [α]`, `a = nxi + i = 3`, `off = nm + q = 1`,
`d = nf - i + s = 1`, `nxi = 2`; and on the other side `u = r.idx = 0`, `L = m_idx + 1 = 5`.
Route A lifts `[.bvar 1]` to `[.bvar 4]`, then `[.bvar 5]`, then `[.bvar 6]`; route B lifts
it straight to `[.bvar 6]`.  Both the lemma and the arithmetic are checked. -/

example : liftTele 1 (liftTele 1 (liftTele 3 (accDecl.atRecTele accType.indices) 0) 3) 2
    = [VExpr.bvar 6] := rfl
example : liftTele 5 (liftTele 0 (accDecl.atRecTele accType.indices) 0) 0
    = [VExpr.bvar 6] := rfl
example : liftTele 1 (liftTele 1 (liftTele 3 (accDecl.atRecTele accType.indices) 0) 3) 2
    = liftTele 5 (liftTele 0 (accDecl.atRecTele accType.indices) 0) 0 :=
  VInductDecl'.ih_telescope_eq (by omega) (by omega)

-- the same for `Forest'.cons`'s second recursive field (`s = 1`), where the index
-- telescope is empty so both routes are trivially `[]`
example : liftTele 2 (liftTele 4 (liftTele 1 (mutDecl.atRecTele (mutDecl.types[1]!).indices) 0) 1) 0
    = liftTele 6 (liftTele 1 (mutDecl.atRecTele (mutDecl.types[1]!).indices) 0) 0 :=
  VInductDecl'.ih_telescope_eq (by omega) (by omega)

/-! ### `instAll` on the recursor's spine

Applying `I` to `bvars L np ++ bvars 0 ni` and then instantiating the `ni` index arguments
by genuine terms `π` shifts the parameter block down by `ni` and returns `π` itself.  With
`Acc`'s `π = [y] = [.bvar 1]` and the parameter block at 6: -/

example : (bvars 6 accDecl.np).map (VExpr.instAll · [VExpr.bvar 1] 0)
    = bvars 5 accDecl.np := VExpr.map_instAll_bvars_ge (by decide)
example : (bvars 6 accDecl.np).map (VExpr.instAll · [VExpr.bvar 1] 0)
    = [VExpr.bvar 6, VExpr.bvar 5] := rfl
example : (bvars 0 accIntroRec.args.length).map (VExpr.instAll · accIntroRec.args 0)
    = accIntroRec.args := VExpr.map_instAll_bvars _
example : (bvars 0 1).map (VExpr.instAll · [VExpr.bvar 1] 0) = [VExpr.bvar 1] := rfl

/-! ### `ParamsExtra.ctor_ty`'s arity clauses

The pi-arity of a stored constructor type is exactly `|C.params| + |C.fields|` -- exact
because the result is an application, never a `∀`. -/

example : (accIntro.type accDecl 0).piArity
    = (accIntro.params ++ accIntro.fields.map (·.type)).length :=
  VIndCtor.type_piArity _ _ _
example : (accIntro.type accDecl 0).piArity = 4 := rfl
example : (eqRefl.type eqDecl 0).piArity = 2 := rfl
example : (natZero.type natDecl 0).piArity = 0 := rfl
example : (forestCons.type mutDecl 1).piArity = 2 := rfl

/-- The head-arity of a constructor's result is `D.np + |C.args|`.  The clause is stated
per-constructor but `classify T.name` is not, so what makes it well defined is
`VIndCtor.WF.args_len`: **two constructors of the same type must agree**.  Checked on the
two blocks that have more than one constructor per type. -/
example : (accIntro.canonResult accDecl 0).appArity = accDecl.np + accIntro.args.length := rfl
example : (accIntro.canonResult accDecl 0).appArity
    = accDecl.np + accType.indices.length := rfl
example : (natZero.canonResult natDecl 0).appArity
    = (natSucc.canonResult natDecl 0).appArity := rfl
example : (forestNil.canonResult mutDecl 1).appArity
    = (forestCons.canonResult mutDecl 1).appArity := rfl

/-! ### D6's body: the two offset identities and the `instAll` computation

`Acc` (`j = 0, ni = 1, nm = nmin = 1`, so `K = 3`) and `Forest'.rec` (`j = 1, ni = 0,
nm = 2, nmin = 3`, so `K = 4`). -/

example : accDecl.nm + accDecl.nmin + (1 + accType.indices.length)
    = 0 + (1 + accType.indices.length + accDecl.nmin + (accDecl.nm - 1 - 0) + 1) :=
  VInductDecl'.rec_tele_offset (by decide)
example : 1 + accType.indices.length + accDecl.nmin + (accDecl.nm - 1 - 0) + 1 + 0
    = 1 + accType.indices.length + accDecl.nmin + accDecl.nm :=
  VInductDecl'.rec_dom_offset (by decide)

example : mutDecl.nm + mutDecl.nmin + (1 + (mutDecl.types[1]!).indices.length)
    = 1 + (1 + (mutDecl.types[1]!).indices.length + mutDecl.nmin + (mutDecl.nm - 1 - 1) + 1) :=
  VInductDecl'.rec_tele_offset (by decide)
example : 1 + (mutDecl.types[1]!).indices.length + mutDecl.nmin + (mutDecl.nm - 1 - 1) + 1 + 1
    = 1 + (mutDecl.types[1]!).indices.length + mutDecl.nmin + mutDecl.nm :=
  VInductDecl'.rec_dom_offset (by decide)

/-- The `instAll` computation, by hand: `Acc α r x` at the motive's offsets lifts to
`[.bvar 6, .bvar 5, .bvar 0]`, then instantiating the single index argument by `[.bvar 1]`
shifts the parameter block down by one and returns the index — `[.bvar 5, .bvar 4, .bvar 1]`
— which is exactly the major premise's own type. -/
example : VExpr.instAll ((accDecl.tyApp' 0 (1 + 0) (bvars 0 1)).liftN (3 + 1) 1)
      (bvars 1 1) 0
    = (accDecl.tyApp' 0 (1 + accDecl.nmin + accDecl.nm) (bvars 0 1)).liftN 1 0 :=
  VInductDecl'.tyApp'_instAll_bvars (by decide)
example : VExpr.instAll ((accDecl.tyApp' 0 (1 + 0) (bvars 0 1)).liftN (3 + 1) 1) (bvars 1 1) 0
    = (VExpr.const ``Acc accDecl.selfLvls).mkApp
        [VExpr.bvar 5, VExpr.bvar 4, VExpr.bvar 1] := rfl

-- `motiveApp_hasType`'s subject is literally `recType`'s body
example : accDecl.recType 0
    = mkPi (accDecl.atRecTele accDecl.params ++ accDecl.motives ++ accDecl.minors
        ++ liftTele (accDecl.nm + accDecl.nmin) (accDecl.atRecTele accType.indices))
      (.forallE (accDecl.tyApp' 0 (accType.indices.length + accDecl.nmin + accDecl.nm)
          (bvars 0 accType.indices.length))
        ((VExpr.bvar (1 + accType.indices.length + accDecl.nmin + (accDecl.nm - 1 - 0))).mkApp
          (bvars 1 accType.indices.length ++ [.bvar 0]))) := rfl

/-! ### D5's body: `minorBody_hasType`'s subject is `minorType`'s body

For `Acc.intro` (`q = t = 0`, so `nr = 1`, `nf = 2`, `off = nm + q = 1`, and the motive
index is `nr + nf + q + (nm-1-t) = 3`). -/

example : (accDecl.ihTypes 0 accIntro).length = 1 := rfl
example : accDecl.minorType 0 0 accIntro
    = mkPi (liftTele 1 (accDecl.atRecTele (accIntro.fields.map (·.type)))
        ++ accDecl.ihTypes 0 accIntro)
      ((VExpr.bvar 3).mkApp
        ((accIntro.args.map fun a => VExpr.shift 1 1 2 (accDecl.atRec a))
          ++ [accDecl.ctorApp' accIntro 4 (bvars 1 2)])) := rfl

-- the two minor offsets, on `Acc.intro` and on `Forest'.cons` (`q = 2, t = 1, nr = nf = 2`)
example : accIntro.fields.length + (accDecl.nm + 0) + (accDecl.ihTypes 0 accIntro).length
    = 0 + ((accDecl.ihTypes 0 accIntro).length + accIntro.fields.length + 0
        + (accDecl.nm - 1 - 0) + 1) :=
  VInductDecl'.minor_tele_offset (by decide)
example : ((accDecl.ihTypes 0 accIntro).length + accIntro.fields.length + 0
      + (accDecl.nm - 1 - 0)) + 1 + (accType.indices.length + 0) - accType.indices.length
    = (accDecl.ihTypes 0 accIntro).length + accIntro.fields.length + (accDecl.nm + 0) :=
  VInductDecl'.minor_dom_offset (by decide)

example : (mutDecl.ihTypes 2 forestCons).length = 2 := rfl
example : forestCons.fields.length + (mutDecl.nm + 2) + (mutDecl.ihTypes 2 forestCons).length
    = 1 + ((mutDecl.ihTypes 2 forestCons).length + forestCons.fields.length + 2
        + (mutDecl.nm - 1 - 1) + 1) :=
  VInductDecl'.minor_tele_offset (by decide)
example : ((mutDecl.ihTypes 2 forestCons).length + forestCons.fields.length + 2
      + (mutDecl.nm - 1 - 1)) + 1 + ((mutDecl.types[1]!).indices.length + 1)
      - (mutDecl.types[1]!).indices.length
    = (mutDecl.ihTypes 2 forestCons).length + forestCons.fields.length + (mutDecl.nm + 2) :=
  VInductDecl'.minor_dom_offset (by decide)

/-! ### D6: the decomposition `IsType.mkPi` performs on `recType`

`recType`'s telescope reverses into the context `recType_isType` builds:
indices, then minors, then motives, then parameters. -/

example : (accDecl.atRecTele accDecl.params ++ accDecl.motives ++ accDecl.minors
      ++ liftTele (accDecl.nm + accDecl.nmin) (accDecl.atRecTele accType.indices)).reverse
    = (liftTele (accDecl.nm + accDecl.nmin) (accDecl.atRecTele accType.indices)).reverse
      ++ (accDecl.minors.reverse ++ accDecl.motives.reverse
          ++ (accDecl.atRecTele accDecl.params).reverse) := rfl

example : (accDecl.atRecTele accDecl.params ++ accDecl.motives ++ accDecl.minors
      ++ liftTele (accDecl.nm + accDecl.nmin)
        (accDecl.atRecTele accType.indices)).reverse.length
    = accDecl.np + accDecl.nm + accDecl.nmin + accType.indices.length := rfl

/-- `Forest'.rec` pins the motive index in the `j ≠ 0` case: `1 + ni + nmin + (nm-1-j)`
is `1 + 0 + 3 + 0 = 4`.  Since `mutDecl.recType 1` was already checked equal to
`vconst(type_of% @Forest'.rec)`, this confirms `.bvar 4` really names `m2`. -/
example : mutDecl.recType 1
    = mkPi (mutDecl.atRecTele mutDecl.params ++ mutDecl.motives ++ mutDecl.minors
        ++ liftTele (mutDecl.nm + mutDecl.nmin)
          (mutDecl.atRecTele (mutDecl.types[1]!).indices))
      (.forallE (mutDecl.tyApp' 1
          ((mutDecl.types[1]!).indices.length + mutDecl.nmin + mutDecl.nm)
          (bvars 0 (mutDecl.types[1]!).indices.length))
        ((VExpr.bvar 4).mkApp
          (bvars 1 (mutDecl.types[1]!).indices.length ++ [.bvar 0]))) := rfl

-- and `lookup_motive`'s index for that case: `Δ = major :: indices ++ minors`, so
-- `Δ.length + (nm-1-j) = (1 + 0 + 3) + 0 = 4`
example : (1 + (mutDecl.types[1]!).indices.length + mutDecl.nmin) + (mutDecl.nm - 1 - 1)
    = 4 := rfl

/-! ### The constructor interface for `ctor_ty`

`args_len`, and the fact that the result head carries the block's *own* universe parameters
— so `instL ls` puts exactly `ls` there, which a consumer rebuilding the spine at a
different level list needs. -/

example : accIntro.args.length = accType.indices.length := rfl
example : eqRefl.args.length = eqType.indices.length := rfl
example : forestCons.args.length = (mutDecl.types[1]!).indices.length := rfl

example : (accIntro.canonResult accDecl 0).instL [.param 5]
    = (VExpr.const ``Acc [.param 5]).mkApp
        (bvars accIntro.fields.length accDecl.np
          ++ accIntro.args.map (VExpr.instL [.param 5])) :=
  VIndCtor.canonResult_instL _ _ _ rfl
example : (accIntro.canonResult accDecl 0).instL [.param 5]
    = (VExpr.const ``Acc [.param 5]).mkApp
        [VExpr.bvar 3, VExpr.bvar 2, VExpr.bvar 1] := rfl
example : (eqRefl.canonResult eqDecl 0).instL [.param 7]
    = (VExpr.const ``Eq [.param 7]).mkApp
        [VExpr.bvar 1, VExpr.bvar 0, VExpr.bvar 0] := rfl

-- the bundled interface, instantiated: every clause holds for `Acc.intro`
example : accIntro.args.length = accType.indices.length := rfl
example : (accIntro.type accDecl 0).piArity
    = accIntro.params.length + accIntro.fields.length := VIndCtor.type_piArity ..
example : (accIntro.canonResult accDecl 0).appArity
    = accDecl.np + accType.indices.length := rfl

/-! ### D4's body: `ihBody_hasType`'s subject is the `ihTypes` entry's body

`Acc.intro`'s recursive field: `i = 1, s = 0, nxi = 2, nf = 2, q = 0, nm = 1, r.idx = 0`,
so `off = 1`, `d = 1`, and the motive index `K = nxi + s + nf + q + (nm-1-r.idx) = 4`. -/

example : (accDecl.ihTypes 0 accIntro)[0]!
    = mkPi (shiftTele (accDecl.nm + 0) (accIntro.fields.length - 1 + 0) 1
        (accDecl.atRecTele accIntroRec.binders))
      ((VExpr.bvar 4).mkApp
        ((accIntroRec.args.map fun a =>
            VExpr.shift (accDecl.nm + 0) (accIntro.fields.length - 1 + 0) 1
              (accDecl.atRec a) accIntroRec.binders.length)
          ++ [(VExpr.bvar 2).mkApp (bvars 0 accIntroRec.binders.length)])) := rfl

/-- The offset identity `ihBody_hasType` turns on: `args_ty`'s parameter offset after both
weakenings, `nxi + i + off + d`, equals the motive's `K + 1 + r.idx`.  Both are 5 for
`Acc.intro`, and 7 for `Forest'.cons`'s second (`s = 1`) recursive field. -/
example : 2 + 1 + (accDecl.nm + 0) + (accIntro.fields.length - 1 + 0)
    = 4 + 1 + accIntroRec.idx := rfl
example : 0 + 1 + (mutDecl.nm + 2) + (forestCons.fields.length - 1 + 1) = 5 + 1 + 1 := rfl

/-! ### `ihTypes` entry/prefix plumbing

`getElem?` and `take` read back to `C.recFields`, with `ihType` naming the entry. -/

example : (accDecl.ihTypes 0 accIntro)[0]?
    = some (accDecl.ihType 0 accIntro 1 accIntroRec 0) := rfl
example : (accDecl.ihTypes 0 accIntro).length = accIntro.recFields.length := rfl
example : (accDecl.ihTypes 0 accIntro).take 0 = [] := rfl

-- the mutual block's two-recursive-field constructor, where `s` actually varies
example : forestCons.recFields
    = [(0, { binders := [], idx := 0, args := [] }),
       (1, { binders := [], idx := 1, args := [] })] := rfl
example : (mutDecl.ihTypes 2 forestCons)[1]?
    = some (mutDecl.ihType 2 forestCons 1 { binders := [], idx := 1, args := [] } 1) := rfl
example : (mutDecl.ihTypes 2 forestCons).take 1
    = [mutDecl.ihType 2 forestCons 0 { binders := [], idx := 0, args := [] } 0] := rfl

/-! ### Splitting the field telescope at `i`

The cut on the second block is `i`, not `0` — if it were `0` the later fields would be
shifted wrongly, so these `rfl`s pin it. -/

example : liftTele 1 (accDecl.atRecTele (accIntro.fields.map (·.type))) 0
    = liftTele 1 (accDecl.atRecTele ((accIntro.fields.map (·.type)).take 1)) 0
      ++ liftTele 1 (accDecl.atRecTele ((accIntro.fields.map (·.type)).drop 1)) 1 := rfl

example : liftTele 4 (mutDecl.atRecTele (forestCons.fields.map (·.type))) 0
    = liftTele 4 (mutDecl.atRecTele ((forestCons.fields.map (·.type)).take 1)) 0
      ++ liftTele 4 (mutDecl.atRecTele ((forestCons.fields.map (·.type)).drop 1)) 1 := rfl

-- `liftN_ihCtx`'s length side condition really is `d = nf - i + s`
example : ((accDecl.ihTypes 0 accIntro).take 0).length
      + ((accIntro.fields.map (·.type)).drop 1).length
    = accIntro.fields.length - 1 + 0 := rfl
example : ((mutDecl.ihTypes 2 forestCons).take 1).length
      + ((forestCons.fields.map (·.type)).drop 1).length
    = forestCons.fields.length - 1 + 1 := rfl

/-! ## `Nonempty` — the `isLE := false` case

The four blocks above are all large eliminators, so none of them exercises the
`isLE = false` path: `elimLvl = .zero`, `recUvars = uvars` (no fresh universe prepended),
`selfLvls = VLevel.params uvars` (the identity, so `atRec` is the identity and **no
`swap01` is needed**).  `Nonempty` is the prelude's small eliminator, and
`Theory/Consistency.lean`'s `nonemptyIndDecl` has to be expressible in this record. -/

def nonemptyIntro : VIndCtor where
  name := ``Nonempty.intro
  params := [.sort (.param 0)]
  fields := [{ type := .bvar 0, lvl := .param 0, recArg := none }]
  args := []

def nonemptyType : VIndType where
  name := ``Nonempty
  type := mkPi [.sort (.param 0)] (.sort .zero)
  indices := []
  ctors := [nonemptyIntro]

/-- `Nonempty.{u} : Sort u → Prop`, a **small** eliminator: its single field has level
`u`, which is not `≈ 0`, and there are no result indices for it to occur in — so `LECond`
fails and `isLE` must be `false`. -/
def nonemptyDecl : VInductDecl' where
  uvars := 1
  params := [.sort (.param 0)]
  lvl := .zero
  isLE := false
  types := [nonemptyType]

example : nonemptyDecl.isLE = false := rfl
example : nonemptyDecl.elimLvl = .zero := rfl
example : nonemptyDecl.recUvars = nonemptyDecl.uvars := rfl
example : nonemptyDecl.selfLvls = VLevel.params nonemptyDecl.uvars := rfl
-- `atRec` is the identity here, which is what makes `swap01` unnecessary below
example : nonemptyDecl.atRecTele nonemptyDecl.params = nonemptyDecl.params := rfl
example : nonemptyDecl.atRec (nonemptyDecl.tyApp 0 0 []) = nonemptyDecl.tyApp' 0 0 [] := rfl

example : nonemptyType.type = nonemptyType.canonType nonemptyDecl := rfl
example : nonemptyType.canonType nonemptyDecl = (vconst(type_of% @Nonempty)).type := rfl
example : nonemptyIntro.type nonemptyDecl 0 = (vconst(type_of% @Nonempty.intro)).type := rfl

-- **the recursor, against Lean's own `Nonempty.rec` — no level renaming**
example : nonemptyDecl.recType 0 = (vconst(type_of% @Nonempty.rec)).type := rfl
example : nonemptyDecl.recUvars = (vconst(type_of% @Nonempty.rec)).uvars := rfl

example : mkPi (motiveCtx nonemptyDecl 0) (nonemptyDecl.motiveType 0)
    = vexpr(∀ (α : Sort u), Nonempty α → Prop) := rfl
example : mkPi (minorPreCtx nonemptyDecl 0) (nonemptyDecl.minorType 0 0 nonemptyIntro)
    = vexpr(∀ (α : Sort u) (motive : Nonempty α → Prop),
        (a : α) → motive (Nonempty.intro a)) := rfl

-- the ι-rule
example : nonemptyDecl.ihValues nonemptyIntro = [] := rfl
example : nonemptyDecl.iotaLam 0 nonemptyIntro
    = vexpr(fun (α : Sort u) (motive : Nonempty α → Prop)
        (intro : (a : α) → motive (Nonempty.intro a)) (a : α) => intro a) := rfl
example : mkLams (nonemptyDecl.iotaCtx nonemptyIntro)
      (nonemptyDecl.iotaLhs 0 nonemptyIntro)
    = vexpr(fun (α : Sort u) (motive : Nonempty α → Prop)
        (intro : (a : α) → motive (Nonempty.intro a)) (a : α) =>
        @Nonempty.rec α motive intro (Nonempty.intro a)) := rfl

example : (VEnv.empty.addInduct' nonemptyDecl).isSome := rfl
example : nonemptyDecl.allNames = [``Nonempty, ``Nonempty.intro, ``Nonempty.rec] := rfl

/-! ## `Iff` — the third prelude literal

`uvars = 0` but `isLE = true`: both fields are proofs, so `LECond`'s second disjunct holds
and a fresh elimination universe *is* prepended (`recUvars = 1`), while `selfLvls = []`
because the block has no universes of its own. -/

def iffIntro : VIndCtor where
  name := ``Iff.intro
  params := [.sort .zero, .sort .zero]
  fields :=
    [{ type := mkPi [.bvar 1] (.bvar 1), lvl := .zero, recArg := none },
     { type := mkPi [.bvar 1] (.bvar 3), lvl := .zero, recArg := none }]
  args := []

def iffType : VIndType where
  name := ``Iff
  type := mkPi [.sort .zero, .sort .zero] (.sort .zero)
  indices := []
  ctors := [iffIntro]

def iffDecl : VInductDecl' where
  uvars := 0
  params := [.sort .zero, .sort .zero]
  lvl := .zero
  isLE := true
  types := [iffType]

example : iffDecl.uvars = 0 := rfl
example : iffDecl.recUvars = 1 := rfl
example : iffDecl.selfLvls = [] := rfl
example : iffDecl.elimLvl = .param 0 := rfl

example : iffType.type = iffType.canonType iffDecl := rfl
example : iffType.canonType iffDecl = (vconst(type_of% Iff)).type := rfl
example : iffIntro.type iffDecl 0 = (vconst(type_of% @Iff.intro)).type := rfl

-- **the recursor, against Lean's own `Iff.rec`**
example : iffDecl.recType 0 = (vconst(type_of% @Iff.rec)).type := rfl
example : iffDecl.recUvars = (vconst(type_of% @Iff.rec)).uvars := rfl

example : iffDecl.ihValues iffIntro = [] := rfl
example : iffDecl.iotaLam 0 iffIntro
    = vexpr(fun (a b : Prop) (motive : Iff a b → Sort u)
        (intro : (mp : a → b) → (mpr : b → a) → motive (Iff.intro mp mpr))
        (mp : a → b) (mpr : b → a) => intro mp mpr) := rfl

example : (VEnv.empty.addInduct' iffDecl).isSome := rfl

/-- All three of `Theory/Consistency.lean`'s prelude literals are expressible: `Eq`
(`isLE`, indices), `Iff` (`isLE`, `uvars = 0`), `Nonempty` (**not** `isLE`). -/
example : (VEnv.empty.addInduct' eqDecl).isSome
    ∧ (VEnv.empty.addInduct' iffDecl).isSome
    ∧ (VEnv.empty.addInduct' nonemptyDecl).isSome := ⟨rfl, rfl, rfl⟩

/-! ## `LvlWit` — a universe parameter inside a *field* type and an *index* type

**Why this block exists.**  Every other block in this file is blind to a whole class of
error: the one where `atRec`/`atRecTele` is *omitted* at one of the sites where a stored
telescope is spliced into a recursor-side term.  Catching that needs two conditions at once —
a universe parameter occurring in the spliced telescope, and a use at levels other than the
block's own, since at `ownLvls` the `instL` is the identity and the omission is invisible.

`Eq` and `Acc` cover the *parameter* telescope (`.sort (.param 0)` is a parameter type, and
both are `isLE`).  Nothing covered the other sites: no field type, index type or recursive
field's `ξ`/`π` anywhere above contains a universe parameter — `Nat`, `Tree'`/`Forest'` and
`Iff` have `uvars = 0`, `Nonempty` has `isLE := false` so `atRec` is the identity, and
`Eq`/`Acc` build every field and index type out of `bvar`/`app` alone.

`LvlWit` closes that gap.  It has no parameters at all, and puts a universe parameter in
*four* spliced positions: the index type (`Sort u`), a field type (`Sort u`), a recursive
field's `ξ`-binder (`Sort u`) and its `π` (`PUnit.{u}`).  It is `isLE`, so
`selfLvls = [.param 1] ≠ ownLvls = [.param 0]` and every `instL` here is non-trivial: drop
`atRec` at any one of those four sites and the checks below fail. -/
inductive LvlWit : Sort u → Type u where
  | mk (f : Sort u) (r : Sort u → LvlWit PUnit.{u}) : LvlWit PUnit.{u}
  | mk2 (β : Sort u) : LvlWit β

/-- `Sort u → LvlWit PUnit.{u}`: the recursive field of `LvlWit.mk`, whose `ξ`-binder *and*
whose index argument each carry a universe parameter. -/
def lvlMkRec : VIndRecArg where
  binders := [.sort (.param 0)]
  idx := 0
  args := [.const ``PUnit [.param 0]]

def lvlMk : VIndCtor where
  name := ``LvlWit.mk
  params := []
  fields :=
    [{ type := .sort (.param 0), lvl := .succ (.param 0), recArg := none },
     { type := mkPi lvlMkRec.binders
         ((VExpr.const ``LvlWit [.param 0]).mkApp [.const ``PUnit [.param 0]])
       lvl := .imax (.succ (.param 0)) (.succ (.param 0))
       recArg := some lvlMkRec }]
  args := [.const ``PUnit [.param 0]]

def lvlMk2 : VIndCtor where
  name := ``LvlWit.mk2
  params := []
  fields := [{ type := .sort (.param 0), lvl := .succ (.param 0), recArg := none }]
  args := [.bvar 0]

def lvlType : VIndType where
  name := ``LvlWit
  type := mkPi [.sort (.param 0)] (.sort (.succ (.param 0)))
  indices := [.sort (.param 0)]
  ctors := [lvlMk, lvlMk2]

/-- `LvlWit.{u} : Sort u → Type u`, with no parameters and one index. -/
def lvlDecl : VInductDecl' where
  uvars := 1
  params := []
  lvl := .succ (.param 0)
  isLE := true
  types := [lvlType]

example : lvlDecl.np = 0 := rfl
example : lvlDecl.nm = 1 := rfl
example : lvlDecl.nmin = 2 := rfl
example : lvlDecl.recUvars = 2 := rfl
-- the point of the block: `atRec` is *not* the identity here
example : lvlDecl.ownLvls = [.param 0] := rfl
example : lvlDecl.selfLvls = [.param 1] := rfl
example : lvlMk.recFields = [(1, lvlMkRec)] := rfl

example : lvlType.type = lvlType.canonType lvlDecl := rfl
example : lvlType.canonType lvlDecl = (vconst(type_of% @LvlWit)).type := rfl
example : (vconst(type_of% @LvlWit)).uvars = lvlDecl.uvars := rfl
example : lvlMk.type lvlDecl 0 = (vconst(type_of% @LvlWit.mk)).type := rfl
example : lvlMk2.type lvlDecl 0 = (vconst(type_of% @LvlWit.mk2)).type := rfl
example : (lvlMk.fields[1]!).type = lvlMkRec.canonType lvlDecl 1 := rfl

-- the motive and the two minor premises: `atRecTele` on the index telescope and on the
-- field types, at `selfLvls`
example : swap01 (mkPi (motiveCtx lvlDecl 0) (lvlDecl.motiveType 0)) =
    vexpr((a : Sort u) → LvlWit a → Sort v) := rfl
example : swap01 (mkPi (minorPreCtx lvlDecl 0) (lvlDecl.minorType 0 0 lvlMk)) =
    vexpr(∀ (motive : (a : Sort u) → LvlWit a → Sort v),
      (f : Sort u) → (r : Sort u → LvlWit PUnit.{u}) →
        ((a : Sort u) → motive PUnit.{u} (r a)) →
        motive PUnit.{u} (LvlWit.mk f r)) := rfl
example : swap01 (mkPi (minorPreCtx lvlDecl 1) (lvlDecl.minorType 1 0 lvlMk2)) =
    vexpr(∀ (motive : (a : Sort u) → LvlWit a → Sort v)
      (mk : (f : Sort u) → (r : Sort u → LvlWit PUnit.{u}) →
        ((a : Sort u) → motive PUnit.{u} (r a)) → motive PUnit.{u} (LvlWit.mk f r)),
      (β : Sort u) → motive β (LvlWit.mk2 β)) := rfl

-- **the recursor type, against Lean's own `LvlWit.rec`**
example : swap01 (lvlDecl.recType 0) = (vconst(type_of% @LvlWit.rec)).type := rfl
example : lvlDecl.recUvars = (vconst(type_of% @LvlWit.rec)).uvars := rfl

-- the ι-rules: `ihValues` splices the recursive field's `ξ` and `π`, both of which carry a
-- universe parameter here
example : swap01 (mkLams (lvlDecl.iotaCtx lvlMk) ((lvlDecl.ihValues lvlMk)[0]!)) =
    vexpr(fun (motive : (a : Sort u) → LvlWit a → Sort v)
      (mk : (f : Sort u) → (r : Sort u → LvlWit PUnit.{u}) →
        ((a : Sort u) → motive PUnit.{u} (r a)) → motive PUnit.{u} (LvlWit.mk f r))
      (mk2 : (β : Sort u) → motive β (LvlWit.mk2 β))
      (f : Sort u) (r : Sort u → LvlWit PUnit.{u}) =>
      fun (a : Sort u) => @LvlWit.rec motive mk mk2 PUnit.{u} (r a)) := rfl
example : swap01 (mkLams (lvlDecl.iotaCtx lvlMk) (lvlDecl.iotaLhs 0 lvlMk)) =
    vexpr(fun (motive : (a : Sort u) → LvlWit a → Sort v)
      (mk : (f : Sort u) → (r : Sort u → LvlWit PUnit.{u}) →
        ((a : Sort u) → motive PUnit.{u} (r a)) → motive PUnit.{u} (LvlWit.mk f r))
      (mk2 : (β : Sort u) → motive β (LvlWit.mk2 β))
      (f : Sort u) (r : Sort u → LvlWit PUnit.{u}) =>
      @LvlWit.rec motive mk mk2 PUnit.{u} (LvlWit.mk f r)) := rfl

example : (VEnv.empty.addInduct' lvlDecl).isSome := rfl

/-! ## A declaration that is well-formed — the predicate, not just the encoding

Everything above validates the *encoding*: `recType`, `iotaLhs`, `ihValues` and friends are
compared against Lean's own kernel by `rfl`.  None of it says that any declaration satisfies
`VInductDecl'.WF`, and until this section nothing in the tree did — `WF` had 36 consumers and
no witness.  That is the same gap that let four classes stay unsatisfiable this session: a
predicate nothing is ever asked to satisfy cannot be caught by anything downstream, because
downstream is vacuous.

`fooDecl` is deliberately the *smallest* declaration that still exercises the three parts
with content:

* `VIndField.WF.pos` on its `none` branch — a non-recursive field, so the block-freeness is
  the definitional one;
* `VIndField.WF.level` in the `Prop` case — `imax (.succ .zero) .zero ≤ .zero`, which holds
  only because `imax _ 0 = 0`, the clause `divergences.md` records as weaker than the
  kernel's;
* `VIndCtor.WF.result` in the **staged** environment — the constructor's result mentions
  `Foo`, which exists only after `addIndTypes`, so this is the clause that forces `WF.ctors`
  to be stated over `env₁` rather than `env`.

`Prop`-valued is not incidental: it is the case that `ParamsExtra.ctor_ty` asserted was
impossible (`D.lvl ≠ .zero`) before that clause was found false and replaced. -/

/-- `inductive Foo : Prop | mk : Prop → Foo` — one `Prop`-valued type, one constructor with
one non-recursive field. -/
def fooDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .zero
  types := [{ name := `Foo, type := .sort .zero, indices := [],
              ctors := [{ name := `Foo.mk, params := [],
                          fields := [{ type := .sort .zero, lvl := .succ .zero,
                                       recArg := none }],
                          args := [] }] }]
  isLE := false

/-- **The first `VInductDecl'.WF` witness in the tree.** -/
theorem fooDecl_WF : fooDecl.WF .empty where
  types_ne := by simp [fooDecl]
  params := trivial
  types := by
    intro T hT
    simp [fooDecl] at hT
    subst hT
    exact { indices := trivial
            isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
            canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp [fooDecl] at hT
      subst hT
      simp at hC
      subst hC
      have hc : env₁.constants `Foo = some ⟨0, VExpr.sort .zero⟩ := by
        simp [VEnv.addIndTypes, VEnv.addConstList, VInductDecl'.typeConsts, fooDecl,
          VEnv.addConst, VEnv.empty] at he
        subst he; simp
      refine { params_len := rfl, params_eq := .zero, fields := ?_,
               args_len := rfl, args_fresh := by simp, args_ty := .nil,
               result := .constDF hc nofun nofun rfl .nil }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp at hF
        subst hF
        exact { hasType := .sortDF trivial trivial (.refl _)
                level := fun ls => by simp [VLevel.eval, fooDecl, Lean.Nat.imax]
                -- `fooDecl`'s only field is non-recursive, so this clause is vacuous here.
                -- The section below checks it on families that do have recursive fields.
                binders_indep := nofun
                pos := ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        _, .sortDF trivial trivial (.refl _)⟩ }
  isLE := by simp [fooDecl]

/-! ## `VIndField.WF.binders_indep` is satisfiable, and it bites

`binders_indep` (`Theory/Inductive/Decl.lean`) restricts a recursive field's `ξ` to be
independent of *earlier recursive* fields, because the set model's `Pos q a` must evaluate
`⟦ξ⟧` without the recursive filler `f` that `Pos q a` itself types.

A clause nothing satisfies is the configuration that produced every vacuity finding on this
project, and `fooDecl_WF` discharges it by `nofun` — its only field is non-recursive, so that
witness proves nothing about the clause.  This section is the real check.  `BindersIndep` is
**pure syntax** (no `VEnv` occurs in it), so each check is a closed computation.

Three checks, in increasing strength: the motivating family, a non-vacuous instance, and a
refutation showing the clause is not trivially true.

These check `BindersIndep` *in isolation*, which is not the same as showing that a full
`VIndCtor.WF` containing it is inhabited.  `accDecl_WF` and `mutDecl_WF` at the end of this
file are that: complete `VInductDecl'.WF` witnesses whose constructors have recursive fields,
so `binders_indep` is discharged there as one clause among the others rather than alone. -/

/-- **`Acc` satisfies it** — the family that motivated the clause, since it is a
large-eliminating subsingleton whose eliminator `Ind_subsingleton` must reach.

It satisfies it *vacuously*: `Acc.intro`'s recursive field is field 1, and the only earlier
field is `x : α`, which is **not** recursive.  That is exactly the point — `ξ = [α, r y x]`
does mention `x`, and a clause that forbade dependence on *all* earlier fields would reject
`Acc`. -/
theorem accIntroRec_BindersIndep : accIntroRec.BindersIndep (accIntro.fields.take 1) 1 := by
  intro i' t F' hF' hrec heq
  match i', heq with
  | 0, heq => simp [accIntro] at hF'; subst hF'; exact absurd hrec (by simp)

/-- **`Forest'.cons` satisfies it** — `mutDecl`'s `cons : Tree' → Forest' → Forest'` is the
only constructor in this file with *two* recursive fields, so it is the closest real case to
what the clause constrains.  Its second recursive field has `ξ = []`, so the `Skips`
obligation is reached with nothing to check.

Every constructor of `natDecl`, `mutDecl`, `accDecl`, `eqDecl`, `iffDecl`, `nonemptyDecl`,
`lvlDecl` and `fooDecl` was enumerated: none has a recursive field that both follows another
recursive field *and* carries a binder, so the clause rejects nothing in this tree.

Stated over *all* of `forestCons`'s fields rather than just the second, because
`mutDecl_WF` below consumes it as `VIndCtor.WF`'s `fields` clause needs it. -/
theorem forestCons_BindersIndep : ∀ i (F : VIndField), forestCons.fields[i]? = some F →
    ∀ r, F.recArg = some r → r.BindersIndep (forestCons.fields.take i) i := by
  intro i F hF r hr i' t F' hF' _ heq k B hB
  match i, hF with
  | 0, hF => cases hF; cases hr; omega
  | 1, hF =>
    cases hF; cases hr
    exact absurd hB nofun

/-! ### The deepest rung: two recursive fields where the later one **carries a binder**

`accDecl_WF` and `mutDecl_WF` at the end of this file both *reach* `binders_indep`'s
hypothesis, but discharge the `Skips` obligation trivially: `Acc.intro` has no earlier
*recursive* field, and `Forest'.cons`'s later recursive field has `ξ = []`.  A clause has as
many vacuity levels as it has nested conditions, and the deepest one — **there is a binder,
and it must actually skip the earlier recursive field's variable** — was still untested.

`W'` is the smallest declaration that reaches it:

```
inductive W' (β : Prop) : Prop
  | mk : W' β → (β → W' β) → W' β
```

Field 0 is recursive.  Field 1 is recursive with `ξ = [β]`, and in field 1's context
`[W' β, β]` the parameter `β` is `.bvar 1` while field 0 is `.bvar 0` — so
`(.bvar 1).Skips 1 0` is a real computation that could have come out either way.  `wRecBad`
is the same shape with `ξ = [.bvar 0]`, and it is refuted.

Worth building against the *current* spec rather than later: this is the configuration the
nested/companion design produces for real, because a companion's substituted constructors turn
several of `J`'s fields recursive at once.  If the clause were wrong here, learning it from
five lines is much cheaper than learning it from the nested port. -/

inductive W' (β : Prop) : Prop
  | mk : W' β → (β → W' β) → W' β

def wRec0 : VIndRecArg where binders := []; idx := 0; args := []

/-- `ξ = [β]`: the binder is the *parameter*, which sits one de Bruijn index past field 0. -/
def wRec1 : VIndRecArg where binders := [.bvar 1]; idx := 0; args := []

def wMk : VIndCtor where
  name := ``W'.mk
  params := [.sort .zero]
  fields :=
    [{ type := (VExpr.const ``W' []).mkApp [.bvar 0], lvl := .zero, recArg := some wRec0 },
     { type := mkPi wRec1.binders ((VExpr.const ``W' []).mkApp [.bvar 2]),
       lvl := .zero, recArg := some wRec1 }]
  args := []

def wType : VIndType where
  name := ``W'
  type := mkPi [.sort .zero] (.sort .zero)
  indices := []
  ctors := [wMk]

def wDecl : VInductDecl' where
  uvars := 0
  params := [.sort .zero]
  lvl := .zero
  isLE := false
  types := [wType]

-- Ground truth: the hand-written `VExpr`s are Lean's own encoding, not a convenient fiction.
example : wType.type = (vconst(type_of% @W')).type := rfl
example : wMk.type wDecl 0 = (vconst(type_of% @W'.mk)).type := rfl
example : (VEnv.empty.addInduct' wDecl).isSome := rfl
example : wMk.recFields = [(0, wRec0), (1, wRec1)] := rfl

/-- **The clause holds at the deepest rung.**  Both conditions bite: field 0 is recursive, and
`ξ` is non-empty, so the proof really evaluates `(.bvar 1).Skips 1 0`. -/
theorem wMk_BindersIndep : ∀ i (F : VIndField), wMk.fields[i]? = some F →
    ∀ r, F.recArg = some r → r.BindersIndep (wMk.fields.take i) i := by
  intro i F hF r hr i' t F' hF' hrec heq k B hB
  match i, hF with
  | 0, hF => cases hF; cases hr; omega
  | 1, hF =>
    cases hF; cases hr
    obtain ⟨rfl, rfl⟩ : i' = 0 ∧ t = 0 := by omega
    match k, hB with
    | 0, hB => cases hB; exact rfl

/-- **…and the clause bites.**  Replace `ξ = [β]` by `ξ = [x]`, where `x` is the *first*
(recursive) field's variable — the shape whose `⟦ξ⟧` the model cannot evaluate, because it
needs the value `Pos` is being asked to type.  `BindersIndep` refutes it.

Without this, `binders_indep` could be a clause every `VIndRecArg` satisfies, in which case it
would constrain nothing and the model would still be stuck. -/
def wRecBad : VIndRecArg where binders := [.bvar 0]; idx := 0; args := []

example : ¬ wRecBad.BindersIndep (wMk.fields.take 1) 1 := by
  intro h
  have := h 0 0 wMk.fields[0]! rfl (by simp [wMk]) rfl 0 (.bvar 0) rfl
  rw [VExpr.skips_iff] at this; simp [VExpr.Skips'] at this

/-- …and `addInduct'` accepts it. -/
theorem fooEnv_eq : ∃ e, VEnv.empty.addInduct' fooDecl = some e := ⟨_, rfl⟩

noncomputable def fooEnv : VEnv := fooEnv_eq.choose

/-- A witness for `VEnv.IsStructure`, hence for `VInductDecl'.ProjClosed`'s consumer. -/
theorem fooEnv_IsStructure :
    fooEnv.IsStructure `Foo fooDecl (fooDecl.types[0]!)
      ((fooDecl.types[0]!).ctors[0]!) where
  types := rfl
  name := rfl
  ctors := rfl
  noRec := rfl
  decl := ⟨.empty, fooEnv, fooDecl_WF, fooEnv_eq.choose_spec, VEnv.LE.rfl⟩

/-- A witness for `VInductDecl'.RecCtx` — the situation the whole recursor construction is
stated over, and the hypothesis of `onCtxMinors`, `recType_isType` and `iotaRules_WF`. -/
theorem fooRecCtx : ∃ env₃, fooDecl.RecCtx env₃ := by
  obtain ⟨e1, h1⟩ : ∃ e, VEnv.empty.addIndTypes fooDecl = some e := ⟨_, rfl⟩
  obtain ⟨e2, h2⟩ : ∃ e, e1.addIndCtors fooDecl = some e := by
    rw [← Option.isSome_iff_exists]; revert h1; rintro ⟨⟩; rfl
  have o1 := VInductDecl'.addIndTypes_ordered .empty fooDecl_WF h1
  have o2 := VInductDecl'.addIndCtors_ordered o1 fooDecl_WF h1 h2
  exact ⟨e2, fooDecl_WF.recCtx h1 h2 VEnv.LE.rfl o2⟩

/-! ### `D.lvl` is in none of the stored types

`SExpr.ParamsExtra.ctor_ty` asks for `classify T.name = some (.indTy _ rel)` with
`rel = true ↔ D.lvl ≠ .zero`, so `rel` has to be a function of the *name*.  Four times now an
F1 obstruction has been dissolved by reading the fact off a **different** stored constant —
arities off `env.constants`, the `.indTy` arity off the recursor's type, which is
syntactically informative where `T.type` is not.  That move has no target here.

`fooDecl'` differs from `fooDecl` only in `lvl`, and all three stored types — the block type's,
the constructor's, and the recursor's — are *identical* on the nose.  So no constant carries
the block's result universe: `D.lvl` reaches the environment only through `VIndType.WF.canon`
and `VIndCtor.WF.result`, both of which are typing judgements, not syntax. -/

def fooDecl' : VInductDecl' := { fooDecl with lvl := .succ .zero }

example : fooDecl.lvl = VLevel.zero := rfl
example : fooDecl'.lvl = VLevel.succ .zero := rfl

-- the block type's stored type
example : (fooDecl'.types.getD 0 default).type = (fooDecl.types.getD 0 default).type := rfl
-- the constructor's stored type
example : ((fooDecl'.types.getD 0 default).ctors.getD 0 default).type fooDecl' 0
        = ((fooDecl.types.getD 0 default).ctors.getD 0 default).type fooDecl 0 := rfl
-- the recursor's stored type, and its universe count
example : fooDecl'.recType 0 = fooDecl.recType 0 := rfl
example : fooDecl'.recUvars = fooDecl.recUvars := rfl
-- …and the ι-rule, for completeness: nothing `addInduct'` stores sees `lvl`
example : fooDecl'.iotaRules = fooDecl.iotaRules := rfl

/-! ### K1's skeleton, against Lean's own constructor types

`VIndCtor.skeleton_type` says the splitter inverts `VIndCtor.type`.  That is a statement about
the *record*; what the translation will actually be handed is the constant Lean stores.  These
check the splitter against `vconst(type_of% …)` — the same ground truth the recursor
comparisons above use — so a mismatch between the record and the kernel shows up here rather
than being assumed away.

Covered: no fields (`Eq.refl`), no parameters and a recursive field (`Nat.succ`), parameters
*and* an index with a higher-order recursive field (`Acc.intro`), and fields whose types are
themselves `forallE` (`Iff.intro` — the case a *maximal* pi-peel would walk past). -/

example : VIndCtor.skeleton eqDecl.np eqRefl.fields.length (vconst(type_of% @Eq.refl)).type
    = (eqRefl.params, eqRefl.fields.map (·.type), eqRefl.args) := rfl

example : VIndCtor.skeleton natDecl.np natZero.fields.length (vconst(type_of% @Nat.zero)).type
    = (natZero.params, natZero.fields.map (·.type), natZero.args) := rfl

example : VIndCtor.skeleton natDecl.np natSucc.fields.length (vconst(type_of% @Nat.succ)).type
    = (natSucc.params, natSucc.fields.map (·.type), natSucc.args) := rfl

example : VIndCtor.skeleton accDecl.np accIntro.fields.length
      (vconst(type_of% @Acc.intro)).type
    = (accIntro.params, accIntro.fields.map (·.type), accIntro.args) := rfl

example : VIndCtor.skeleton iffDecl.np iffIntro.fields.length
      (vconst(type_of% @Iff.intro)).type
    = (iffIntro.params, iffIntro.fields.map (·.type), iffIntro.args) := rfl

example : VIndCtor.skeleton nonemptyDecl.np nonemptyIntro.fields.length
      (vconst(type_of% @Nonempty.intro)).type
    = (nonemptyIntro.params, nonemptyIntro.fields.map (·.type), nonemptyIntro.args) := rfl

/-! #### The mutant

Two validation suites in this tree were blind to a universe-parameter shift inside a field
type, so the splitter is checked against one before it is trusted.  `lvlMkMutant` differs from
`lvlMk` only in that its field types read `.param 1` where the real ones read `.param 0`.

The test is stated *positively*: each side pins the level index the splitter actually returns.
A pass that normalised, erased or defaulted universe parameters would make one of the two
`rfl`s fail, rather than making an inequality silently true. -/

def lvlMkMutant : VIndCtor :=
  { lvlMk with fields := lvlMk.fields.map fun F =>
      { F with type := F.type.instL [.param 1] } }

example : (VIndCtor.skeleton lvlDecl.np lvlMk.fields.length
      (lvlMk.type lvlDecl 0)).2.1.head? = some (VExpr.sort (.param 0)) := rfl

example : (VIndCtor.skeleton lvlDecl.np lvlMkMutant.fields.length
      (lvlMkMutant.type lvlDecl 0)).2.1.head? = some (VExpr.sort (.param 1)) := rfl

-- and the splitter still round-trips on the mutant: it is faithful, not merely sensitive
example : VIndCtor.skeleton lvlDecl.np lvlMkMutant.fields.length (lvlMkMutant.type lvlDecl 0)
    = (lvlMkMutant.params, lvlMkMutant.fields.map (·.type), lvlMkMutant.args) := rfl

/-! ### R11's probe: `iotaLam` against Lean's *stored* recursor rules

Everything above validates the spec against Lean's recursor **types** and against hand-written
`vexpr(…)` transcriptions of its rules.  Nothing yet compares the spec's ι-rule right-hand side
against the reduction rule Lean actually stores — which is the thing `addDecl.WF`'s inductive
branch has to reproduce, and the thing that decides whether that branch is transcription or a
spec change.

`vrecrule(r, i)` pulls `RecursorVal.rules[i].rhs` out of the environment and translates it, so
this is ground truth of the same kind as `vconst(type_of% …)` — not a restatement of the spec.

Reading `Lean4Lean/Inductive/Add.lean`'s `mkRecRules` first: it builds
`λ params motives minors fields. minor_q fields v`, with each `v` being
`λ ξ. I_{idx}.rec params motives minors π (field_i ξ)`.  `VInductDecl'.iotaLam` and
`ihValues` are written the same way, argument order included — so the expectation is equality
on the nose, and these checks are what turn that expectation into a fact.

**Result: equality on the nose, with no universe renaming at all.**  Two things follow.

*R11 is transcription, not a spec change.*  All six pass — including `Acc`, whose recursive
field is higher-order, and both `Prop`-valued blocks of `stdPrelude`.  Whatever
`addDecl.WF`'s inductive branch has to prove about the ι-rules' right-hand sides, it is not
fighting a mismatch.

*The `swap01` convention does not apply here, and the section header above should be read with
that in mind.*  `swap01` compensates for `vconst(type_of% X)` numbering universes **by order of
first appearance in `X`'s elaborated type**.  `vrecrule` reads `rv.levelParams`, the
declaration's *own* level-parameter order, and that already puts the elimination universe
first — exactly `VInductDecl'.selfLvls`' convention.  So against the stored declaration there
is nothing to bridge.  This was found the useful way round: the three checks that need a
renaming against `vconst` were written with `swap01` and **failed**, which is also what shows
`vrecrule` returns real, distinguishing terms rather than something every `rfl` accepts. -/

open Lean Elab Term in
/-- The `rhs` of recursor `r`'s `i`-th reduction rule, as **Lean stores it**, as a `VExpr`. -/
elab "vrecrule(" r:ident ", " i:num ")" : term => do
  let n ← realizeGlobalConstNoOverload r
  let .recInfo rv ← getConstInfo n | throwError "{n} is not a recursor"
  let some rule := rv.rules[i.getNat]? | throwError "{n} has no rule #{i.getNat}"
  let e ← Lean4Lean.Meta.expandExpr rule.rhs
  return toExpr (← Lean4Lean.Meta.ofExpr rv.levelParams {} e)

-- `Eq`: one universe parameter, so the elimination universe has to be swapped into place
example : eqDecl.iotaLam 0 eqRefl = vrecrule(Eq.rec, 0) := rfl

-- `Nat`: no universe parameters of its own, so no renaming; two constructors, two rules
example : natDecl.iotaLam 0 natZero = vrecrule(Nat.rec, 0) := rfl
example : natDecl.iotaLam 1 natSucc = vrecrule(Nat.rec, 1) := rfl

-- `Acc`: parameters *and* an index, and a higher-order recursive field, so this is the one
-- that exercises `ihValues`' `ξ`-telescope against Lean's own
example : accDecl.iotaLam 0 accIntro = vrecrule(Acc.rec, 0) := rfl

-- and the two `Prop`-valued blocks of `stdPrelude`
example : iffDecl.iotaLam 0 iffIntro = vrecrule(Iff.rec, 0) := rfl
example : nonemptyDecl.iotaLam 0 nonemptyIntro = vrecrule(Nonempty.rec, 0) := rfl

/-! ## `Acc` — a full `VInductDecl'.WF` witness *with a recursive field*

`fooDecl_WF` above is the tree's first `VInductDecl'.WF` witness, but `fooDecl`'s single field
is non-recursive, so it discharges `VIndField.WF.binders_indep` *and* the entire `some r`
branch of `VIndField.WF.pos` by `nofun`.  That left the configuration that actually matters —
a constructor with a recursive field — with no witness at all.

That is the shape every vacuity finding on this project has had: impeccable machinery above an
instance that does not exist.  It matters more since `binders_indep` landed, because
strengthening `VIndField.WF` makes everything *above* it (`addInduct_WF`) easier and everything
*below* it harder to satisfy.

`accDecl` is the right target.  `Acc` is the family that motivated `binders_indep`; it is a
large-eliminating subsingleton, so `isLE := true` and `LECond`'s **second** disjunct are
exercised rather than the cheap `IsNeverZero` one; its recursive field carries a two-binder `ξ`
and a nontrivial `π`; and its eliminator is what the set model's subsingleton argument needs.

**Built at the staged environment.**  `WF.ctors` quantifies over `env₁` with
`env.addIndTypes D = some env₁`, and that is the only environment the clause is ever evaluated
at.  `Acc.intro`'s recursive field *and* its result both mention the constant `Acc`, so at
`VEnv.empty` this clause is unsatisfiable — which is precisely the defect
`no_trIndCtor_at_base` (`Verify/Environment/Induct.lean`) records for the refinement's
analogous relation, found by attempting a witness rather than by inspection. -/

/-- The staged environment really does carry `Acc` at its stored type.  Everything in
`accIntro_WF` that mentions the constant goes through this. -/
theorem acc_const_staged {env₁ : VEnv} (h : VEnv.empty.addIndTypes accDecl = some env₁) :
    env₁.constants ``Acc = some ⟨1, accType.type⟩ :=
  VEnv.addConstList_constants h (``Acc, ⟨1, accType.type⟩) (by exact List.Mem.head _)

/-- `α : Sort u, r : α → α → Prop` is a well-formed telescope — **at any environment**, since
it mentions no constant.  Stated that way because `WF.params` needs it at `VEnv.empty` and
`VIndField.WF.pos`'s `OnCtx` clause needs the same telescope at the *staged* environment. -/
theorem accDecl_params_WF {env : VEnv} :
    OnCtx accDecl.params.reverse (env.IsType accDecl.uvars) :=
  ⟨⟨trivial, _, .sort (by decide)⟩, _, by type_tac⟩

/-- `Acc` eliminates large by `LECond`'s **second** disjunct: one type, one constructor, and
each field is either `Prop`-valued (the recursive one) or appears among the result's index
arguments (`x`, which is `Acc`'s single index).  The cheap `IsNeverZero` disjunct is not
available — `accDecl.lvl` is `.zero`. -/
theorem accDecl_LECond : accDecl.LECond := by
  refine .inr ⟨accType, rfl, .inr ⟨accIntro, rfl, ?_⟩⟩
  rintro (_|_|i) F hF
  · -- field 0 is `x : α`, and `x` *is* the result's index argument
    exact .inr (by simp [accIntro])
  · -- field 1 is the recursive one, and it is `Prop`-valued
    exact .inl (by simp [accIntro] at hF; subst hF; rfl)
  · simp [accIntro] at hF

/-- The type side.  `canon` is reflexivity here — `accType.type = accType.canonType accDecl`
on the nose (checked by the `rfl` example above), so F1's definitional slack is unused by
this block; `lvlDecl` is where it bites. -/
theorem accType_WF : VIndType.WF .empty accDecl accType where
  indices := ⟨accDecl_params_WF, _, by type_tac⟩
  isType := ⟨_, by type_tac⟩
  canon := ⟨_, by type_tac⟩

theorem accIntro_WF {env₁ : VEnv} (h : VEnv.empty.addIndTypes accDecl = some env₁) :
    VIndCtor.WF env₁ accDecl 0 accType accIntro := by
  have hc := acc_const_staged h
  refine { params_len := rfl, params_eq := ?_, fields := ?_,
           args_len := rfl, args_fresh := ?_, args_ty := ?_, result := ?_ }
  · -- `accIntro.params` is `accDecl.params` on the nose, so F3's slack is unused here
    exact .succ (.succ .zero (by type_tac)) (by type_tac)
  · intro i F hF
    match i, hF with
    | 0, hF =>
      simp [accIntro] at hF
      subst hF
      exact { hasType := by type_tac
              level := fun ls => by simp [VLevel.eval, accDecl, Lean.Nat.imax]
              binders_indep := nofun
              pos := ⟨.bvar 1, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                      _, by type_tac⟩ }
    | 1, hF =>
      simp [accIntro] at hF
      subst hF
      -- The field's stored type, typed at the sort the pi rule actually delivers.
      --
      -- Two reasons this is a `have` with the pi spelled out rather than one `type_tac`.
      -- (i) Inside the structure instance the goal carries the unreduced projection
      -- `{…}.type`, which `type_tac`'s `refine` will not see a `forallE` through.
      -- (ii) `type_tac`'s `forallE` branch is `refine HasType.forallE (u := ?_) (v := ?_) ?_ ?_`
      -- followed by a **four**-slot `<;> [skip; skip; type_tac; type_tac]`.  That is right only
      -- while the target sort is a metavariable (as under `IsType`, where every other use in
      -- this file sits): here the sort is *concrete*, so unification solves `u` and `v`, only
      -- two goals remain, and the four-slot combinator fails.  Applying `.forallE` directly
      -- sidesteps it.
      have hpi : env₁.HasType accDecl.uvars
          ((List.map (fun x => x.type) (List.take 1 accIntro.fields)).reverse
            ++ accDecl.params.reverse)
          (.forallE (.bvar 2)
            (.forallE (((VExpr.bvar 2).app (.bvar 0)).app (.bvar 1))
              ((((VExpr.const `Acc [VLevel.param 0]).app (.bvar 4)).app (.bvar 3)).app (.bvar 1))))
          (.sort (.imax (.param 0) (.imax .zero .zero))) :=
        .forallE (by type_tac) (.forallE (by type_tac) (by type_tac))
      -- Goals come out in *declaration* order: hasType, level, pos, binders_indep.
      refine { hasType := ?_, level := ?_, binders_indep := ?_, pos := ?_ }
      · -- `∀ (y : α), r y x → Acc r y` is `Prop`-valued, but the pi rule delivers the sort
        -- `imax u (imax 0 0)`, which is only *equivalent* to `0`.  One `defeqDF` closes it —
        -- the same slack `VIndField.WF.level` is stated against.
        exact VEnv.IsDefEq.defeq (u := .succ (.imax (.param 0) (.imax .zero .zero)))
          (.sortDF (by decide) (by decide)
            (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax])) hpi
      · exact fun ls => by simp [VLevel.eval, accDecl, Lean.Nat.imax]
      · refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [accIntroRec, VInductDecl'.NoBlock, VExpr.NoConsts]
        · simp [accIntroRec, VInductDecl'.NoBlock, VExpr.NoConsts]
        · -- `ξ.reverse ++ Γ` is `[r y x, y, x, r, α]`
          exact ⟨⟨⟨accDecl_params_WF, _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩
        · -- `Acc α r y` really is a `Prop` — no `imax` slack here
          exact by type_tac
        · exact fun T' hT' => by cases hT'; exact .cons (by type_tac) .nil
        · -- `F.type` *is* `canonType` on the nose, so this is `IsType`, not a real conversion
          exact ⟨_, hpi⟩
      · exact fun r hr => by cases hr; exact accIntroRec_BindersIndep
  · intro a ha
    simp [accIntro] at ha
    subst ha
    simp [VInductDecl'.NoBlock, VExpr.NoConsts]
  · exact .cons (by type_tac) .nil
  · exact by type_tac

theorem accDecl_WF : accDecl.WF .empty where
  types_ne := by simp [accDecl]
  params := accDecl_params_WF
  types := by
    intro T hT
    simp [accDecl] at hT
    subst hT
    exact accType_WF
  ctors := by
    intro env₁ he j T hT C hC
    match j, hT with
    | 0, hT =>
      simp [accDecl] at hT
      subst hT
      simp [accType] at hC
      subst hC
      exact accIntro_WF he
  isLE := fun _ => accDecl_LECond

/-! ### …and `mutDecl`, the two-type case

`accDecl_WF` covers a recursive field.  `mutDecl_WF` covers the two configurations it does
*not*: a block with **more than one type** — so `addIndTypes` stages two constants and
`WF.ctors` genuinely ranges over `j` — and a constructor with **two recursive fields**, which
is the shape `binders_indep` was added for and the one the nested/companion design will make
routine (a companion's substituted constructors turn several of `J`'s fields recursive at
once).

`Forest'.cons`'s second recursive field has an earlier *recursive* field, so `binders_indep`
is reached here with its hypothesis satisfied rather than skipped. -/

theorem tree_const_staged {env₁ : VEnv} (h : VEnv.empty.addIndTypes mutDecl = some env₁) :
    env₁.constants ``Tree' = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants h (``Tree', ⟨0, .sort (.succ .zero)⟩) (by exact List.Mem.head _)

theorem forest_const_staged {env₁ : VEnv} (h : VEnv.empty.addIndTypes mutDecl = some env₁) :
    env₁.constants ``Forest' = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants h (``Forest', ⟨0, .sort (.succ .zero)⟩)
    (by exact List.Mem.tail _ (List.Mem.head _))

theorem mutDecl_WF : mutDecl.WF .empty where
  types_ne := by simp [mutDecl]
  params := trivial
  types := by
    intro T hT
    simp [mutDecl] at hT
    rcases hT with rfl | rfl <;>
      exact { indices := trivial, isType := ⟨_, .sort (by decide)⟩,
              canon := ⟨_, VEnv.HasType.sort (by decide)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    have ht := tree_const_staged he
    have hf := forest_const_staged he
    match j, hT with
    | 0, hT =>
      simp [mutDecl] at hT
      subst hT
      simp at hC
      subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_,
               args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp [treeNode] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, mutDecl, Lean.Nat.imax]
                -- no earlier field at all, so vacuous
                binders_indep := by rintro r ⟨⟩ i' t F' hF'; simp at hF'
                pos := ⟨by decide, rfl, nofun, nofun, trivial, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
    | 1, hT =>
      simp [mutDecl] at hT
      subst hT
      simp at hC
      rcases hC with rfl | rfl
      · -- `Forest'.nil`: no fields
        exact { params_len := rfl, params_eq := .zero, fields := nofun,
                args_len := rfl, args_fresh := nofun, args_ty := .nil, result := by type_tac }
      · refine { params_len := rfl, params_eq := .zero, fields := ?_,
                 args_len := rfl, args_fresh := nofun, args_ty := .nil,
                 result := by type_tac }
        intro i F hF
        match i, hF with
        | 0, hF =>
          simp [forestCons] at hF
          subst hF
          exact { hasType := by type_tac
                  level := fun ls => by simp [VLevel.eval, mutDecl, Lean.Nat.imax]
                  binders_indep := forestCons_BindersIndep 0 _ rfl
                  pos := ⟨by decide, rfl, nofun, nofun, trivial, by type_tac,
                          fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
        | 1, hF =>
          simp [forestCons] at hF
          subst hF
          exact { hasType := by type_tac
                  level := fun ls => by simp [VLevel.eval, mutDecl, Lean.Nat.imax]
                  -- **the non-vacuous case**: field 0 is recursive, so the clause's
                  -- hypothesis holds and `ξ = []` is what discharges it
                  binders_indep := forestCons_BindersIndep 1 _ rfl
                  pos := ⟨by decide, rfl, nofun, nofun, ⟨trivial, _, by type_tac⟩, by type_tac,
                          fun T' hT' => by cases hT'; exact .nil, _, by type_tac⟩ }
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, mutDecl])

/-! ### …and `wDecl`, the deepest rung

`accDecl_WF` reaches `binders_indep` with no earlier *recursive* field; `mutDecl_WF` reaches it
with an earlier recursive field but `ξ = []`.  `wDecl_WF` reaches it with **both** conditions
live, so the `Skips` obligation is a real computation on a real binder.

Reporting the deepest level reached, per witness:

| witness | earlier field recursive? | `ξ` non-empty? | `Skips` evaluated? |
|---|---|---|---|
| `fooDecl_WF` | — (no recursive field at all) | — | no |
| `accDecl_WF` | no | yes | no |
| `mutDecl_WF` | **yes** | no | no |
| `wDecl_WF` | **yes** | **yes** | **yes** |

That is the whole clause, and `wRecBad` above shows the last column could have come out the
other way. -/

theorem w_const_staged {env₁ : VEnv} (h : VEnv.empty.addIndTypes wDecl = some env₁) :
    env₁.constants ``W' = some ⟨0, wType.type⟩ :=
  VEnv.addConstList_constants h (``W', ⟨0, wType.type⟩) (by exact List.Mem.head _)

theorem wDecl_WF : wDecl.WF .empty where
  types_ne := by simp [wDecl]
  params := ⟨trivial, _, .sort (by decide)⟩
  types := by
    intro T hT
    simp [wDecl] at hT
    subst hT
    exact { indices := ⟨trivial, _, .sort (by decide)⟩
            isType := ⟨_, by type_tac⟩
            canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    have hw := w_const_staged he
    match j, hT with
    | 0, hT =>
      simp [wDecl] at hT
      subst hT
      simp [wType] at hC
      subst hC
      refine { params_len := rfl, params_eq := .succ .zero (by type_tac), fields := ?_,
               args_len := rfl, args_fresh := nofun, args_ty := .nil,
               result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp [wMk] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, wDecl, Lean.Nat.imax]
                binders_indep := wMk_BindersIndep 0 _ rfl
                pos := ⟨by decide, rfl, nofun, nofun, ⟨trivial, _, .sort (by decide)⟩,
                        by type_tac, fun T' hT' => by cases hT'; exact .nil,
                        _, by type_tac⟩ }
      | 1, hF =>
        simp [wMk] at hF
        subst hF
        -- `β → W' β` is `Prop`-valued, but the pi rule delivers `imax 0 0`; and the pi has to
        -- be built by `.forallE` rather than `type_tac`, whose four-slot `forallE` branch is
        -- only correct while the target sort is a metavariable (see `docs/soundness-ledger.md`).
        have hpi : env₁.HasType wDecl.uvars
            ((List.map (fun x => x.type) (List.take 1 wMk.fields)).reverse
              ++ wDecl.params.reverse)
            (.forallE (.bvar 1) ((VExpr.const ``W' []).mkApp [.bvar 2]))
            (.sort (.imax .zero .zero)) :=
          .forallE (by type_tac) (by type_tac)
        exact { hasType := VEnv.IsDefEq.defeq (u := .succ (.imax .zero .zero))
                  (.sortDF (by decide) (by decide)
                    (by simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax])) hpi
                level := fun ls => by simp [VLevel.eval, wDecl, Lean.Nat.imax]
                -- **the deepest rung**: field 0 is recursive *and* `ξ = [β]` is non-empty, so
                -- this really evaluates `(.bvar 1).Skips 1 0`
                binders_indep := wMk_BindersIndep 1 _ rfl
                pos := ⟨by decide, rfl,
                        by simp [wRec1, VInductDecl'.NoBlock, VExpr.NoConsts], nofun,
                        ⟨⟨⟨trivial, _, .sort (by decide)⟩, _, by type_tac⟩, _, by type_tac⟩,
                        by type_tac, fun T' hT' => by cases hT'; exact .nil,
                        _, hpi⟩ }
  isLE := by simp [wDecl]

end InductiveDeclExamples
end Lean4Lean
