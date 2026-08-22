import Lean4Lean.Theory.Inductive.Lemmas
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

end InductiveDeclExamples
end Lean4Lean
