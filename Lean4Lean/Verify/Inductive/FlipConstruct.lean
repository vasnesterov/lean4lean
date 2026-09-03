/-
# `FlipConstruct`: `AddInduct`'s constructor, and its payload at a **parameterised** nested block

`AddInduct` (`Verify/Environment/Basic.lean:149`) is an inductive with **no constructors**.  It is
therefore uninhabited, `TrEnv'.induct` (`:628`) can never fire, and every environment holding an
inductive is outside `TrEnv`.  "The flip" is giving it a constructor.

This file does two things and claims nothing else.

1. It writes the constructor's payload down as a *definition this file owns* (`AddInductN`, §5),
   so that "what the constructor needs" is a checkable proposition rather than a paragraph.
2. It **constructs that payload** at `ntreeAux` — `NTree α` with a `List (NTree α)` field,
   `uvars = 1`, `params = [Type u]`, the block Lean's own kernel runs the nested elimination on
   (`Theory/Inductive/NestedHead.lean:589`).  Deliberately **not** `nfnAux`: that block has
   `uvars = 0` and `params = []`, which makes the universe-ordering question of §3 *invisible* and
   the parameter-context hypotheses `trivial`.  `Verify/Environment/InductR.lean` §6 already has
   the `nfnAux` construction (`NestedWit.addInductStagesR_wit`); this file is the `np = 1`,
   `uvars = 1` counterpart, and §3 is a finding that only exists above `uvars = 0`.

**What is NOT claimed.**  Not that the flip can be *made*: making it edits `Basic.lean`,
`Theory/Typing/Env.lean` and three more files this stream does not own, and §7 records exactly
which edits and which of them is still blocked.  Not that `VEnv.WF.ordered` survives the flip in
general — §7.2 is precise about that being the live residual and about its shape.  Nothing here
is a `sorry`, and nothing here uses `VEnv.HasArgs.of_mkApp`.
-/
import Lean4Lean.Verify.Environment.InductR
import Lean4Lean.Theory.Inductive.NestedTele

namespace Lean4Lean

open Lean (Name)

namespace InductiveDeclExamples

/-! ## 1. The three constant lists the fold runs over, at `ntreeAux`

Read them: **one** type constant (the companion `_nested.List_1` is not declared), **one**
constructor constant (the companion's `nil`/`cons` are not declared either), and **two**
recursors, the second of which is the *renamed auxiliary* one, `NTree.rec_1`.  Every equation is
`rfl`. -/

theorem ntree_typeConstsC_eq : ntreeAux.typeConstsC ntreeK
    = [(``NTree, ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)] := rfl

theorem ntree_ctorConstsCR_eq : ntreeAux.ctorConstsCR ntreeRestore ntreeK
    = [(``NTree.node, ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩)] := rfl

theorem ntree_recConstsR_eq' : ntreeAux.recConstsR ntreeRestore ntreeK
    = [(``NTree.rec, ⟨2, ntreeAux.recTypeR ntreeRestore 0⟩),
       (``NTree.rec_1, ⟨2, ntreeAux.recTypeR ntreeRestore 1⟩)] := rfl

/-! ## 2. The `ConstantInfo`s, with their types spliced from Lean's own environment

`exprOf%` (`Verify/Environment/InductR.lean` §6) splices the constant's **stored type, as Lean's
kernel holds it**, into the term.  So nothing below is a hand transcription that could drift from
the declaration `NestedHead.lean:589` makes. -/

def ntreeInd : Lean.InductiveVal where
  name := ``NTree; levelParams := [`u]; type := exprOf% NTree
  numParams := 1; numIndices := 0; all := [``NTree]; ctors := [``NTree.node]
  numNested := 1; isRec := true; isUnsafe := false; isReflexive := false

def ntreeNodeCI : Lean.ConstructorVal where
  name := ``NTree.node; levelParams := [`u]; type := exprOf% NTree.node
  induct := ``NTree; cidx := 0; numParams := 1; numFields := 2; isUnsafe := false

/-! ### 2a. The universe order is the one Lean stores, and it is **not** `swap01`

`NestedHead.lean`'s recursor checks are stated as `swap01 (ntreeAux.recTypeR ntreeRestore i)
= (vconst(type_of% @NTree.rec)).type`, and `swap01` is a real renaming here (`ntreeAux.uvars = 1`,
so the recursor has two universe parameters).  That could have been a wall: `TrConstant`
(`Verify/Environment/Basic.lean:19`) fixes the translation's level context to `ci.levelParams`,
so a mismatch between the abstract numbering and Lean's would be unrepairable without either
renumbering the spec or writing a `levelParams` list Lean does not use.

It is not a wall, and the reason is worth recording because `nfnAux` cannot see it.  The two
numberings that differ are

* `vconst(type_of% X)`, which numbers by **order of first appearance in `X`'s own type** — for
  `NTree.rec` that is `u` (the block's) then `u_1` (the elimination universe); and
* the specification, which puts the **elimination universe at index 0** (F10, see
  `Theory/Inductive/DeclExamples.lean`'s "Conventions").

`swap01` bridges *those*.  But Lean's actual `RecursorVal.levelParams` for `NTree.rec` is
`[u_1, u]` — elimination universe **first** — measured directly from the environment, so it agrees
with the specification and disagrees with `vconst`.  Hence `Us := ci.levelParams` is exactly the
right level context and §3's recursor bridges hold against the *un-swapped* `recTypeR`.

At `nfnAux` (`uvars = 0`) the recursor has one universe parameter and there is nothing to order,
which is precisely why `Verify/Environment/InductR.lean` §6's `tr_recType0` could be stated with
`Us := [`u]` and no such question arose. -/

def ntreeRecCI : Lean.RecursorVal where
  name := ``NTree.rec; levelParams := [`u_1, `u]; type := exprOf% NTree.rec
  all := [``NTree]; numParams := 1; numIndices := 0; numMotives := 2; numMinors := 3
  rules := []; k := false; isUnsafe := false

def ntreeRec1CI : Lean.RecursorVal where
  name := ``NTree.rec_1; levelParams := [`u_1, `u]; type := exprOf% NTree.rec_1
  all := [``NTree]; numParams := 1; numIndices := 0; numMotives := 2; numMinors := 3
  rules := []; k := false; isUnsafe := false

/-! ## 3. The four `TrExprS` bridges

Each says: the type **Lean's kernel stores** for the constant translates to the type the abstract
nested step declares.  Discharged by `trS_tac` — `TrExprS` by structure, with `type_tac` on the
side conditions — so each is a typing derivation over the staged environment, not a syntactic
comparison. -/

section
variable {env : VEnv}
  (hList : env.constants ``List = some ⟨1, listType.type⟩)
  (hNil : env.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩)
  (hCons : env.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩)
  (hNTree : env.constants ``NTree
    = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
  (hNode : env.constants ``NTree.node
    = some ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩)

/-- The block's own type constant: `Type u → Type u`, and no hypotheses at all. -/
theorem tr_ntreeType : TrExprS env [`u] []
    (exprOf% NTree) (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) := by
  trS_tac

include hList hNTree in
/-- Lean's stored type for `NTree.node` translates to the **restored** constructor type — the one
whose field was rewritten from `_nested.List_1 α` back to `List (NTree α)`. -/
theorem tr_ntreeNodeType : TrExprS env [`u] [] (exprOf% NTree.node)
    (ntreeNode.typeR ntreeAux ntreeRestore 0) := by
  show TrExprS env [`u] [] _ (vconst(type_of% @NTree.node)).type
  trS_tac

include hList hNil hCons hNTree hNode in
/-- **…and for `NTree.rec` to `recTypeR … 0`**, against the un-swapped abstract numbering (§2a). -/
theorem tr_ntreeRecType0 : TrExprS env [`u_1, `u] [] (exprOf% NTree.rec)
    (ntreeAux.recTypeR ntreeRestore 0) := by
  trS_tac

include hList hNil hCons hNTree hNode in
/-- **…and for the *renamed auxiliary* recursor `NTree.rec_1` to `recTypeR … 1`.**  This is the
constant that refutes `AddInductStages` (`Verify/Inductive/AddDeclWF.lean` §2): it is `mkRecName`
of no type the block declares. -/
theorem tr_ntreeRecType1 : TrExprS env [`u_1, `u] [] (exprOf% NTree.rec_1)
    (ntreeAux.recTypeR ntreeRestore 1) := by
  trS_tac

end

/-! ## 4. The two shape predicates

`IndShapeOf`/`CtorShapeOf` (`Verify/Environment/Basic.lean`) pin the elaboration bookkeeping the
structure-eta and projection checks read (`Verify/StructureBridge.lean` is why they exist).  Both
have two halves — an `∃` for non-vacuity and a `∀` for pinning — and the `∀` half is where a
nested block bites: `ctorsAll` has three entries and two of them belong to the companion, whose
restored names are `List.nil`/`List.cons`. -/

theorem indShapeOf_ntreeInd : IndShapeOf ntreeAux ntreeRestore.ctorName (.inductInfo ntreeInd) := by
  refine ⟨ntreeInd, rfl, ⟨_, List.mem_cons_self, rfl⟩, fun T hT hn => ?_⟩
  have hts : ntreeAux.types
      = [{ name := ``NTree, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
           indices := [], ctors := [ntreeNode] },
         { name := `_nested.List_1,
           type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
           indices := [], ctors := [nlistNil, nlistCons] }] := rfl
  rw [hts] at hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · exact ⟨ntreeInd, rfl, rfl, rfl, rfl, by decide, fun h => absurd h (by decide)⟩
  · exact absurd hn (by decide)

theorem ctorShapeOf_ntreeNodeCI :
    CtorShapeOf ntreeAux ntreeRestore.ctorName ntreeRestore.tyName (.ctorInfo ntreeNodeCI) := by
  have hcs : ntreeAux.ctorsAll = [(0, ntreeNode), (1, nlistNil), (1, nlistCons)] := rfl
  refine ⟨ntreeNodeCI, rfl, ⟨(0, ntreeNode), by rw [hcs]; exact List.mem_cons_self, by decide⟩,
    fun jC hjC hn => ?_⟩
  rw [hcs] at hjC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjC
  rcases hjC with rfl | rfl | rfl
  · exact ⟨ntreeNodeCI, rfl, by decide, by decide, rfl, rfl⟩
  · exact absurd hn (by decide)
  · exact absurd hn (by decide)

end InductiveDeclExamples

/-! ## 5. The constructor, written down

`AddInductN` is what the brief calls the constructor's *payload*: the proposition a flipped

    inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
        (m₂ : ConstMap) (env₂ : VEnv) : Prop where
      | nested {K R} : AddInductStagesR m₁ env₁ decl K R m₂ env₂ →
          VEnv.AddNestedStep env₁ decl K R env₂ → AddInduct m₁ env₁ decl m₂ env₂

would carry.  It is a definition in *this* file, so nothing frozen or foreign is touched, and
`AddInduct` stays empty.

**Why these two conjuncts and no others.**

* `AddInductStagesR` is the constant-map side, and it is the *definition of the output map*: it
  supplies `env₁.addInductR decl K R = some env₂` (`to_addInductR`) and all four Tier-1 arms
  (§6).  It is what `Basic.lean:118`'s own docstring proposes.
* `VEnv.AddNestedStep` is the abstract side, and it is **not** derivable from the fold: the fold
  is exact on the *names and types* the step declares, and says nothing about whether `R` is an
  honest restoration.  A lying `R` — one renaming a companion to a type it is not — passes the
  fold.  `AddNestedStep` = `∃ npJ, decl.WF env₁ ∧ R.OwnId decl K ∧ R.Faithful decl env₁ K npJ ∧
  env₁.addInductR decl K R = some env₂` is what `VDecl.WF.inductNested`
  (`Theory/Typing/Env.lean:72`, the rule that file's docstring already writes out) consumes, so
  carrying it here is what lets `TrEnv'.wf`'s `induct` arm close.

`decl.WF env₁` is already a *separate* hypothesis of `TrEnv'.induct`, so the overlap with
`AddNestedStep`'s first conjunct is deliberate redundancy, not a second obligation. -/
def AddInductN (m₁ : Lean.ConstMap) (env₁ : VEnv) (decl : VInductDecl')
    (m₂ : Lean.ConstMap) (env₂ : VEnv) : Prop :=
  ∃ K R, AddInductStagesR m₁ env₁ decl K R m₂ env₂ ∧
    VEnv.AddNestedStep env₁ decl K R env₂

/-! ## 6. The payload keeps every Tier-1 arm

`docs/handoff-addinduct.md`'s Tier 1 is the seven lemmas whose *proofs* case on the empty
relation.  Five of them are arms of the relation itself, and each is one line from
`AddInductStagesR`'s counterpart — i.e. the flip costs Tier 1 nothing.  The sixth,
`AddInduct.to_addInduct`, is the one that **cannot** survive; §7.1 is its refutation. -/

namespace AddInductN

variable {m₁ m₂ : Lean.ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}

theorem le (H : AddInductN m₁ env₁ D m₂ env₂) : env₁ ≤ env₂ := by
  obtain ⟨K, R, h, -⟩ := H; exact h.le

theorem map_wf (H : AddInductN m₁ env₁ D m₂ env₂) (hwf : m₁.WF) : m₂.WF := by
  obtain ⟨K, R, h, -⟩ := H; exact h.map_wf hwf

theorem find?_shape (H : AddInductN m₁ env₁ D m₂ env₂) (hwf : m₁.WF)
    {name ci} (hf : m₂.find? name = some ci) :
    m₁.find? name = some ci ∨
    (((∃ v, ci = .inductInfo v) ∨ (∃ v, ci = .ctorInfo v) ∨ (∃ v, ci = .recInfo v)) ∧
      ci.name = name ∧ ci.safety = .safe) := by
  obtain ⟨K, R, h, -⟩ := H; exact h.find?_shape hwf hf

/-- The only definitional equalities a nested step adds are its **restored** ι-rules, and the
map is unchanged outside the four names the step declares. -/
theorem defeqs_and_anti_lie (H : AddInductN m₁ env₁ D m₂ env₂) (hwf : m₁.WF) :
    ∃ K R, (∀ {df}, env₂.defeqs df → env₁.defeqs df ∨ df ∈ D.iotaRulesRS R K) ∧
      ∀ n ∉ D.allNamesCR R K, m₂.find? n = m₁.find? n := by
  obtain ⟨K, R, h, -⟩ := H
  exact ⟨K, R, fun hd => h.defeqs hd, fun _ hn => h.find?_of_not_mem hwf hn⟩

/-- The abstract-side step, which is what a flipped `VDecl.WF.inductNested` consumes. -/
theorem to_addNestedStep (H : AddInductN m₁ env₁ D m₂ env₂) :
    ∃ K R, VEnv.AddNestedStep env₁ D K R env₂ := by
  obtain ⟨K, R, -, h⟩ := H; exact ⟨K, R, h⟩

/-- …and the environment equation, in the only form a nested block has one. -/
theorem to_addInductR (H : AddInductN m₁ env₁ D m₂ env₂) :
    ∃ K R, env₁.addInductR D K R = some env₂ := by
  obtain ⟨K, R, h, -⟩ := H; exact ⟨K, R, h.to_addInductR⟩

end AddInductN


/-! ## 7. The payload, constructed at `ntreeAux`

`np = 1`, `uvars = 1`, `recUvars = 2`.  Nothing is hypothesised about the *declaration history*
beyond `List` having been declared, which is the history the block needs; nothing is
hypothesised about the constant map beyond freshness at the four names the step declares — in
particular the map is **not** assumed empty, which is what `Verify/Environment/InductR.lean`
§6's `nfnAux` counterpart assumes (`hfr : ∀ n, m.find? n = none`). -/

namespace InductiveDeclExamples

/-- `ntreeAux`'s **companion** member — the one `restoreNested` renames to `List` and the one no
step declares.  Named so that §7b can point at it. -/
def nlistMember : VIndType where
  name := `_nested.List_1
  type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
  indices := []
  ctors := [nlistNil, nlistCons]

theorem nlistMember_mem : nlistMember ∈ ntreeAux.types := List.Mem.tail _ List.mem_cons_self

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- **The constant-map side of the nested step, at a parameterised block.**  Four constants land
in the map — `NTree`, `NTree.node`, `NTree.rec` and the renamed auxiliary `NTree.rec_1` — and the
companion member `_nested.List_1` together with its two constructors land **nowhere**, on either
side. -/
theorem ntree_addInductStagesR {m : Lean.ConstMap} (hwf : m.WF)
    (hfr : ∀ n ∈ [``NTree, ``NTree.node, ``NTree.rec, ``NTree.rec_1], m.find? n = none) :
    ∃ m' env', AddInductStagesR m env₁ ntreeAux ntreeK ntreeRestore m' env' ∧
      m'.find? ``NTree.rec_1 = some (.recInfo ntreeRec1CI) ∧
      m'.find? ``NTree.rec = some (.recInfo ntreeRecCI) ∧
      m'.find? `_nested.List_1 = m.find? `_nested.List_1 ∧
      env₁.addInductR ntreeAux ntreeK ntreeRestore = some env' := by
  have fT := hfr ``NTree (by simp)
  have fN := hfr ``NTree.node (by simp)
  have fR := hfr ``NTree.rec (by simp)
  have fR1 := hfr ``NTree.rec_1 (by simp)
  -- the environment chain
  obtain ⟨e1, he1⟩ := VEnv.addConst_eq_none (env := env₁) (name := ``NTree)
    (ci := ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
    (ntree_fresh h _ (by simp))
  have c1 := VEnv.addConst_constants_eq he1
  have hL1 : e1.constants ``List = some ⟨1, listType.type⟩ := by rw [c1]; simp [list_const h]
  have hNi1 : e1.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩ := by
    rw [c1]; simp [listNil_const h]
  have hCo1 : e1.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩ := by
    rw [c1]; simp [listCons_const h]
  have hT1 : e1.constants ``NTree
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := by
    rw [c1]; simp
  obtain ⟨e2, he2⟩ := VEnv.addConst_eq_none (env := e1) (name := ``NTree.node)
    (ci := ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩)
    (by rw [c1]; simp [ntree_fresh h ``NTree.node (by simp)])
  have c2 := VEnv.addConst_constants_eq he2
  have hL2 : e2.constants ``List = some ⟨1, listType.type⟩ := by rw [c2]; simp [hL1]
  have hNi2 : e2.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩ := by
    rw [c2]; simp [hNi1]
  have hCo2 : e2.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩ := by
    rw [c2]; simp [hCo1]
  have hT2 : e2.constants ``NTree
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := by
    rw [c2]; simp [hT1]
  have hN2 : e2.constants ``NTree.node
      = some ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩ := by rw [c2]; simp
  obtain ⟨e3, he3⟩ := VEnv.addConst_eq_none (env := e2) (name := ``NTree.rec)
    (ci := ⟨2, ntreeAux.recTypeR ntreeRestore 0⟩)
    (by rw [c2, c1]; simp [ntree_fresh h ``NTree.rec (by simp)])
  have c3 := VEnv.addConst_constants_eq he3
  have hL3 : e3.constants ``List = some ⟨1, listType.type⟩ := by rw [c3]; simp [hL2]
  have hNi3 : e3.constants ``List.nil = some ⟨1, listNil.type listDecl 0⟩ := by
    rw [c3]; simp [hNi2]
  have hCo3 : e3.constants ``List.cons = some ⟨1, listCons.type listDecl 0⟩ := by
    rw [c3]; simp [hCo2]
  have hT3 : e3.constants ``NTree
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := by
    rw [c3]; simp [hT2]
  have hN3 : e3.constants ``NTree.node
      = some ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩ := by rw [c3]; simp [hN2]
  obtain ⟨e4, he4⟩ := VEnv.addConst_eq_none (env := e3) (name := ``NTree.rec_1)
    (ci := ⟨2, ntreeAux.recTypeR ntreeRestore 1⟩)
    (by rw [c3, c2, c1]; simp [ntree_fresh h ``NTree.rec_1 (by simp)])
  -- the map chain
  have w1 := hwf.insert ``NTree (.inductInfo ntreeInd) fT
  have f2 : (m.insert ``NTree (.inductInfo ntreeInd)).find? ``NTree.node = none := by
    rw [hwf.find?_insert]; simp [fN]
  have w2 := w1.insert ``NTree.node (.ctorInfo ntreeNodeCI) f2
  have f3 : ((m.insert ``NTree (.inductInfo ntreeInd)).insert ``NTree.node
      (.ctorInfo ntreeNodeCI)).find? ``NTree.rec = none := by
    rw [w1.find?_insert, hwf.find?_insert]; simp [fR]
  have w3 := w2.insert ``NTree.rec (.recInfo ntreeRecCI) f3
  have f4 : (((m.insert ``NTree (.inductInfo ntreeInd)).insert ``NTree.node
      (.ctorInfo ntreeNodeCI)).insert ``NTree.rec
      (.recInfo ntreeRecCI)).find? ``NTree.rec_1 = none := by
    rw [w2.find?_insert, w1.find?_insert, hwf.find?_insert]; simp [fR1]
  have w4 := w3.insert ``NTree.rec_1 (.recInfo ntreeRec1CI) f4
  have s1 : AddIndConsts (IndShapeOf ntreeAux ntreeRestore.ctorName)
      (ntreeAux.typeConstsC ntreeK) m env₁ (m.insert ``NTree (.inductInfo ntreeInd)) e1 :=
    .cons (ci := .inductInfo ntreeInd) rfl indShapeOf_ntreeInd
      ⟨by decide, rfl, tr_ntreeType⟩ fT he1 .nil
  have s2 : AddIndConsts (CtorShapeOf ntreeAux ntreeRestore.ctorName ntreeRestore.tyName)
      (ntreeAux.ctorConstsCR ntreeRestore ntreeK)
      (m.insert ``NTree (.inductInfo ntreeInd)) e1
      ((m.insert ``NTree (.inductInfo ntreeInd)).insert ``NTree.node
        (.ctorInfo ntreeNodeCI)) e2 :=
    .cons (ci := .ctorInfo ntreeNodeCI) rfl ctorShapeOf_ntreeNodeCI
      ⟨by decide, rfl, tr_ntreeNodeType hL1 hT1⟩ f2 he2 .nil
  have s3 : AddIndConsts (fun ci => ∃ v, ci = .recInfo v)
      (ntreeAux.recConstsR ntreeRestore ntreeK)
      ((m.insert ``NTree (.inductInfo ntreeInd)).insert ``NTree.node
        (.ctorInfo ntreeNodeCI)) e2
      ((((m.insert ``NTree (.inductInfo ntreeInd)).insert ``NTree.node
        (.ctorInfo ntreeNodeCI)).insert ``NTree.rec (.recInfo ntreeRecCI)).insert
        ``NTree.rec_1 (.recInfo ntreeRec1CI)) e4 :=
    .cons (ci := .recInfo ntreeRecCI) rfl ⟨_, rfl⟩
      ⟨by decide, rfl, tr_ntreeRecType0 hL2 hNi2 hCo2 hT2 hN2⟩ f3 he3 <|
    .cons (ci := .recInfo ntreeRec1CI) rfl ⟨_, rfl⟩
      ⟨by decide, rfl, tr_ntreeRecType1 hL3 hNi3 hCo3 hT3 hN3⟩ f4 he4 .nil
  have H : AddInductStagesR m env₁ ntreeAux ntreeK ntreeRestore _
      (e4.addIndRulesR ntreeAux ntreeK ntreeRestore) := ⟨_, _, _, _, e4, s1, s2, s3, rfl⟩
  refine ⟨_, _, H, ?_, ?_, ?_, H.to_addInductR⟩
  · rw [w3.find?_insert]; simp
  · rw [w3.find?_insert, w2.find?_insert]; simp
  · rw [w3.find?_insert, w2.find?_insert, w1.find?_insert, hwf.find?_insert]; simp

/-- **THE PAYLOAD, AT A PARAMETERISED NESTED BLOCK.**  Both conjuncts of §5's constructor at one
block, one restoration, one constant map — plus `Ordered` of the result, which is what
`VEnv.WF.ordered` would need at this step, and the two "the companion is declared nowhere"
facts that make the statement nested rather than a disguised ordinary block. -/
theorem ntreeAux_addInductN {m : Lean.ConstMap} (hwf : m.WF)
    (hfr : ∀ n ∈ [``NTree, ``NTree.node, ``NTree.rec, ``NTree.rec_1], m.find? n = none) :
    ∃ m' env', AddInductN m env₁ ntreeAux m' env' ∧
      env₁.addInductR ntreeAux ntreeK ntreeRestore = some env' ∧
      m'.find? ``NTree.rec_1 = some (.recInfo ntreeRec1CI) ∧
      m'.find? `_nested.List_1 = m.find? `_nested.List_1 ∧
      env'.constants `_nested.List_1 = none := by
  obtain ⟨m', env', H, hr1, -, hcomp, he⟩ := ntree_addInductStagesR h hwf hfr
  refine ⟨m', env', ⟨ntreeK, ntreeRestore, H,
    ⟨fun _ => 1, ntreeAux_WF', ntreeRestore_ownId, ntreeRestore_faithful h, he⟩⟩, he, hr1,
    hcomp, ?_⟩
  have hnm : (`_nested.List_1 : Lean.Name) ∉ ntreeAux.allNamesCR ntreeRestore ntreeK := by
    rw [ntreeAux_allNamesCR]; decide
  rw [VEnv.addInductR_constants_of_not_mem he hnm,
    VEnv.addInduct'_constants_of_not_mem h (by decide)]
  rfl


/-! ### 7a. …with `Ordered`, and with nothing hypothesised about the history

`ntreeAux_addInductR_ordered` (`Theory/Inductive/NestedTele.lean:4279`, arity 0, hole-free) is
`Ordered` after the nested step at this block, with all three obligations of
`VEnv.addInductR_ordered'` discharged.  Composed with §7 it gives the payload **and** the
environment fact `VEnv.WF.ordered`'s nested arm would need, at one block, with the declaration
history existentially closed. -/

omit h in
/-- **THE HEADLINE.**  `AddInduct`'s constructor payload, `Ordered` of the result, the restored
type of the renamed auxiliary recursor, and the fact that the companion member is declared
nowhere — at `ntreeAux`, with only `m.WF` and freshness of the four declared names assumed. -/
theorem ntreeAux_addInductN_ordered {m : Lean.ConstMap} (hwf : m.WF)
    (hfr : ∀ n ∈ [``NTree, ``NTree.node, ``NTree.rec, ``NTree.rec_1], m.find? n = none) :
    ∃ (env₁ : VEnv) (m' : Lean.ConstMap) (env' : VEnv),
      VEnv.empty.addInduct' listDecl = some env₁ ∧
      AddInductN m env₁ ntreeAux m' env' ∧
      env'.Ordered ∧
      env'.constants ``NTree.rec_1 = some ⟨2, ntreeAux.recTypeR ntreeRestore 1⟩ ∧
      m'.find? ``NTree.rec_1 = some (.recInfo ntreeRec1CI) ∧
      env'.constants `_nested.List_1 = none := by
  obtain ⟨E₁, E', h, he', hord⟩ := ntreeAux_addInductR_ordered
  obtain ⟨m', env', H, he, hr1, -, hnone⟩ := ntreeAux_addInductN h hwf hfr
  cases Option.some.inj (he.symm.trans he')
  exact ⟨E₁, m', E', h, H, hord, (ntreeAux_recs_declared he).2, hr1, hnone⟩

/-! ### 7b. The construction is **not** an ordinary block in disguise

`ntreeAux_not_addInduct'` is the exact reason `AddInduct.to_addInduct`
(`Verify/Environment/Basic.lean:153`) cannot be kept: its conclusion
`env₁.addInduct' decl = some env₂` is **false** at this payload, not merely unproved.
`addInduct'` declares the companion member and its constructors; the nested step declares
neither. -/

theorem ntreeAux_not_addInduct' {m : Lean.ConstMap} (hwf : m.WF)
    (hfr : ∀ n ∈ [``NTree, ``NTree.node, ``NTree.rec, ``NTree.rec_1], m.find? n = none) :
    ∃ m' env', AddInductN m env₁ ntreeAux m' env' ∧
      env₁.addInduct' ntreeAux ≠ some env' := by
  obtain ⟨m', env', H, -, -, -, hnone⟩ := ntreeAux_addInductN h hwf hfr
  refine ⟨m', env', H, fun hc => ?_⟩
  have hmem : env'.constants `_nested.List_1
      = some ⟨ntreeAux.uvars, nlistMember.type⟩ := VEnv.addInduct'_types hc nlistMember_mem
  rw [hnone] at hmem
  exact absurd hmem nofun

end

/-! ## 8. Non-vacuity, stated separately from hole-freeness

`docs/vacuity-ledger.md` §0's rule: a clean axiom line is not evidence of content.  So:

* the two hypotheses of §7 are jointly satisfiable — `({} : Lean.ConstMap)` is `WF` and fresh
  everywhere, and `VEnv.empty.addInduct' listDecl` really is a `some`.
  `ntreeAux_addInductN_nonvacuous` discharges both, so the payload is *inhabited*, not merely
  derivable;
* the payload's own content is not degenerate: `AddInductStagesR` carries four `TrConstant`s
  whose `TrExprS` components are §3's derivations against the types **Lean's kernel stores**;
  `Faithful` is `ntreeRestore_faithful` (the `List`-agreement equations); `AddNestedStep` carries
  `ntreeAux.WF`;
* and the block is genuinely nested where it matters: `NTree.rec_1` is declared (§7a) while
  `_nested.List_1` is not, which is the configuration that refutes `AddInductStages` and makes
  `AddInduct.to_addInduct` false (§7b). -/

/-- **The payload is inhabited with nothing assumed at all.** -/
theorem ntreeAux_addInductN_nonvacuous :
    ∃ (env₁ : VEnv) (m' : Lean.ConstMap) (env' : VEnv),
      AddInductN ({} : Lean.ConstMap) env₁ ntreeAux m' env' ∧ env'.Ordered := by
  obtain ⟨env₁, m', env', -, H, hord, -, -, -⟩ :=
    ntreeAux_addInductN_ordered (m := {}) Lean.SMap.WF.empty
      (fun _ _ => by simp [Lean.SMap.find?])
  exact ⟨env₁, m', env', H, hord⟩

end InductiveDeclExamples

/-! ## 10. The residual, exactly

With the constructor in hand, what is left is **one** thing on the abstract side, and it is not
about the constructor: `VEnv.WF.ordered` (`Theory/Typing/EnvLemmas.lean`, cone 3226) has an
`induct` arm which for a nested step is `VEnv.addInductR_ordered`, and that reduces
(`VEnv.addInductR_ordered'`, `Theory/Inductive/NestedOrdered.lean:146`) to exactly three
obligations:

| | obligation | live general route |
|---|---|---|
| (A) | `hctors` — the restored **constructor** types are `VConstant.WF` at stage 1 | `VEnv.ctorConstsCR_wf_of_substC'` |
| (B) | `hrecs` — the restored **recursor** types are `VConstant.WF` at stage 2 | `VEnv.recConstsR_wf_of_blocksD` / `_of_entriesD` |
| (C) | `hrules` — the restored **ι-rules** are `VDefEq.WF` at stage 3 | `VEnv.iotaRulesRS_wf_of_hargsD` (and `…_of_hargsD_of_barrier`) |

`ordered_of_obligations` below is the precise statement that **nothing else** is missing: the
payload supplies `henv`'s companions (`D.WF env`, `R.OwnId D K`, the `addInductR` equation) from
inside itself, so a caller who has the three obligations has `Ordered` with no further input.
That is the sharpest form of "the residual is exactly the three" this file can prove without
inverting `VEnv.Ordered` (an inductive over the *construction*, so a genuine converse
"`Ordered env'` → the three obligations" needs an inversion of the `addConstList` chain, which is
**not** proved here and is not claimed).

**Status of the three, re-measured 2026-09-03 (see `docs/handoff-flipconstruct.md` §1).**  All
three are theorems *in general at `D.params = []`*, and all three are theorems *hypothesis-free
at `ntreeAux`* (arity 0: `ntreeAux_obligationA/B/C`, cones 3594/5407/5643).  What is open is the
general parameterful case, and each is an ordinary open theorem — **not** one of the thirteen
holes.

**Where a hole does appear, and how far it is from here.**  (B) and (C)'s general routes take
`hσ : (R.csubst D K).WFD env e₃ D.recUvars`, whose `val` field is `VIndRestore.ValAt` — node 3 of
`Verify/Inductive/RestrictStep.lean`'s cycle.  That file's `restrictStep_entry` (arity 9, cone
3257, hole-free) is an `↔` showing every node of the cycle is interderivable with
`VIndRestore.ValStrengthen`, and `valStrengthen_endpoints_clean` shows the latter is a **plain**
instance of `VEnv.AxiomConservativityWF` ≡ `StrengtheningTarget`, one of the thirteen holes
(`Theory/Typing/UniqueTyping.lean`, the comment above `IsDefEqU.weakN_iff`).  So:

* the general (B)/(C) routes have **no known entry other than that instance family** — the `↔` is
  what makes that a measurement rather than a guess;
* but they are **not provably dependent on the hole**: `RestrictStep.lean` §3a discharges an
  instance of the family *with no hole at all* (`type_tac` on the concrete spine at this very
  block), so the family is not equivalent to the hole pointwise.  Whether it is strictly weaker is
  open, and is the question a concurrent stream is asking in `StrengthenFamily.lean`; a second
  concurrent stream is delivering `ValAt` unconditionally at this same `ntreeAux` block in
  `ValAtParam.lean`.  Both are the same node as the one named here, and this file deliberately
  does not duplicate either. -/

namespace AddInductN

/-- **THE RESIDUAL, ISOLATED.**  At the payload's own `K` and `R`: `Ordered` after the step needs
*exactly* `addInductR_ordered'`'s three obligations and nothing else — `D.WF env₁`, `R.OwnId D K`
and the `addInductR` equation all come out of the payload.

Stating the obligations at a **fixed** `K`/`R` rather than universally is not cosmetic.  A `∀ K R`
form would demand `VConstant.WF` of the constant lists a *junk* restoration produces, which is
false in general; the hypothesis set would then be unsatisfiable and the lemma vacuous — the
defect `docs/vacuity-ledger.md` §0 is about.  §10a's `ntreeAux_ordered_via_residual` is the
inhabitation check: the same three obligations, at the same fixed `K`/`R`, holding at `ntreeAux`. -/
theorem ordered_of_obligations {env₁ env₂ : VEnv} {D : VInductDecl'}
    {K : List Name} {R : VIndRestore}
    (hns : VEnv.AddNestedStep env₁ D K R env₂) (henv : env₁.Ordered)
    (hctors : ∀ {e₁ : VEnv}, env₁.addConstList (D.typeConstsC K) = some e₁ →
      ∀ c ∈ D.ctorConstsCR R K, c.2.WF e₁)
    (hrecs : ∀ {e₁ e₂ : VEnv}, env₁.addConstList (D.typeConstsC K) = some e₁ →
      e₁.addConstList (D.ctorConstsCR R K) = some e₂ → ∀ c ∈ D.recConstsR R K, c.2.WF e₂)
    (hrules : ∀ {e₁ e₂ e₃ : VEnv}, env₁.addConstList (D.typeConstsC K) = some e₁ →
      e₁.addConstList (D.ctorConstsCR R K) = some e₂ →
      e₂.addConstList (D.recConstsR R K) = some e₃ → ∀ df ∈ D.iotaRulesRS R K, df.WF e₃) :
    env₂.Ordered := by
  obtain ⟨npJ, hwf, hown, -, he⟩ := hns
  exact VEnv.addInductR_ordered' henv hwf hown hctors hrecs hrules he

/-- …and the payload is the pair the lemma above consumes. -/
theorem exists_pair {m₁ m₂ : Lean.ConstMap} {env₁ env₂ : VEnv} {D : VInductDecl'}
    (H : AddInductN m₁ env₁ D m₂ env₂) :
    ∃ K R, AddInductStagesR m₁ env₁ D K R m₂ env₂ ∧
      VEnv.AddNestedStep env₁ D K R env₂ := H

end AddInductN

/-! ### 10a. The residual's hypotheses are inhabited at `ntreeAux`

A reduction whose hypothesis set is empty proves nothing (`docs/vacuity-ledger.md` §0), so §10's
three obligations are exhibited holding **at the same fixed `K`/`R` the payload witnesses**, with
the constant map and the declaration history closed off. -/

namespace InductiveDeclExamples

theorem ntreeAux_ordered_via_residual : ∃ (env₁ : VEnv) (m' : Lean.ConstMap) (env' : VEnv),
    VEnv.empty.addInduct' listDecl = some env₁ ∧
    AddInductStagesR ({} : Lean.ConstMap) env₁ ntreeAux ntreeK ntreeRestore m' env' ∧
    VEnv.AddNestedStep env₁ ntreeAux ntreeK ntreeRestore env' ∧ env'.Ordered := by
  obtain ⟨env₁, hL⟩ : ∃ e, VEnv.empty.addInduct' listDecl = some e := ⟨_, rfl⟩
  obtain ⟨m', env', hst, -, -, -, he⟩ :=
    ntree_addInductStagesR hL Lean.SMap.WF.empty (fun _ _ => by simp [Lean.SMap.find?])
  obtain ⟨E₁, E₂, E₃, hE₁, hE₂, hE₃⟩ := ntreeAux_stages hL
  have hns : VEnv.AddNestedStep env₁ ntreeAux ntreeK ntreeRestore env' :=
    ⟨fun _ => 1, ntreeAux_WF', ntreeRestore_ownId, ntreeRestore_faithful hL, he⟩
  exact ⟨env₁, m', env', hL, hst, hns,
    AddInductN.ordered_of_obligations hns (listEnv_ordered hL)
      (fun {F₁} hF₁ => ntreeAux_ctorConstsCR_wf hL (listEnv_ordered hL) hE₁ hF₁)
      (fun {F₁ F₂} hF₁ hF₂ => ntreeAux_recConstsR_wf hL hE₁ hE₂ hF₁ hF₂)
      (fun {F₁ F₂ F₃} hF₁ hF₂ hF₃ => ntreeAux_iotaRulesRS_wf hL hE₁ hE₂ hE₃ hF₁ hF₂ hF₃)⟩

end InductiveDeclExamples

/-! ## 9. Axiom audit -/

#print axioms Lean4Lean.InductiveDeclExamples.nlistMember_mem
#print axioms Lean4Lean.InductiveDeclExamples.tr_ntreeType
#print axioms Lean4Lean.InductiveDeclExamples.tr_ntreeNodeType
#print axioms Lean4Lean.InductiveDeclExamples.tr_ntreeRecType0
#print axioms Lean4Lean.InductiveDeclExamples.tr_ntreeRecType1
#print axioms Lean4Lean.InductiveDeclExamples.indShapeOf_ntreeInd
#print axioms Lean4Lean.InductiveDeclExamples.ctorShapeOf_ntreeNodeCI
#print axioms Lean4Lean.AddInductN.le
#print axioms Lean4Lean.AddInductN.map_wf
#print axioms Lean4Lean.AddInductN.find?_shape
#print axioms Lean4Lean.AddInductN.defeqs_and_anti_lie
#print axioms Lean4Lean.AddInductN.to_addNestedStep
#print axioms Lean4Lean.AddInductN.to_addInductR
#print axioms Lean4Lean.InductiveDeclExamples.ntree_addInductStagesR
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_addInductN
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_addInductN_ordered
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_not_addInduct'
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_addInductN_nonvacuous
#print axioms Lean4Lean.AddInductN.ordered_of_obligations
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_ordered_via_residual

end Lean4Lean
