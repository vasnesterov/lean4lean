import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Theory.Inductive.ProjGen

/-!
# The refutation, re-run against the generalisation

`MutNonRec.projCore_arity_wrong` (`Verify/StructureBridge.lean`) is the machine-checked
refutation of weakening `VEnv.IsStructure.types` from `D.types = [T]` to `T ∈ D.types`: at
`MutNonRec.decl2` — a two-type, non-recursive block, the abstract image of a block Lean's own
kernel accepts `.proj` on and performs structure eta at — `projCore`'s argument spine has
**3** entries between the head and the end while `recType` demands `recArity = 5`.

A repair that does not visibly kill its own witness has not been shown to work.  This file
fires the same measurement at `projCoreG` (`Verify/Typing/ProjGen.lean`), **at `decl2`
itself**, and the mismatch is gone: the spine has 5 entries, `recArity` is 5, and the
`nm + nmin = 2` side condition that `recArity_eq_projCore_iff` makes the whole thing turn on
is *not* needed — `decl2` fails it (`¬ decl2.nm + decl2.nmin = 2` is one of
`projCore_arity_wrong`'s own conjuncts) and the generalised spine saturates anyway.
-/

set_option maxHeartbeats 2000000

namespace Lean4Lean
namespace MutNonRec

open VExpr

/-- **The generalised spine saturates the recursor at the refutation's own witness.**

Read against `projCore_arity_wrong`'s conjuncts: there, spine length `3` against
`recArity = 5`, with `¬ decl2.nm + decl2.nmin = 2`.  Here, spine length `5` against
`recArity = 5`, with the same block and the same `nm`/`nmin`. -/
theorem projCoreG_arity_right (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (i j : Nat) (earlier : List VExpr) (e : VExpr) :
    -- the motive block is full length…
    (decl2.padMotives T C us [] [] i j earlier e).length = 2 ∧
    -- …and so is the minor block…
    (decl2.padMinors (decl2.projLvls C us i) []
      (decl2.padMotives T C us [] [] i j earlier e)
      ((T.projMotive C us [] [] i earlier).mkApp ([] ++ [e])) i j).length = 2 ∧
    -- …so the spine `projCoreG` hands the recursor has five entries…
    (([] : List VExpr) ++ decl2.padMotives T C us [] [] i j earlier e ++
      decl2.padMinors (decl2.projLvls C us i) []
        (decl2.padMotives T C us [] [] i j earlier e)
        ((T.projMotive C us [] [] i earlier).mkApp ([] ++ [e])) i j ++ [] ++ [e]).length = 5 ∧
    -- …which is exactly what the recursor binds.
    decl2.recArity (decl2.types.getD 0 default) = 5 := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact (VInductDecl'.length_padMotives ..).trans rfl
  · exact (VInductDecl'.length_padMinors ..).trans rfl
  · exact (VInductDecl'.length_projCoreG_spine decl2 T C us rfl).trans rfl

/-- …and the identity holds at `decl2` for the same reason it holds anywhere: no
`nm + nmin = 2` side condition is involved.  `decl2` **fails** that side condition, which is
what made the weakening false. -/
theorem projCoreG_arity_right' (C : VIndCtor) (us : List VLevel)
    (i j : Nat) (earlier : List VExpr) (e : VExpr) :
    (([] : List VExpr) ++
        decl2.padMotives (decl2.types.getD 0 default) C us [] [] i j earlier e ++
      decl2.padMinors (decl2.projLvls C us i) []
        (decl2.padMotives (decl2.types.getD 0 default) C us [] [] i j earlier e)
        (((decl2.types.getD 0 default).projMotive C us [] [] i earlier).mkApp ([] ++ [e]))
        i j ++ [] ++ [e]).length
      = decl2.recArity (decl2.types.getD 0 default) ∧
    ¬ decl2.nm + decl2.nmin = 2 :=
  ⟨VInductDecl'.recArity_eq_projCoreG decl2 (decl2.types.getD 0 default) C us rfl rfl,
    by decide⟩

/-! ## The head identification, fired

`minorBody_instAll_spine` is the index computation the whole generalisation turns on: minor
`q`'s declared body reads motive `t` out of the spine `ps ++ mots ++ mins<q`.  An off-by-one
there would be invisible to every arity check above — the spine has the right *length* either
way — so it is fired here at two different `(q, t)` pairs of `decl2`, with **distinct**
motives in the block, so that reading the wrong one would not typecheck.

`decl2`'s two types have no fields and no indices, so `nf = nr = np = 0` and what is exercised
is precisely the `q + (nm - 1 - t)` half of the index. -/

theorem minorBody_head_at_decl2 (lvls : List VLevel) (m0 m1 a0 : VExpr) (C : VIndCtor) :
    -- minor 0, a constructor of the block's type 0, reads motive `m0`…
    VExpr.instAll ((decl2.minorBody 0 0 C).instL lvls) ([] ++ [m0, m1] ++ [])
        ((decl2.minorBinders 0 C).map (VExpr.instL lvls)).length
      = (m0.liftN ((decl2.minorBinders 0 C).map (VExpr.instL lvls)).length).mkApp
          (decl2.minorBodyArgs lvls 0 C ([] ++ [m0, m1] ++ [])) ∧
    -- …and minor 1, a constructor of type 1, reads `m1` — one further along the spine, and
    -- with one more entry of the accumulator below it.
    VExpr.instAll ((decl2.minorBody 1 1 C).instL lvls) ([] ++ [m0, m1] ++ [a0])
        ((decl2.minorBinders 1 C).map (VExpr.instL lvls)).length
      = (m1.liftN ((decl2.minorBinders 1 C).map (VExpr.instL lvls)).length).mkApp
          (decl2.minorBodyArgs lvls 1 C ([] ++ [m0, m1] ++ [a0])) :=
  ⟨decl2.minorBody_instAll_spine rfl rfl rfl rfl (by decide),
   decl2.minorBody_instAll_spine rfl rfl rfl rfl (by decide)⟩

/-- **`padMinor_beta`'s `hget` premise is satisfiable, and at the padding entry.**  At the
projected index the block holds the *real* motive; at the other index it holds a `padMotive`,
which is what `padMinor_beta` reads.  Both directions, at `decl2` with `j = 0`. -/
theorem padMotives_at_decl2 (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (i : Nat) (earlier : List VExpr) (e : VExpr) :
    (decl2.padMotives T C us [] [] i 0 earlier e)[0]?
        = some (T.projMotive C us [] [] i earlier) ∧
    (decl2.padMotives T C us [] [] i 0 earlier e)[1]?
        = some (decl2.padMotive (decl2.types.getD 1 default) us []
            ((T.projMotive C us [] [] i earlier).mkApp ([] ++ [e]))) :=
  ⟨decl2.padMotives_getElem_eq T C us [] [] i 0 earlier e (by decide),
   decl2.padMotives_getElem_ne T C us [] [] i 0 earlier e (by decide) (by decide)⟩

end MutNonRec

/-! ## The recursive constructor, fired

`padMinor_hasType_gen` (`ProjGen.lean`) drops `padMinor_hasType_norec`'s `recFields = []`.
Its two syntactic ingredients — `minorTele_gen` and `minorBodyArgs_gen` — are fired here at a
block whose single constructor **is** recursive, so `nr = 1` and the induction-hypothesis
binder is really in the way.  `decl2` cannot test this: every constructor of `decl2` is
nullary, so `nr = 0` there and the `liftN nr` the generalisation introduces is the identity.

Each firing comes with a **negative control**: the statement with the induction hypothesis
ignored — which is exactly what the `norec` lemmas assert — is rejected by the elaborator.
Neither error is an arity error: both lists have the right length either way, so no length or
arity check in this cluster would have caught the difference. -/

namespace MutRec

open VExpr

/-- One type, one constructor, one **recursive** field: `R.mk : R → R`.  Declared for real so
that `isRec` is checked against Lean's own elaborator rather than read off `Add.lean`. -/
inductive R where | mk : R → R

/-! **[EV]** `R` is recursive, has one constructor and no indices — so it is the shape
`VEnv.IsStructure.noRec` excludes, and `isNonRecStructure` rejects it.  The `#eval` fails the
build if any of that stops holding. -/
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let some (.inductInfo v) := env.find? ``R | throwError "MutRec.R is not an inductive"
  unless v.isRec = true do throwError "MutRec.R.isRec is no longer true"
  unless v.numParams = 0 && v.numIndices = 0 do throwError "MutRec.R arity moved"
  unless v.ctors = [``R.mk] do throwError "MutRec.R.ctors moved"
  if Lean.isNonRecStructure env ``R then
    throwError "isNonRecStructure now accepts a recursive one-constructor inductive"

/-- The constructor, abstractly: one field, recorded as recursive into block member `0`.
As with `decl2`, only the shape data matters and no `WF` claim is made. -/
def rmk : VIndCtor where
  name := `MutRec.R.mk
  params := []
  fields := [{ type := .const `MutRec.R [], lvl := .succ .zero,
               recArg := some { binders := [], idx := 0, args := [] } }]
  args := []

/-- The block. -/
def decl1r : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := false
  types := [{ name := `MutRec.R, type := .sort (.succ .zero), indices := [], ctors := [rmk] }]

/-- `nr = 1` at this block, and the induction hypothesis is `motive field` — motive at
`.bvar 1`, the field it is about at `.bvar 0`. -/
theorem ihTypes_at_rmk :
    decl1r.ihTypes 0 rmk = [VExpr.app (.bvar 1) (.bvar 0)] ∧
    (decl1r.ihTypes 0 rmk).length = 1 ∧ rmk.recFields.length = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- **`minorTele_gen` fired at a recursive constructor.**  The minor's telescope is *not* the
field telescope: it is the field `R` followed by the induction hypothesis `m f`, with the
motive `m` weakened past the field binder.

Negative control (run outside the tree; the `norec` collapse `= [const R []]` is what
`minorTele_norec` would give):

    error: Application type mismatch: The argument `rfl` has type `?m = ?m`
    but is expected to have type
      instAllTele (List.map (fun F => instL [] F.type) rmk.fields) [] ++
          instAllTele (List.map (instL []) (decl1r.ihTypes 0 rmk)) ([] ++ [m] ++ [])
            rmk.fields.length
        = [const `MutRec.R []] -/
theorem minorTele_at_rmk (m : VExpr) :
    VExpr.instAllTele ((decl1r.minorBinders 0 rmk).map (VExpr.instL [])) ([] ++ [m] ++ [])
      = [VExpr.const `MutRec.R [], VExpr.app (m.liftN 1) (.bvar 0)] :=
  (decl1r.minorTele_gen (lvls := []) (us := []) (q := 0) (C := rmk) (ps := [])
    (mots := [m]) (acc := []) rfl rfl rfl).trans rfl

/-- **`minorBodyArgs_gen` fired at a recursive constructor.**  The constructor applied to its
own field is `R.mk (.bvar 1)`, **not** `R.mk (.bvar 0)`: the induction hypothesis sits below
the field, so the field has moved up by one.  That shift is the entire content of the
recursive case, and it is invisible to any arity check — the spine has one entry either way.

Negative control (run outside the tree; `.bvar 0` is the `nr = 0` reading, which is what
`minorBodyArgs_norec` gives):

    error: Application type mismatch: The argument `rfl` has type `?m = ?m`
    but is expected to have type
      List.map (fun x => liftN (decl1r.ihTypes 0 rmk).length x)
          (List.map (fun a => (instL [] a).instAll [] rmk.fields.length) rmk.args ++
            [(const rmk.name []).mkApp
              (List.map (fun x => liftN rmk.fields.length x) [] ++ bvars 0 rmk.fields.length)])
        = [(const `MutRec.R.mk []).mkApp [bvar 0]] -/
theorem minorBodyArgs_at_rmk (m : VExpr) :
    decl1r.minorBodyArgs [] 0 rmk ([] ++ [m] ++ [])
      = [(VExpr.const `MutRec.R.mk []).mkApp [.bvar 1]] :=
  (decl1r.minorBodyArgs_gen (lvls := []) (us := []) (q := 0) (C := rmk) (ps := [])
    (mots := [m]) (acc := []) rfl rfl rfl rfl).trans rfl

end MutRec

/-! ## Block A's prerequisite is bigger than `ProjClosed`'s three fields

`docs/handoff-projections.md` §0.4 item 3 names the prerequisite of the `lift'`/`instN`/`instL`
commutation lemmas for `projCoreG` as "`ProjClosed` generalised to every block member
(`ClosedTele` for *each* `T'.indices` and each `C'.fields`)".  **That is not sufficient**, and
the reason is exactly what this round changed: `projCoreG`'s minor block is built over
`minorBinders`, which contains `ihTypes`, which splices in a recursive field's stored `ξ`
(`VIndRecArg.binders`) and `π` (`.args`).

`VExpr.lift'_instAllTele` — the step every one of those commutations runs on — asks for
`ClosedTele ((D.minorBinders q C').map (·.instL lvls)) (D.np + D.nm + q)`.  The block below
satisfies all three fields of `ProjClosed` and **fails** that.

**Register.**  This is a counterexample to an *implication between predicates*, which is what
a hypothesis-sufficiency claim is: `ProjClosed` is a hypothesis the commutation lemmas take,
so the question is whether its fields determine the closedness the proof needs, and they do
not.  `blockOf badCtor` is **not** a well-formed declaration — `VIndField.WF.pos` (the `some r`
branch) demands `OnCtx (r.binders.reverse ++ Γ)`, which forces `r.binders` closed at
`np + i` — so nothing here says a real block breaks.  It says the *generalised predicate*
must record the recursive-field data, or the commutation lemmas must take `D.WF env` and
derive it. -/

namespace ProjClosedGap

open VExpr

/-- The type constant of the one-member block below. -/
def qty : VExpr := .const `ProjClosedGap.Q []

/-- One recursive field whose stored `ξ` is **not** closed at its declared arity: it is
`[.bvar 0]` over `params ++ fields<0 = []`. -/
def badCtor : VIndCtor where
  name := `ProjClosedGap.Q.mk
  params := []
  fields := [{ type := qty, lvl := .succ .zero,
               recArg := some { binders := [.bvar 0], idx := 0, args := [] } }]
  args := []

/-- The same with `ξ` empty — the positive control. -/
def goodCtor : VIndCtor where
  name := `ProjClosedGap.Q.mk
  params := []
  fields := [{ type := qty, lvl := .succ .zero,
               recArg := some { binders := [], idx := 0, args := [] } }]
  args := []

/-- A one-type block with no parameters and no indices around a given constructor. -/
def blockOf (C : VIndCtor) : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := false
  types := [{ name := `ProjClosedGap.Q, type := .sort (.succ .zero), indices := [], ctors := [C] }]

/-- The minor's telescope at `badCtor`: the field, then the induction hypothesis, whose own
binder is the stored `ξ` shifted to `.bvar 2` — one past the `k = 2` the closedness check
allows at that entry. -/
theorem minorBinders_bad :
    ((blockOf badCtor).minorBinders 0 badCtor).map (VExpr.instL [])
      = [qty, .forallE (.bvar 2) ((VExpr.bvar 2).app ((VExpr.bvar 1).app (.bvar 0)))] := rfl

/-- The same at `goodCtor`: no `ξ` binder, and the ih's own two variables (`.bvar 1` the
motive, `.bvar 0` the field) are both in range. -/
theorem minorBinders_good :
    ((blockOf goodCtor).minorBinders 0 goodCtor).map (VExpr.instL [])
      = [qty, (VExpr.bvar 1).app (.bvar 0)] := rfl

/-- **The three fields of `ProjClosed` do not imply the closedness block A needs.**  All
three hold at `blockOf badCtor`; the minor's telescope is not closed at the spine arity. -/
theorem projClosedG_needs_recArgs :
    VExpr.ClosedTele (blockOf badCtor).params 0 ∧
    VExpr.ClosedTele ((blockOf badCtor).types.getD 0 default).indices (blockOf badCtor).np ∧
    VExpr.ClosedTele (badCtor.fields.map (·.type)) (blockOf badCtor).np ∧
    ¬ VExpr.ClosedTele (((blockOf badCtor).minorBinders 0 badCtor).map (VExpr.instL []))
        ((blockOf badCtor).np + (blockOf badCtor).nm + 0) := by
  refine ⟨trivial, trivial, ⟨trivial, trivial⟩, ?_⟩
  rw [minorBinders_bad]
  show ¬ VExpr.ClosedTele [qty, .forallE (.bvar 2) _] 1
  simp [VExpr.ClosedTele, VExpr.ClosedN, qty]

/-- **The positive control**: with the stored `ξ` closed, the same telescope *is* closed.  So
what fails above is precisely the recursive-field data, not the shape of `ihTypes`. -/
theorem projClosed_ok_without_recArgs :
    VExpr.ClosedTele (((blockOf goodCtor).minorBinders 0 goodCtor).map (VExpr.instL []))
      ((blockOf goodCtor).np + (blockOf goodCtor).nm + 0) := by
  rw [minorBinders_good]
  show VExpr.ClosedTele [qty, _] 1
  simp [VExpr.ClosedTele, VExpr.ClosedN, qty]

end ProjClosedGap
end Lean4Lean
