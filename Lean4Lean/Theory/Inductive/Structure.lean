import Lean4Lean.Theory.Inductive.Decl

/-!
# Structures and their projections

A *structure* is an inductive block with one type and one constructor.  `Lean.Expr` makes
projection out of one a primitive (`Expr.proj`), but `VExpr` does not — it has only
`bvar`/`sort`/`const`/`app`/`lam`/`forallE`.  So the abstract counterpart of `Expr.proj`
has to be the term a projection *is*: an application of the block's recursor.

This file supplies the two things `Verify/Typing/Expr.lean`'s `TrProj` is built from:

* `VInductDecl'.projTerm`, the recursor application, and
* `VEnv.IsStructure`, saying that an environment declares a given name as a structure.

It follows `docs/design-inductive.md` §6.2, and is deliberately additive: it imports
`Decl.lean` and modifies nothing there.

## What is *not* here

`VEnv.HasInduct` and its uniqueness lemma (the design ledger's G1/G4) are not built.
`IsStructure.decl` below asks directly for a well-formed `addInduct'` step in the
environment's past, which is what G1 would deliver and is enough for everything except
*functionality* of `TrProj` — see the blocked-lemma comments in
`Verify/Typing/Lemmas.lean`.
-/

namespace Lean4Lean

open VExpr

namespace VInductDecl'

variable (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)

/-- The recursor application computing the `i`-th projection of `e`, given the earlier
projections `earlier = [proj 0 x, …, proj (i-1) x]` of the motive's major-premise binder
`x`:

```
S.rec.{ℓ, us} ps (fun ι x => Aᵢ[ps, proj 0 x, …, proj (i-1) x])
              (fun f₀ … f_{n-1} => fᵢ) ι e
```

Three things about this are load-bearing.

*The motive projects its own binder.*  Field `i`'s type may mention the earlier fields,
so the result type of `proj i e` is `Aᵢ` with those replaced by projections of `e` — which
is exactly what the kernel computes when `inferProj` instantiates a dependent field binder
with `.proj I_name i struct` (`TypeChecker.lean:233`).  Hence the `earlier` parameter,
threaded by `projArgs`.

*The elimination level is the field's own sort*, `F.lvl.inst us`.  That is the small-
elimination side condition in disguise: for a structure whose sort is not `isNeverZero`,
`inferProj` requires every dependent field domain and the projected domain to be a `Prop`
(F17), which is precisely what keeps this level legal.  The implementation's guard and
the encoding's requirement agree — checked, not assumed; see
`Theory/Inductive/StructureExamples.lean`, where `And` (a `Prop` structure with `Prop`
fields) validates on this path.

*The minor premise binds only the fields*, so this is correct only for a constructor with
no recursive fields — which `VEnv.IsStructure.noRec` demands.  A recursive
single-constructor inductive would need the induction-hypothesis binders too
(`D.ihTypes`), and while `inferProj` does *not* reject such a type, no `structure`
declaration produces one.  Generalising the minor premise is the fix if
`inferProj.WF` ever needs it. -/
def projCore (ps is : List VExpr) (i : Nat) (earlier : List VExpr) (e : VExpr) : VExpr :=
  let nf := C.fields.length
  let ni := is.length
  let F := C.fields.getD i default
  let lvls := if D.isLE then F.lvl.inst us :: us else us
  -- Everything read out of `D`/`T`/`C` is stored at the *block's own* universe numbering
  -- (`VInductDecl'.ownLvls`), so it has to be moved to the use site's `us` before being
  -- spliced into a term built at `us`.  This is the same step `VInductDecl'.atRec`
  -- performs for the recursor construction, at `selfLvls` instead.
  let ftype := F.type.instL us
  let ftypes := C.fields.map fun F => F.type.instL us
  let indices := T.indices.map (·.instL us)
  let mot :=
    mkLams (instAllTele indices ps) <|
      .lam ((VExpr.const T.name us).mkApp (ps.map (·.liftN ni) ++ bvars 0 ni)) <|
        instAll ftype (ps.map (·.liftN (ni+1)) ++ earlier)
  let minor := mkLams (instAllTele ftypes ps) (.bvar (nf - 1 - i))
  (VExpr.const (Lean.mkRecName T.name) lvls).mkApp (ps ++ [mot, minor] ++ is ++ [e])

/-- `[proj 0 (.bvar 0), …, proj (i-1) (.bvar 0)]`: the earlier projections of a
major-premise binder sitting at de Bruijn index 0, for use in `projCore`'s motive.

**Keep this structural.**  Both recursive calls are at `i`, with the parameter lists
differing (the inner one re-lifted for the motive's extra binders), so this is structural
recursion on the `Nat` and `projTerm` reduces by `rfl`.  The obvious "cleanup" — fusing
this into `projTerm` with `termination_by i` — type-checks but produces a
well-founded definition that does **not** reduce, and every `rfl` check in
`StructureExamples.lean` fails.  The validation suite is only possible in this form. -/
def projArgs (ps is : List VExpr) : Nat → List VExpr
  | 0 => []
  | i+1 =>
    projArgs ps is i ++
      [D.projCore T C us ps is i
        (projArgs (ps.map (·.liftN (is.length+1))) (bvars 1 is.length) i) (.bvar 0)]

/-- The `i`-th projection of `e`, where `e : S.{us} ps ι`. -/
def projTerm (ps is : List VExpr) (i : Nat) (e : VExpr) : VExpr :=
  D.projCore T C us ps is i
    (D.projArgs T C us (ps.map (·.liftN (is.length+1))) (bvars 1 is.length) i) e

end VInductDecl'

/-! ## Commutation with universe instantiation

`projTerm` is built from its inputs by operations that all commute with `instL`, and the
stored data it splices in is moved to `us` first (see `projCore`), so `instL` distributes
with no side conditions.  This is what `TrProj.instL` runs on.

Note this is exactly the equation that would have been **false** before the `instL us` fix
in `projCore`: the stored field type would have kept a universe parameter of the block,
which `instL ls` would then have rewritten, while `us.map (·.inst ls)` on the right would
not have reached it. -/

/-- Missing companion to `VExpr.instL_instAll` (`Theory/Inductive/Telescope.lean`).
Belongs there; kept here to avoid editing a file another stream owns. -/
@[simp] theorem _root_.Lean4Lean.VExpr.instL_instAllTele :
    (instAllTele As as k).map (VExpr.instL ls) =
      instAllTele (As.map (VExpr.instL ls)) (as.map (VExpr.instL ls)) k := by
  induction As generalizing k <;> simp [*]

namespace VInductDecl'

variable (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)

theorem projCore_instL (ps is : List VExpr) (i : Nat) (earlier : List VExpr) (e : VExpr) :
    (D.projCore T C us ps is i earlier e).instL ls =
      D.projCore T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
        (is.map (VExpr.instL ls)) i (earlier.map (VExpr.instL ls)) (e.instL ls) := by
  simp [projCore, VExpr.instL, List.map_map, Function.comp_def, VExpr.instL_instL]
  split <;> simp [VLevel.inst_inst]

theorem projArgs_instL : ∀ (i : Nat) (ps is : List VExpr),
    (D.projArgs T C us ps is i).map (VExpr.instL ls) =
      D.projArgs T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
        (is.map (VExpr.instL ls)) i
  | 0, _, _ => rfl
  | i+1, ps, is => by
    simp [projArgs, projArgs_instL i, projCore_instL, List.map_map,
      Function.comp_def, VExpr.instL]

theorem projTerm_instL (ps is : List VExpr) (i : Nat) (e : VExpr) :
    (D.projTerm T C us ps is i e).instL ls =
      D.projTerm T C (us.map (VLevel.inst ls)) (ps.map (VExpr.instL ls))
        (is.map (VExpr.instL ls)) i (e.instL ls) := by
  simp [projTerm, projCore_instL, projArgs_instL, List.map_map, Function.comp_def]

end VInductDecl'

/-- `env` declares `S` as a structure: a single-constructor inductive block, with `T` its
one type and `C` its one constructor.

`decl` is stated as "some well-formed `addInduct'` step in `env`'s past declared `D`"
rather than through a `VEnv.HasInduct` predicate, which does not exist yet (ledger G1).
The shape is chosen so that it is *monotone* in `env` — see `IsStructure.mono` — which is
what `TrProj.mono` needs, and so that the keystone's `addInduct'` step supplies it
directly.

Deliberately absent: any claim that `S` belongs to **at most one** block.  That is ledger
G4, it needs `VEnv.Sig` (I1), and it is what `TrProj` would need to be *functional*.  Not
smuggling it in here is the point; the two lemmas that need it are marked blocked in
`Verify/Typing/Lemmas.lean`. -/
structure VEnv.IsStructure (env : VEnv) (S : Lean.Name)
    (D : VInductDecl') (T : VIndType) (C : VIndCtor) : Prop where
  /-- One type in the block… -/
  types : D.types = [T]
  /-- …named `S`… -/
  name : T.name = S
  /-- …with exactly one constructor. -/
  ctors : T.ctors = [C]
  /-- No recursive fields.  Required by `projCore`'s minor premise (see there), and by
  structure eta (F16) independently. -/
  noRec : C.recFields = []
  /-- The block was declared, well-formedly, at some point in `env`'s past. -/
  decl : ∃ env₀ env₁, D.WF env₀ ∧ env₀.addInduct' D = some env₁ ∧ env₁ ≤ env

namespace VEnv.IsStructure

variable {env env' : VEnv} {S : Lean.Name} {D : VInductDecl'} {T : VIndType} {C : VIndCtor}

theorem mono (h : env ≤ env') (H : env.IsStructure S D T C) : env'.IsStructure S D T C :=
  { H with decl := let ⟨_, _, h1, h2, h3⟩ := H.decl; ⟨_, _, h1, h2, h3.trans h⟩ }

/-- The block has exactly one type, so it has exactly one motive. -/
theorem nm_eq (H : env.IsStructure S D T C) : D.nm = 1 := by simp [VInductDecl'.nm, H.types]

/-- …and exactly one minor premise. -/
theorem nmin_eq (H : env.IsStructure S D T C) : D.nmin = 1 := by
  simp [VInductDecl'.nmin, VInductDecl'.ctorsAll, H.types, H.ctors]

end VEnv.IsStructure

end Lean4Lean
