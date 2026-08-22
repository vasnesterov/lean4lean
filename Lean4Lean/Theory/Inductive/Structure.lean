import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.Inductive.TelescopeLift

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


/-! ## F17's occurrence guard

`inferProj` walks the constructor's field telescope and, for each field before the projected
one, distinguishes two cases (`Lean4Lean/TypeChecker.lean:249-257`):

```
if b.hasLooseBVars then
  if maybePropType then if !(← isProp dom) then fail
  r := b.instantiate1 (.proj I_name i struct)
else
  r := b
```

A field whose binder is *unused* by the rest of the telescope is dropped with no `Prop`
check at all.  `FieldUsed` is the abstract image of that `b.hasLooseBVars`. -/

/-- Field `k`'s binder is used by the rest of the constructor's telescope.

`C.type D j = mkPi (C.params ++ C.fields.map (·.type)) (C.canonResult D j)`, so after
binding field `k` the remainder is `mkPi (fields>k) result`, in which field `k` is
`.bvar 0`. -/
def VIndCtor.FieldUsed (C : VIndCtor) (D : VInductDecl') (j k : Nat) : Prop :=
  ¬ VExpr.Skips' 1 (VExpr.mkPi ((C.fields.drop (k+1)).map (·.type)) (C.canonResult D j)) 0

/-- An unused field does not occur in any later field's type.  In `F_i.type`, which lives
over `params ++ fields<i`, field `k` is de Bruijn variable `i - 1 - k`. -/
theorem VIndCtor.not_fieldUsed_skips {C : VIndCtor} {D : VInductDecl'} {j k i : Nat}
    (h : ¬ C.FieldUsed D j k) (hki : k < i) (hi : i < C.fields.length) :
    VExpr.Skips' 1 (C.fields.getD i default).type (i - 1 - k) := by
  have hs : VExpr.Skips' 1
      (VExpr.mkPi ((C.fields.drop (k+1)).map (·.type)) (C.canonResult D j)) 0 :=
    Classical.byContradiction h
  have hm : (((C.fields.drop (k+1)).map (·.type))[i - (k+1)]?)
      = some (C.fields.getD i default).type := by
    rw [List.getElem?_map, List.getElem?_drop,
      show k + 1 + (i - (k+1)) = i from by omega,
      List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have := VExpr.skips'_mkPi_getElem (k := 0) hs hm
  simpa [show 0 + (i - (k+1)) = i - 1 - k from by omega] using this


/-! ## Level bookkeeping for the projection

`recApp_hasType''` states the major premise's type with the block's head at
`D.selfLvls.map (·.inst ls)`; `projCore` and `TrProj` carry it at the use site's `us`.
These agree. -/

theorem map_getD_range {l : List VLevel} : (List.range l.length).map (l.getD · .zero) = l := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- `selfLvls` instantiated at the projection's level list is the use site's `us` — whether
or not a fresh elimination universe was prepended. -/
theorem VInductDecl'.selfLvls_inst (D : VInductDecl') (a : VLevel) {us : List VLevel}
    (h : us.length = D.uvars) :
    D.selfLvls.map (VLevel.inst (if D.isLE then a :: us else us)) = us := by
  simp only [VInductDecl'.selfLvls, List.map_map, Function.comp_def, VLevel.inst]
  split
  · rw [← h]; simpa using map_getD_range (l := us)
  · rw [← h]; exact map_getD_range

/-- The stored telescopes of a structure are closed at their declared arities.

This is what makes `projTerm` commute with context operations, and it is a genuine
precondition rather than a proof-strategy artifact: `projCore` splices the stored data in
via `instAll A as k`, and

```
(instAll A as k).lift' (ρ.consN (k + |as|))
  = instAll (A.lift' (ρ.consN (k + |as|))) (as.map (·.lift' ρ)) k
```

is a `projCore` at lifted arguments only when `A.lift' (ρ.consN (k + |as|)) = A`, i.e. when
`A` is closed at `k + |as|` — which is exactly the declared arity at each splice site.
Without it a stored entry can carry a variable pointing at the ambient context, which the
left-hand lift moves and the right-hand one cannot; see the `decide`-checked refutation in
the scratchpad witness `ProjTermLiftNeedsClosed.lean`.

Not a hypothesis: `VEnv.IsStructure.projClosed` (`Theory/Inductive/StructureClosed.lean`)
derives it from `IsStructure` plus `Ordered env`. -/
structure VInductDecl'.ProjClosed (D : VInductDecl') (T : VIndType) (C : VIndCtor) : Prop where
  /-- The parameter telescope is closed at its own arities. -/
  params : VExpr.ClosedTele D.params 0
  /-- Index `j` lives over `params ++ indices<j`. -/
  indices : VExpr.ClosedTele T.indices D.np
  /-- Field `j` lives over `params ++ fields<j`. -/
  fields : VExpr.ClosedTele (C.fields.map (·.type)) D.np


namespace VInductDecl'

variable (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)

/-! ### Commutation with `lift'`

Unlike `instL`, these carry `ProjClosed`: `projCore` splices the stored telescopes in with
`instAll`, and an entry not closed at its declared arity keeps a variable reaching into the
ambient context, which the lift moves on one side of the equation and not the other.  See
`VExpr.lift'_instAll` and the refutation recorded at `ProjClosed`. -/

theorem length_projArgs : ∀ {i : Nat} {ps is : List VExpr},
    (D.projArgs T C us ps is i).length = i
  | 0, _, _ => rfl
  | i+1, ps, is => by simp [projArgs, length_projArgs (i := i)]

theorem projCore_lift' (hcl : D.ProjClosed T C) {ps is earlier : List VExpr} {e : VExpr}
    {i : Nat} {ρ : Lift}
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hearlier : earlier.length = i) (hi : i < C.fields.length) :
    (D.projCore T C us ps is i earlier e).lift' ρ =
      D.projCore T C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) i
        (earlier.map (·.lift' (ρ.consN (is.length + 1)))) (e.lift' ρ) := by
  have hidx : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) (0 + ps.length) := by
    simpa [hps] using VExpr.ClosedTele.map_instL hcl.indices
  have hfldeq : (C.fields.map fun F => F.type.instL us)
      = (C.fields.map (·.type)).map (VExpr.instL us) := by simp [List.map_map, Function.comp_def]
  have hfld : VExpr.ClosedTele (C.fields.map fun F => F.type.instL us) (0 + ps.length) := by
    rw [hfldeq]; simpa [hps] using VExpr.ClosedTele.map_instL hcl.fields
  have hget : (C.fields.map (·.type))[i]? = some (C.fields.getD i default).type := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hftype : ((C.fields.getD i default).type.instL us).ClosedN
      (0 + (ps.map (·.liftN (is.length+1)) ++ earlier).length) := by
    have := (VExpr.ClosedTele.getElem? hcl.fields hget).instL (ls := us)
    simpa [hps, hearlier] using this
  have e1 : liftTele' ρ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
      = VExpr.instAllTele (T.indices.map (VExpr.instL us)) (ps.map (·.lift' ρ)) :=
    VExpr.lift'_instAllTele (ρ := ρ) (k := 0) (by simpa using hidx)
  have e2 : liftTele' ρ (VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps)
      = VExpr.instAllTele (C.fields.map fun F => F.type.instL us) (ps.map (·.lift' ρ)) :=
    VExpr.lift'_instAllTele (ρ := ρ) (k := 0) (by simpa using hfld)
  have e3 : (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (is.length+1)) ++ earlier)).lift' (ρ.consN is.length).cons
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
        ((ps.map (·.liftN (is.length+1)) ++ earlier).map (·.lift' (ρ.consN (is.length+1)))) :=
    VExpr.lift'_instAll (ρ := ρ.consN (is.length+1)) (k := 0) hftype
  have e4 : (bvars 0 is.length).map (·.lift' (ρ.consN is.length)) = bvars 0 is.length :=
    VExpr.lift'_bvars (lo := 0) (n := is.length) (ρ := ρ.consN is.length)
      (by simpa using Lift.consN_fixes)
  simp only [projCore, VExpr.lift'_mkApp, VExpr.lift', List.map_append, List.map_cons,
    List.map_nil, VExpr.lift'_mkLams, List.length_map, VExpr.length_instAllTele, ← his]
  rw [e1, e2, e3, e4,
    Lift.consN_fixes.liftVar_eq (show C.fields.length - 1 - i < C.fields.length by omega)]
  simp only [List.map_append, List.map_map, Function.comp_def, VExpr.liftN_lift']

theorem projArgs_lift' (hcl : D.ProjClosed T C) :
    ∀ {i : Nat} {ps is : List VExpr} {ρ : Lift},
    ps.length = D.np → is.length = T.indices.length → i ≤ C.fields.length → ρ.Fixes 1 →
    (D.projArgs T C us ps is i).map (·.lift' ρ)
      = D.projArgs T C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) i
  | 0, _, _, _, _, _, _, _ => rfl
  | i+1, ps, is, ρ, hps, his, hi, hρ => by
    have hinner := projArgs_lift' hcl (i := i)
      (ps := ps.map (·.liftN (is.length+1))) (is := bvars 1 is.length)
      (ρ := ρ.consN (is.length+1)) (by simpa using hps) (by simpa using his)
      (by omega) (Lift.consN_fixes.le (by omega))
    have hbv : (bvars 1 is.length).map (·.lift' (ρ.consN (is.length+1))) = bvars 1 is.length :=
      VExpr.lift'_bvars (lo := 1) (n := is.length) (ρ := ρ.consN (is.length+1))
        (by rw [Nat.add_comm]; exact Lift.consN_fixes)
    simp only [projArgs, List.map_append, List.map_cons, List.map_nil]
    rw [projArgs_lift' hcl (i := i) hps his (by omega) hρ,
      projCore_lift' D T C us hcl hps his (D.length_projArgs T C us) (by omega),
      hinner, hbv]
    simp only [VExpr.lift', hρ.liftVar_eq (show 0 < 1 by omega),
      List.map_map, Function.comp_def, VExpr.liftN_lift', List.length_map]

theorem projTerm_lift' (hcl : D.ProjClosed T C) {ps is : List VExpr} {e : VExpr}
    {i : Nat} {ρ : Lift}
    (hps : ps.length = D.np) (his : is.length = T.indices.length) (hi : i < C.fields.length) :
    (D.projTerm T C us ps is i e).lift' ρ =
      D.projTerm T C us (ps.map (·.lift' ρ)) (is.map (·.lift' ρ)) i (e.lift' ρ) := by
  have hbv : (bvars 1 is.length).map (·.lift' (ρ.consN (is.length+1))) = bvars 1 is.length :=
    VExpr.lift'_bvars (lo := 1) (n := is.length) (ρ := ρ.consN (is.length+1))
      (by rw [Nat.add_comm]; exact Lift.consN_fixes)
  simp only [projTerm]
  rw [projCore_lift' D T C us hcl hps his (D.length_projArgs T C us) hi,
    projArgs_lift' D T C us hcl (i := i) (ps := ps.map (·.liftN (is.length+1)))
      (is := bvars 1 is.length) (ρ := ρ.consN (is.length+1))
      (by simpa using hps) (by simpa using his) (by omega) (Lift.consN_fixes.le (by omega)),
    hbv]
  simp only [List.map_map, Function.comp_def, VExpr.liftN_lift', List.length_map]

theorem projCore_instN (hcl : D.ProjClosed T C) {ps is earlier : List VExpr} {e e₀ : VExpr}
    {i k : Nat}
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hearlier : earlier.length = i) (hi : i < C.fields.length) :
    (D.projCore T C us ps is i earlier e).inst e₀ k =
      D.projCore T C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) i
        (earlier.map (·.inst e₀ (k + is.length + 1))) (e.inst e₀ k) := by
  have hidx : VExpr.ClosedTele (T.indices.map (VExpr.instL us)) (0 + ps.length) := by
    simpa [hps] using VExpr.ClosedTele.map_instL hcl.indices
  have hfldeq : (C.fields.map fun F => F.type.instL us)
      = (C.fields.map (·.type)).map (VExpr.instL us) := by simp [List.map_map, Function.comp_def]
  have hfld : VExpr.ClosedTele (C.fields.map fun F => F.type.instL us) (0 + ps.length) := by
    rw [hfldeq]; simpa [hps] using VExpr.ClosedTele.map_instL hcl.fields
  have hget : (C.fields.map (·.type))[i]? = some (C.fields.getD i default).type := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hftype : ((C.fields.getD i default).type.instL us).ClosedN
      (0 + (ps.map (·.liftN (is.length+1)) ++ earlier).length) := by
    have := (VExpr.ClosedTele.getElem? hcl.fields hget).instL (ls := us)
    simpa [hps, hearlier] using this
  have e1 : VExpr.instTele e₀ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) k
      = VExpr.instAllTele (T.indices.map (VExpr.instL us)) (ps.map (·.inst e₀ k)) :=
    VExpr.inst_instAllTele (m := k) (j := 0) (by simpa using hidx)
  have e2 : VExpr.instTele e₀ (VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps) k
      = VExpr.instAllTele (C.fields.map fun F => F.type.instL us) (ps.map (·.inst e₀ k)) :=
    VExpr.inst_instAllTele (m := k) (j := 0) (by simpa using hfld)
  have e3 : (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN (is.length+1)) ++ earlier)).inst e₀ (k + is.length + 1)
      = VExpr.instAll ((C.fields.getD i default).type.instL us)
        ((ps.map (·.liftN (is.length+1)) ++ earlier).map (·.inst e₀ (k + is.length + 1))) :=
    VExpr.inst_instAll (m := k + is.length + 1) (j := 0) hftype
  have e4 : (bvars 0 is.length).map (·.inst e₀ (k + is.length)) = bvars 0 is.length :=
    VExpr.inst_bvars (by omega)
  simp only [projCore, VExpr.inst_mkApp, VExpr.inst, VExpr.instVar, List.map_append,
    List.map_cons, List.map_nil, VExpr.inst_mkLams, List.length_map,
    VExpr.length_instAllTele, ← his]
  have e5 : ∀ (n : Nat) (l : List VExpr),
      l.map (fun x => (x.liftN n).inst e₀ (k + n)) = l.map (fun x => (x.inst e₀ k).liftN n) :=
    fun n l => List.map_congr_left fun x _ => by
      rw [Nat.add_comm k n]; exact (VExpr.liftN_instN_lo n x e₀ k 0 (Nat.zero_le _)).symm
  rw [e1, e2, e3, e4, if_pos (show C.fields.length - 1 - i < k + C.fields.length by omega)]
  simp only [List.map_append, List.map_map, Function.comp_def, Nat.add_assoc, e5]

theorem projArgs_instN (hcl : D.ProjClosed T C) :
    ∀ {i : Nat} {ps is : List VExpr} {e₀ : VExpr} {k : Nat},
    ps.length = D.np → is.length = T.indices.length → i ≤ C.fields.length → 1 ≤ k →
    (D.projArgs T C us ps is i).map (·.inst e₀ k)
      = D.projArgs T C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) i
  | 0, _, _, _, _, _, _, _, _ => rfl
  | i+1, ps, is, e₀, k, hps, his, hi, hk => by
    have hinner := projArgs_instN hcl (i := i)
      (ps := ps.map (·.liftN (is.length+1))) (is := bvars 1 is.length)
      (e₀ := e₀) (k := k + is.length + 1)
      (by simpa using hps) (by simpa using his) (by omega) (by omega)
    have hbv : (bvars 1 is.length).map (·.inst e₀ (k + is.length + 1)) = bvars 1 is.length :=
      VExpr.inst_bvars (by omega)
    have e5 : ∀ (l : List VExpr),
        l.map (fun x => (x.liftN (is.length+1)).inst e₀ (k + is.length + 1))
          = l.map (fun x => (x.inst e₀ k).liftN (is.length+1)) :=
      fun l => List.map_congr_left fun x _ => by
        rw [show k + is.length + 1 = k + (is.length + 1) from by omega, Nat.add_comm k]
        exact (VExpr.liftN_instN_lo (is.length+1) x e₀ k 0 (Nat.zero_le _)).symm
    simp only [projArgs, List.map_append, List.map_cons, List.map_nil]
    rw [projArgs_instN hcl (i := i) hps his (by omega) hk,
      projCore_instN D T C us hcl hps his (D.length_projArgs T C us) (by omega),
      hinner, hbv]
    simp only [VExpr.inst, VExpr.instVar, if_pos (show 0 < k by omega),
      List.map_map, Function.comp_def, e5, List.length_map]

theorem projTerm_instN (hcl : D.ProjClosed T C) {ps is : List VExpr} {e e₀ : VExpr}
    {i k : Nat}
    (hps : ps.length = D.np) (his : is.length = T.indices.length) (hi : i < C.fields.length) :
    (D.projTerm T C us ps is i e).inst e₀ k =
      D.projTerm T C us (ps.map (·.inst e₀ k)) (is.map (·.inst e₀ k)) i (e.inst e₀ k) := by
  have hbv : (bvars 1 is.length).map (·.inst e₀ (k + is.length + 1)) = bvars 1 is.length :=
    VExpr.inst_bvars (by omega)
  have e5 : ∀ (l : List VExpr),
      l.map (fun x => (x.liftN (is.length+1)).inst e₀ (k + is.length + 1))
        = l.map (fun x => (x.inst e₀ k).liftN (is.length+1)) :=
    fun l => List.map_congr_left fun x _ => by
      rw [show k + is.length + 1 = k + (is.length + 1) from by omega, Nat.add_comm k]
      exact (VExpr.liftN_instN_lo (is.length+1) x e₀ k 0 (Nat.zero_le _)).symm
  simp only [projTerm]
  rw [projCore_instN D T C us hcl hps his (D.length_projArgs T C us) hi,
    projArgs_instN D T C us hcl (i := i) (ps := ps.map (·.liftN (is.length+1)))
      (is := bvars 1 is.length) (e₀ := e₀) (k := k + is.length + 1)
      (by simpa using hps) (by simpa using his) (by omega) (by omega),
    hbv]
  simp only [List.map_map, Function.comp_def, e5, List.length_map]

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
