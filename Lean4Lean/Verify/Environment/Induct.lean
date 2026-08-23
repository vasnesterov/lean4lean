import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Inductive.Decl

/-!
# `TrIndDecl`: an inductive declaration and the `VInductDecl'` that models it

`addDecl.WF`'s `inductDecl` branch has to turn a `Lean.Declaration.inductDecl` into a
`VInductDecl'`.  **That is not a function.**  `VInductDecl'` is a *decomposed* record carrying
data the kernel computes while checking, and `Theory/Inductive/Decl.lean`'s skeleton section
records which fields survive into the declaration and which do not:

* recoverable, because `checkConstructors` walks a constructor's pi-spine **without** `whnf`
  (F2): `VIndType.name`/`.type`, and `VIndCtor.params`/`.fields.type`/`.args`;
* not recoverable, because `checkInductiveTypes` `whnf`s at every step (F1):
  `VIndType.indices`, `D.params`, `D.lvl`, `VIndField.lvl`, `VIndField.recArg`, `D.isLE`.

So the translation is a relation.  This file is the *syntactic* half of it — names, counts, and
`TrExprS` on the two kinds of stored type.  It deliberately asserts nothing semantic.

## Why nothing semantic belongs here

`TrEnv'.induct` already carries `decl.WF env` alongside `AddInduct`.  Every fact about the
unrecoverable fields — that the indices exist and the stored type is definitionally the
canonical telescope (`VIndType.WF.canon`), that the recorded field sorts are sorts
(`VIndField.WF.hasType`), that `recArg` really describes the field (`VIndField.WF.pos`) — is a
clause of `VInductDecl'.WF`.  Restating any of it here would duplicate an obligation the
constructor already demands, and would make `TrIndDecl` harder to establish for no gain.

The division of labour is therefore: **`TrIndDecl` says the two records describe the same
syntax; `VInductDecl'.WF` says the `VInductDecl'` is a legitimate declaration.**

## Two carried restrictions

*Safe blocks only.*  `checkConstructors` calls `checkPositivity` under `if !isUnsafe then`, so
for an unsafe block there is no positivity check at all and `VIndField.WF.pos` has no witness.
Unsafe blocks are taken by `TrEnv'.ignore` instead.  The `safe` field below is what pins that.

*Non-nested only.*  `addInductive` discards the auxiliary environment and rebuilds, so a nested
block's result is not `VEnv.addInduct'` of *any* declaration.  This is a **limitation, not a
deferral**: `TrIndDecl` as stated does not describe nested blocks, and no strengthening of it
will.  `stdPrelude` contains none (`Eq`, `Iff`, `Nonempty` — single-type, safe, unnested), but
`kernel_sound` quantifies over arbitrary declaration lists, so they remain reachable in `ds`.

## Indexing

The block index `j` appears in the *target* of the constructor clause, because `VIndCtor.type`
is a computing `def` of `D` and `j` — which is exactly what makes the clause do work rather
than merely assert that some translation exists.  So the lists are related by index rather than
by `List.Forall₂`, matching how `VInductDecl'.WF.ctors` is stated.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-- The constructor half: the stored constructor type translates to the type `addInduct'`
will declare it at, `VIndCtor.type D j`.

`VIndCtor.skeleton` (`Theory/Inductive/Decl.lean`) is what makes this checkable — it inverts
`VIndCtor.type` on the nose, so the `VExpr` side of this clause is recoverable from the
declaration rather than guessed. -/
def TrIndCtor (env : VEnv) (Us : List Name) (D : VInductDecl') (j : Nat)
    (c : Constructor) (C : VIndCtor) : Prop :=
  c.name = C.name ∧ TrExprS env Us [] c.type (C.type D j)

/-- The type half: name and stored type.  `VIndType.type` is stored verbatim — F1 bites on
its *decomposition*, not on the type itself. -/
def TrIndType (env : VEnv) (Us : List Name) (t : InductiveType) (T : VIndType) : Prop :=
  t.name = T.name ∧ TrExprS env Us [] t.type T.type

/-- **The declaration translates.**  Names, counts, and `TrExprS` on the stored types — and
nothing else; see the module docstring. -/
structure TrIndDecl (env : VEnv) (Us : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (D : VInductDecl') : Prop where
  /-- Safe blocks only: positivity is skipped when `isUnsafe`. -/
  safe : isUnsafe = false
  uvars : Us.length = D.uvars
  np : nparams = D.np
  length : types.length = D.types.length
  trType : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T → TrIndType env Us t T
  trCtorsLen : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    t.ctors.length = T.ctors.length
  trCtors : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → TrIndCtor env Us D j c C

/-! ## The fields do work

A relation with no instance is the configuration that has produced every unsatisfiable class
found on this project, so the fields are checked against the triage rather than assumed sound:
what does it quantify over, what do the quantified relations leave free, and does anything make
the fields bite.

The answers here are: it quantifies over syntax only (`Expr` and `VExpr`, no judgements); the
quantified relation `TrExprS` leaves nothing free on its `VExpr` side, because that side is the
*computed* `VIndCtor.type D j` rather than an existential; and the lemmas below are the bite —
the declaration determines every field `TrIndDecl` mentions. -/

theorem TrIndDecl.uvars_eq {env Us np types iu} {D D' : VInductDecl'}
    (h : TrIndDecl env Us np types iu D) (h' : TrIndDecl env Us np types iu D') :
    D.uvars = D'.uvars := h.uvars ▸ h'.uvars

theorem TrIndDecl.np_eq {env Us np types iu} {D D' : VInductDecl'}
    (h : TrIndDecl env Us np types iu D) (h' : TrIndDecl env Us np types iu D') :
    D.np = D'.np := h.np ▸ h'.np

theorem TrIndDecl.types_length_eq {env Us np types iu} {D D' : VInductDecl'}
    (h : TrIndDecl env Us np types iu D) (h' : TrIndDecl env Us np types iu D') :
    D.types.length = D'.types.length := h.length ▸ h'.length

/-- The block's type names are determined by the declaration. -/
theorem TrIndDecl.name_eq {env Us np types iu} {D D' : VInductDecl'} {j : Nat} {t : InductiveType} {T T' : VIndType}
    (h : TrIndDecl env Us np types iu D) (h' : TrIndDecl env Us np types iu D')
    (ht : types[j]? = some t) (hT : D.types[j]? = some T) (hT' : D'.types[j]? = some T') :
    T.name = T'.name := ((h.trType j t T ht hT).1).symm.trans (h'.trType j t T' ht hT').1

/-- …and so are the constructors' names. -/
theorem TrIndDecl.ctor_name_eq {env Us np types iu} {D D' : VInductDecl'}
    {j : Nat} {t : InductiveType} {T T' : VIndType}
    {q : Nat} {c : Constructor} {C C' : VIndCtor}
    (h : TrIndDecl env Us np types iu D) (h' : TrIndDecl env Us np types iu D')
    (ht : types[j]? = some t) (hT : D.types[j]? = some T) (hT' : D'.types[j]? = some T')
    (hc : t.ctors[q]? = some c) (hC : T.ctors[q]? = some C) (hC' : T'.ctors[q]? = some C') :
    C.name = C'.name :=
  ((h.trCtors j t T ht hT q c C hc hC).1).symm.trans (h'.trCtors j t T' ht hT' q c C' hc hC').1

end Lean4Lean
