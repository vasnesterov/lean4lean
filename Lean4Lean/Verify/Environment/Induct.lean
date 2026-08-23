import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.Consistency

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
  /-- **Constructors are translated in the *staged* environment** — the one that already
  contains the block's type constants — exactly as `VInductDecl'.WF.ctors` is stated, and for
  the same reason.  See `no_trIndCtor_at_base` below: at the pre-block environment this clause
  is *unsatisfiable for every real block*, because a constructor's result is `I p args` and
  `TrExprS.const` demands `I` be declared. -/
  trCtors : ∀ env₁, env.addIndTypes D = some env₁ →
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → TrIndCtor env₁ Us D j c C

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
    {q : Nat} {c : Constructor} {C C' : VIndCtor} {env₁ env₁' : VEnv}
    (h : TrIndDecl env Us np types iu D) (h' : TrIndDecl env Us np types iu D')
    (hs : env.addIndTypes D = some env₁) (hs' : env.addIndTypes D' = some env₁')
    (ht : types[j]? = some t) (hT : D.types[j]? = some T) (hT' : D'.types[j]? = some T')
    (hc : t.ctors[q]? = some c) (hC : T.ctors[q]? = some C) (hC' : T'.ctors[q]? = some C') :
    C.name = C'.name :=
  ((h.trCtors env₁ hs j t T ht hT q c C hc hC).1).symm.trans
    (h'.trCtors env₁' hs' j t T' ht hT' q c C' hc hC').1

/-! ## Why the constructor clause is staged — and what attempting a witness found

The first draft of `TrIndDecl` stated its constructor clause at the *pre-block* environment.
Attempting the `Eq` witness is what showed that cannot work, and the reason is not special to
`Eq`: **a constructor's result is `I p args`**, so its stored type mentions the block's own type
constant, and `TrExprS.const` demands that constant be declared.  At the environment the block
is being added *to*, it is not.

So the first draft was unsatisfiable for **every** block with at least one constructor — not
merely hard to witness.  That is the failure mode the whole `Params` episode turned on: each
conjunct fine, the conjunction unsatisfiable at the environment where it is used.  The fix is
to mirror `VInductDecl'.WF.ctors`, which stages for exactly this reason; the spec had already
solved it and the refinement side had to be told.

The lemma below is that finding, kept live so the staging cannot be quietly undone. -/

/-- **The pre-block environment admits no translation of a constructor's stored type.**
Stated at `Eq.refl`'s actual type (`Verify/Soundness.lean`'s `eqDecl`), which is the shape
every constructor has: a result headed by the block's own type constant.  The target is left
free, so this says *no* `VExpr` translates it — not merely that the intended one does not. -/
theorem no_trExprS_eqRefl_at_base {env : VEnv} {Us : List Name} {Δ : VLCtx} {e' : VExpr}
    (hnone : env.constants ``Eq = none)
    (h : TrExprS env Us Δ (.forallE `α (.sort (.param `u_1))
      (.forallE `a (.bvar 0)
        (.app (.app (.app (.const ``Eq [.param `u_1]) (.bvar 1)) (.bvar 0)) (.bvar 0))
        .default) .implicit) e') : False := by
  cases h with | forallE _ _ _ h3 =>
  cases h3 with | forallE _ _ _ h4 =>
  cases h4 with | app _ _ h5 _ =>
  cases h5 with | app _ _ h6 _ =>
  cases h6 with | app _ _ h7 _ =>
  cases h7 with | const h8 _ _ =>
  rw [hnone] at h8
  exact absurd h8 nofun

/-- …hence no `TrIndCtor` at that environment, for the constructor the prelude actually
declares.  This is what forces `trCtors`' staging. -/
theorem no_trIndCtor_at_base {env : VEnv} {Us : List Name} {D : VInductDecl'} {j : Nat}
    {c : Constructor} {C : VIndCtor}
    (hc : c.type = .forallE `α (.sort (.param `u_1))
      (.forallE `a (.bvar 0)
        (.app (.app (.app (.const ``Eq [.param `u_1]) (.bvar 1)) (.bvar 0)) (.bvar 0))
        .default) .implicit)
    (hnone : env.constants ``Eq = none)
    (h : TrIndCtor env Us D j c C) : False :=
  no_trExprS_eqRefl_at_base hnone (hc ▸ h.2)

/-! ## The witness: `Eq`

A relation with no instance is the configuration that has produced every false statement found
on this project, and the determinism lemmas above are only a *proxy* for satisfiability — they
show the fields bite, not that anything satisfies them.  `no_trIndCtor_at_base` is likewise a
refutation of the *wrong* shape, which is a different artifact from a witness of the right one.

This is the witness: `Eq`, the first block of `stdPrelude`, against `Theory/Consistency.lean`'s
`eqIndDecl` — the same literal `VEnv.LeanWF` is stated over, and whose ι-rule is checked
against Lean's own stored recursor rule in `DeclExamples.lean`.

It is built at the **staged** environment, which is the only environment `TrIndDecl` is ever
evaluated at.  A witness at a fully-built environment would have gone through and proved
nothing, since `Eq` would already be declared. -/

def eqTypeE : Expr :=
  .forallE `α (.sort (.param `u_1))
    (.forallE `a (.bvar 0) (.forallE `b (.bvar 1) (.sort .zero) .default) .default) .implicit

theorem tr_eqType : TrExprS VEnv.empty [`u_1] [] eqTypeE
    (eqIndDecl.types.getD 0 default).type := by
  have hu : VLevel.WF 1 (.param 0) := by decide
  refine .forallE ⟨_, .sortDF hu hu (.refl _)⟩ ?_ (.sort rfl) ?_
  · exact ⟨_, .forallEDF (.bvar .zero) (.forallEDF (.bvar (.succ .zero))
      (.sortDF trivial trivial (.refl _)))⟩
  · refine .forallE ⟨_, .bvar .zero⟩ ?_ (.bvar rfl) ?_
    · exact ⟨_, .forallEDF (.bvar (.succ .zero)) (.sortDF trivial trivial (.refl _))⟩
    · refine .forallE ⟨_, .bvar (.succ .zero)⟩ ?_ (.bvar rfl) (.sort rfl)
      exact ⟨_, .sortDF trivial trivial (.refl _)⟩

def eqReflTypeE : Expr :=
  .forallE `α (.sort (.param `u_1))
    (.forallE `a (.bvar 0)
      (.app (.app (.app (.const ``Eq [.param `u_1]) (.bvar 1)) (.bvar 0)) (.bvar 0)) .default)
    .implicit

theorem eq_const_staged {env₁ : VEnv}
    (h : VEnv.empty.addIndTypes eqIndDecl = some env₁) :
    env₁.constants ``Eq = some ⟨1, (eqIndDecl.types.getD 0 default).type⟩ :=
  VEnv.addConstList_constants h (``Eq, ⟨1, (eqIndDecl.types.getD 0 default).type⟩) (by exact List.Mem.head _)

theorem tr_eqRefl {env₁ : VEnv} (h : VEnv.empty.addIndTypes eqIndDecl = some env₁) :
    TrExprS env₁ [`u_1] [] eqReflTypeE
      (((eqIndDecl.types.getD 0 default).ctors.getD 0 default).type eqIndDecl 0) := by
  have hu : VLevel.WF 1 (.param 0) := by decide
  have hEq := eq_const_staged h
  have hc : ∀ Γ, env₁.HasType 1 Γ (.const ``Eq [.param 0])
      (VExpr.mkPi [.sort (.param 0), .bvar 0, .bvar 1] (.sort .zero)) := fun Γ =>
    VEnv.HasType.const (Γ := Γ) (U := 1) hEq
      (by intro l hl; cases List.mem_singleton.1 hl; exact hu) rfl
  have hCty : (((eqIndDecl.types.getD 0 default).ctors.getD 0 default).type eqIndDecl 0)
      = VExpr.mkPi [.sort (.param 0), .bvar 0]
          (.app (.app (.app (.const ``Eq [.param 0]) (.bvar 1)) (.bvar 0)) (.bvar 0)) := rfl
  rw [hCty]
  refine .forallE ⟨_, .sortDF hu hu (.refl _)⟩ ?_ (.sort rfl) ?_
  · exact ⟨_, .forallEDF (.bvar .zero)
      (.appDF (.appDF (.appDF (hc _) (.bvar (.succ .zero))) (.bvar .zero)) (.bvar .zero))⟩
  · refine .forallE ⟨_, .bvar .zero⟩ ?_ (.bvar rfl) ?_
    · exact ⟨_, .appDF (.appDF (.appDF (hc _) (.bvar (.succ .zero))) (.bvar .zero))
        (.bvar .zero)⟩
    · exact .app (.appDF (.appDF (hc _) (.bvar (.succ .zero))) (.bvar .zero)) (.bvar .zero)
        (.app (.appDF (hc _) (.bvar (.succ .zero))) (.bvar .zero)
          (.app (hc _) (.bvar (.succ .zero)) (.const hEq rfl rfl) (.bvar rfl))
          (.bvar rfl))
        (.bvar rfl)

/-- `Eq`'s inductive type, transcribed from `Verify/Soundness.lean`'s `eqDecl`. -/
def eqIndTypeE : InductiveType :=
  { name := ``Eq, type := eqTypeE, ctors := [{ name := ``Eq.refl, type := eqReflTypeE }] }

/-- **`TrIndDecl` is satisfiable**, at the declaration `stdPrelude` actually contains and the
`VInductDecl'` `VEnv.LeanWF` is actually stated over. -/
theorem trIndDecl_eq : TrIndDecl VEnv.empty [`u_1] 2 [eqIndTypeE] false eqIndDecl where
  safe := rfl
  uvars := rfl
  np := rfl
  length := rfl
  trType := by
    intro j t T ht hT
    match j, ht, hT with
    | 0, ht, hT => cases ht; cases hT; exact ⟨rfl, tr_eqType⟩
  trCtorsLen := by
    intro j t T ht hT
    match j, ht, hT with
    | 0, ht, hT => cases ht; cases hT; rfl
  trCtors := by
    intro env₁ h j t T ht hT q c C hc hC
    match j, ht, hT with
    | 0, ht, hT =>
      cases ht; cases hT
      match q, hc, hC with
      | 0, hc, hC => cases hc; cases hC; exact ⟨rfl, tr_eqRefl h⟩

end Lean4Lean
