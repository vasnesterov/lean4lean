import Lean4Lean.Verify.Typing.ProjGen
import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Verify.TypeChecker.IsDefEq

/-!
# Zero-field structure eta, over the **widened** shape predicate

`docs/vacuity-ledger.md` row 99c: `isDefEqUnitLike.WF`'s residual `UnitLikeBridge`
(`Verify/TypeChecker/IsDefEq.lean`) is not merely unproved but **false** once `AddInduct` stops
being empty, because it concludes `VEnv.IsStructure I D T C`, whose `types` field is
`D.types = [T]`, while `isDefEqUnitLike` fires at a member of a **two-type mutual block**
(`FM1`, `Verify/TypeChecker/FiringWitness.lean`).  Row 99d rules that the repair is to *widen
the abstract premise*, not to narrow the checker.

This file is that widening.  `VEnv.UnitEta` is the zero-field eta rule stated over
`VEnv.IsStructureG` (`Verify/Typing/ProjGen.lean`), and `UnitLikeBridgeG` is the correspondingly
widened bridge; `isDefEqUnitLike.WF_of_unitEta` is `isDefEqUnitLike.WF` from those two, in place
of `VEnv.StructEta` and `UnitLikeBridge`.

## Why this file is in `Verify/` and not in `Theory/Inductive/StructureEta.lean`

**`VEnv.IsStructureG` is not reachable from `Theory/`.**  It is declared in
`Lean4Lean/Verify/Typing/ProjGen.lean`, and no file under `Lean4Lean/Theory/` imports anything
under `Lean4Lean/Verify/` (checked: zero hits for `import Lean4Lean.Verify` in `Theory/`).  So
stating `UnitEta` in `StructureEta.lean` would require either duplicating `IsStructureG` or
moving it across the layer boundary — a design decision that is not this file's to take.  Note
that `ProjGen.lean`'s *only* import is `Lean4Lean.Theory.Inductive.StructureClosed`, and
`IsStructureG` mentions nothing outside `Theory/`, so the move is available if wanted; it is
reported rather than performed.

## What the widening costs, exactly

`IsStructureG` drops two fields of `IsStructure`.  At **zero fields** one of them is free:

* `noRec : C.recFields = []` — `VIndCtor.recFields` is a `filterMap` over `C.fields`, so
  `C.fields = []` forces it (`VIndCtor.recFields_of_fields_nil` below).  The zero-field rule
  therefore loses nothing by dropping it.
* `types : D.types = [T]` → `D.types[j]? = some T`.  This is the whole content of the
  widening, and it is the field row 99c is about.

So `UnitEta` is `StructEta`'s zero-field instance plus *members of mutual blocks*, and nothing
else.  It is semantically harmless: at no indices and one constructor with no fields, `S ps` has
exactly one closed inhabitant `C.mk ps` whether or not `S`'s block has siblings — the sibling
types are simply other constants.  The reason `IsStructure.types` cannot be dropped **for the
projection path** does not apply here at all: that reason is `projCore`'s arity
(`MutNonRec.projCore_arity_wrong`, `Verify/StructureBridge.lean`), and at zero fields no
recursor is built into the statement — the η-expansion is `C.mk ps`
(`VInductDecl'.etaExpansion_of_no_fields`).

## Polarity

`StructEta`/`UnitEta` occur as **hypotheses** of the `.WF` obligations, i.e. in negative
position, so widening the class of blocks they quantify over *strengthens* the assumption.  That
is the right direction: it is what both kernels do.  C++'s `is_def_eq_unit_like`
(`~/lean4/src/kernel/type_checker.cpp`) delegates to `is_non_rec_structure`, which reads
`is_inductive`, one constructor, zero indices and not-recursive, and **never**
`InductiveVal.all`.  The price of a stronger assumption is that it must still be *consistent*
and its consumers must still be *satisfiable*; both are discharged below
(`VEnv.empty_unitEta`, and the two-type witness section).
-/

namespace Lean4Lean

open VExpr

/-- **`noRec` is free at zero fields.**  `VIndCtor.recFields` is a `filterMap` over the field
list, so a constructor with no fields has no recursive fields.  This is why dropping
`VEnv.IsStructure.noRec` costs nothing in the zero-field rule. -/
theorem VIndCtor.recFields_of_fields_nil {C : VIndCtor} (h : C.fields = []) :
    C.recFields = [] := by simp [VIndCtor.recFields, h]

/-- **Zero-field structure eta, over `VEnv.IsStructureG`.**

`env.UnitEta` says: whenever `env` declares `S` as the `j`-th type of a block, with no indices
and exactly one constructor `C`, and `C` has no fields, then every inhabitant of `S ps` is
definitionally equal to the closed term `C.mk ps`.

Differences from `VEnv.StructEta` (`Theory/Inductive/StructureEta.lean`), all forced by the
zero-field specialisation:

* `IsStructureG` in place of `IsStructure` — the point of the file;
* `C.fields = []` is a premise, and consequently the right-hand side is spelled out as
  `(const C.name us).mkApp ps` rather than `D.etaExpansion T C us ps e`.  The two agree
  (`unitEta_rhs_eq`), and the explicit spelling is what makes it visible that **no `projTerm`,
  and hence no recursor, occurs anywhere in the statement**;
* the F17 clause (`D.isLE = true ∨ ∀ k < C.fields.length, …`) is dropped, because at zero fields
  its right disjunct is vacuously true — there is no projection whose typing could fail.

Every binder is pinned by a hypothesis — `S`, `D`, `j`, `T`, `C` by `IsStructureG`, `us` and `ps`
by the length and `HasArgs` clauses, `e` by the `HasType` clause — so the conclusion mentions
nothing the premises leave free. -/
def VEnv.UnitEta (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType}
    {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr},
    env.IsStructureG S D j T C →
    T.indices = [] →
    C.fields = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF U) →
    ps.length = D.np →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasType U Γ e ((VExpr.const S us).mkApp ps) →
    env.IsDefEq U Γ e ((VExpr.const C.name us).mkApp ps) ((VExpr.const S us).mkApp ps)

namespace VEnv

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
  {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e e₁ e₂ : VExpr}

/-- The right-hand side of `UnitEta` **is** `VInductDecl'.etaExpansion`, at zero fields.  So
`UnitEta` really is the zero-field instance of the same rule `StructEta` states, and not a
different rule that happens to look similar. -/
theorem unitEta_rhs_eq (hnf : C.fields = []) :
    D.etaExpansion T C us ps e = (VExpr.const C.name us).mkApp ps :=
  D.etaExpansion_of_no_fields T C us hnf

namespace UnitEta

/-- **What `isDefEqUnitLike` needs.**  At zero fields the right-hand side is the same closed
term `C.mk ps` for every inhabitant, so any two inhabitants of `S ps` are definitionally equal.

This is `VEnv.StructEta.unitLike`'s proof, verbatim modulo the widened predicate and the
already-specialised right-hand side (the `rw [etaExpansion_of_no_fields]` step is discharged in
the statement of `UnitEta` itself). -/
theorem unitLike (H : env.UnitEta) (hS : env.IsStructureG S D j T C)
    (hidx : T.indices = []) (hnf : C.fields = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he₁ : env.HasType U Γ e₁ ((VExpr.const S us).mkApp ps))
    (he₂ : env.HasType U Γ e₂ ((VExpr.const S us).mkApp ps)) :
    env.IsDefEq U Γ e₁ e₂ ((VExpr.const S us).mkApp ps) :=
  (H hS hidx hnf hus husWF hps hpsA he₁).trans
    (H hS hidx hnf hus husWF hps hpsA he₂).symm

/-- **Nothing is lost by the swap: every `IsStructure` instance is still covered.**

`VEnv.IsStructure.toG` (`Verify/Typing/ProjGen.lean`) embeds the narrow predicate at `j = 0`, so
`UnitEta` implies `StructEta.unitLike`'s conclusion at every instance `StructEta.unitLike` has
one — this is the negative-position check made concrete rather than argued. -/
theorem unitLike_of_isStructure (H : env.UnitEta) (hS : env.IsStructure S D T C)
    (hidx : T.indices = []) (hnf : C.fields = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he₁ : env.HasType U Γ e₁ ((VExpr.const S us).mkApp ps))
    (he₂ : env.HasType U Γ e₂ ((VExpr.const S us).mkApp ps)) :
    env.IsDefEq U Γ e₁ e₂ ((VExpr.const S us).mkApp ps) :=
  H.unitLike hS.toG hidx hnf hus husWF hps hpsA he₁ he₂

/-- …and the same for `StructEta`'s own conclusion, spelled with `etaExpansion`: at zero fields
`UnitEta` delivers exactly what `VEnv.StructEta` delivers.  (The F17 clause of `StructEta` is
not needed as an input here — at zero fields it is free.) -/
theorem structEta_at_no_fields (H : env.UnitEta) (hS : env.IsStructure S D T C)
    (hidx : T.indices = []) (hnf : C.fields = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps)) :
    env.IsDefEq U Γ e (D.etaExpansion T C us ps e) ((VExpr.const S us).mkApp ps) := by
  rw [unitEta_rhs_eq (D := D) (T := T) (us := us) (ps := ps) (e := e) hnf]
  exact H hS.toG hidx hnf hus husWF hps hpsA he

end UnitEta

/-- `UnitEta` is consistent: the empty environment declares no block, so every instance is
vacuous there.  Read together with the two-type witness below, which shows the premises are
**not** vacuous in general — and, unlike anything available for `StructEta`, are satisfiable at
exactly the configuration `UnitLikeBridge`'s conclusion cannot describe. -/
theorem empty_unitEta : VEnv.empty.UnitEta := by
  intro U Γ S D j T C us ps e hS _ _ _ _ _ _ _
  obtain ⟨env₀, env₁, _, hadd, hle⟩ := hS.decl
  have h := hle.constants
    (VEnv.addInduct'_types (T := T) hadd (List.getElem?_eq_some_iff.1 hS.types |>.2 ▸ (by
      exact List.getElem_mem _)))
  simp [VEnv.empty] at h

end VEnv


/-! ## The firing instance: a **two-type mutual block**

This is the section that makes the widening more than bookkeeping.  `UnitLikeBridge`'s
conclusion cannot be witnessed at a member of a two-type block, and `isDefEqUnitLike` fires at
exactly such a member (`FM1`, `Verify/TypeChecker/FiringWitness.lean`).  So the acceptance
criterion for `UnitEta` is not "some environment satisfies it" — `empty_unitEta` gives that and
it is worthless on its own — but "**its premises are jointly satisfiable at a member of a
two-type mutual block**".  They are.

The block is `MutNonRec.decl2` (`Verify/StructureBridge.lean`), the abstract form of the real
declaration `mutual inductive A | mk : A; inductive B | mk : B end` whose `isNonRecStructure`
verdict is checked there by `#eval`.  That file declares `decl2` with the note "no `WF` claim is
made and none is needed"; the `WF` claim *is* needed here, and `decl2_WF` supplies it.

`decl2` is in `Type`, not `Prop` (`lvl = .succ .zero`), which matters: the `Prop` half of
`isDefEqUnitLike.WF` is already discharged without any eta rule
(`isDefEqUnitLike.WF_prop`), so a `Prop` witness would exercise nothing.
-/

namespace MutNonRec

/-- `decl2`'s first type, named. -/
def aTy : VIndType :=
  { name := `MutNonRec.A, type := .sort (.succ .zero), indices := [],
    ctors := [{ name := `MutNonRec.A.mk, params := [], fields := [], args := [] }] }

/-- `decl2`'s second type, named. -/
def bTy : VIndType :=
  { name := `MutNonRec.B, type := .sort (.succ .zero), indices := [],
    ctors := [{ name := `MutNonRec.B.mk, params := [], fields := [], args := [] }] }

/-- `A`'s only constructor: **zero fields**, which is `isDefEqUnitLike`'s gate. -/
def aCtor : VIndCtor := { name := `MutNonRec.A.mk, params := [], fields := [], args := [] }

/-- `B`'s only constructor. -/
def bCtor : VIndCtor := { name := `MutNonRec.B.mk, params := [], fields := [], args := [] }

theorem decl2_types : decl2.types = [aTy, bTy] := rfl

/-- **The block is well formed.**  `Verify/StructureBridge.lean` declares `decl2` for its shape
alone and explicitly makes no `WF` claim; `VEnv.IsStructureG.decl` needs one, so here it is.

Nothing in it is delicate: no parameters, no indices, no fields, `isLE = false` (so the `LECond`
clause is vacuous), and each constructor's result type is the bare block constant, supplied by
`addConstList_constants` from the staged environment. -/
theorem decl2_WF : decl2.WF .empty where
  types_ne := by simp [decl2]
  params := trivial
  types := by
    intro T hT
    simp [decl2] at hT
    rcases hT with rfl | rfl <;>
      exact { indices := trivial
              isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
              canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    have hA : env₁.constants `MutNonRec.A = some ⟨0, .sort (.succ .zero)⟩ :=
      VEnv.addConstList_constants he (`MutNonRec.A, ⟨0, .sort (.succ .zero)⟩)
        (by simp [VInductDecl'.typeConsts, decl2])
    have hB : env₁.constants `MutNonRec.B = some ⟨0, .sort (.succ .zero)⟩ :=
      VEnv.addConstList_constants he (`MutNonRec.B, ⟨0, .sort (.succ .zero)⟩)
        (by simp [VInductDecl'.typeConsts, decl2])
    match j, hT with
    | 0, hT =>
      simp [decl2] at hT; subst hT; simp at hC; subst hC
      exact { params_len := rfl, params_eq := .zero, fields := nofun,
              args_len := rfl, args_fresh := by simp, args_ty := .nil,
              result := .constDF hA nofun nofun rfl .nil }
    | 1, hT =>
      simp [decl2] at hT; subst hT; simp at hC; subst hC
      exact { params_len := rfl, params_eq := .zero, fields := nofun,
              args_len := rfl, args_fresh := by simp, args_ty := .nil,
              result := .constDF hB nofun nofun rfl .nil }
  isLE := by simp [decl2]

theorem decl2Env_eq : ∃ e, VEnv.empty.addInduct' decl2 = some e := ⟨_, rfl⟩

noncomputable def decl2Env : VEnv := decl2Env_eq.choose

/-- **`IsStructureG` at the first member of the two-type block.**  This is the judgement
`UnitLikeBridge` would have to produce and cannot. -/
theorem decl2Env_IsStructureG : decl2Env.IsStructureG `MutNonRec.A decl2 0 aTy aCtor where
  types := rfl
  name := rfl
  ctors := rfl
  decl := ⟨.empty, decl2Env, decl2_WF, decl2Env_eq.choose_spec, VEnv.LE.rfl⟩

/-- …and at the second, to make plain that the index `j` is doing work rather than being
carried. -/
theorem decl2Env_IsStructureG_1 : decl2Env.IsStructureG `MutNonRec.B decl2 1 bTy bCtor where
  types := rfl
  name := rfl
  ctors := rfl
  decl := ⟨.empty, decl2Env, decl2_WF, decl2Env_eq.choose_spec, VEnv.LE.rfl⟩

/-- **`VEnv.IsStructure` is unavailable at this block, for any `S`, `T`, `C`** — the `types`
field alone refutes it, `decl2` having two types.  Cited rather than re-derived: the
`∀ T, decl2.types ≠ [T]` conjunct is `MutNonRec.indShapeOf_not_singleton`'s last.

Read the quantifier carefully: this says *this* `D` is not admitted by `IsStructure`, which is
what makes `IsStructureG` necessary for stating the rule at this block.  It does **not** say no
other `D` witnesses `IsStructure` for the *name* `MutNonRec.A` — that is ledger G4 (no
uniqueness of blocks per name), and it is a pre-existing gap shared by `IsStructure` and
`IsStructureG` alike, unchanged by this file. -/
theorem decl2_not_isStructure {S T C} : ¬ decl2Env.IsStructure S decl2 T C :=
  fun h => indShapeOf_not_singleton.2.2.2.2 _ h.types

theorem decl2Env_A : decl2Env.constants `MutNonRec.A = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addInduct'_types (T := aTy) decl2Env_eq.choose_spec (by simp [decl2_types])

theorem decl2Env_Amk : decl2Env.constants `MutNonRec.A.mk = some ⟨0, .const `MutNonRec.A []⟩ :=
  VEnv.addInduct'_ctors (C := aCtor) (j := 0) decl2Env_eq.choose_spec
    (by simp [VInductDecl'.ctorsAll, decl2_types, aTy, aCtor, bTy])

/-- The context `(x : A)`. -/
def aCtx : List VExpr := [.const `MutNonRec.A []]

/-- **Every premise of `VEnv.UnitEta`, satisfied at once, at a member of a two-type mutual
block in `Type`.**  Compare `bazEnv_structEta_premises` (`Theory/Inductive/StructureEta.lean`),
which is the same audit for `StructEta` at a *singleton* block. -/
theorem decl2Env_unitEta_premises :
    decl2Env.IsStructureG `MutNonRec.A decl2 0 aTy aCtor ∧
    aTy.indices = [] ∧
    aCtor.fields = [] ∧
    ([] : List VLevel).length = decl2.uvars ∧
    (∀ l ∈ ([] : List VLevel), l.WF 0) ∧
    ([] : List VExpr).length = decl2.np ∧
    decl2Env.HasArgs 0 aCtx (decl2.params.map (VExpr.instL [])) [] ∧
    decl2Env.HasType 0 aCtx (.bvar 0) ((VExpr.const `MutNonRec.A []).mkApp []) ∧
    decl2.types.length = 2 :=
  ⟨decl2Env_IsStructureG, rfl, rfl, rfl, nofun, rfl, .nil, .bvar (.zero ..), rfl⟩

/-- The rule's right-hand side is well typed at the witness — so the instance is not satisfied
by accident of an ill-typed conclusion.  (`VEnv.IsDefEq` implies both sides are well typed, so a
rule whose right-hand side were ill typed would be *false*, not merely useless.) -/
theorem decl2Env_Amk_hasType :
    decl2Env.HasType 0 aCtx ((VExpr.const `MutNonRec.A.mk []).mkApp [])
      ((VExpr.const `MutNonRec.A []).mkApp []) :=
  .constDF decl2Env_Amk nofun nofun rfl .nil

/-- **The rule, fired at that witness**: `x ≡ A.mk` for `x : A`, where `A` is a member of a
two-type mutual block.  This is the instance `UnitLikeBridge` cannot reach. -/
theorem decl2Env_unitEta (H : decl2Env.UnitEta) :
    decl2Env.IsDefEq 0 aCtx (.bvar 0) (.const `MutNonRec.A.mk []) (.const `MutNonRec.A []) :=
  H (us := []) (ps := []) decl2Env_IsStructureG rfl rfl rfl nofun rfl .nil
    (.bvar (.zero ..))

/-- …and the consequence `isDefEqUnitLike` actually reports: any two inhabitants of `A` are
definitionally equal.  Stated in the context `(x : A) (y : A)`. -/
theorem decl2Env_unitLike (H : decl2Env.UnitEta) :
    decl2Env.IsDefEq 0 (.const `MutNonRec.A [] :: aCtx) (.bvar 0) (.bvar 1)
      (.const `MutNonRec.A []) :=
  H.unitLike (us := []) (ps := []) decl2Env_IsStructureG rfl rfl rfl nofun rfl .nil
    (.bvar (.zero ..)) (.bvar (.succ (.zero ..)))

end MutNonRec

/-! ## The widened bridge, and `isDefEqUnitLike.WF` over it -/

namespace TypeChecker.Inner
open Lean hiding Environment Exception

variable {e₁ e₂ : Expr} {e₁' e₂' : VExpr}

/-- **`UnitLikeBridge`, widened to `IsStructureG`.**

Field for field identical to `UnitLikeBridge` (`Verify/TypeChecker/IsDefEq.lean`) except that the
existential now carries a block index `j` and concludes `c.venv.IsStructureG I D j T C` in place
of `c.venv.IsStructure I D T C`.

That is the whole repair for ledger row 99c.  `UnitLikeBridge`'s conclusion is unsatisfiable at a
member of a two-type mutual block, and `isDefEqUnitLike` fires at one; `UnitLikeBridgeG`'s is
satisfiable there (`MutNonRec.decl2Env_IsStructureG`, and `MutNonRec.decl2_not_isStructure` for
the corresponding negative).

Polarity: this is a **hypothesis** of `isDefEqUnitLike.WF_of_unitEta`, so weakening its
conclusion *weakens the hypothesis* and strengthens that theorem.  `UnitLikeBridge.toG` below is
the machine-checked form of that claim — anyone who can prove the old bridge gets the new one
for free, so no work already done on the bridge is invalidated. -/
def UnitLikeBridgeG (c : VContext) : Prop :=
  ∀ {tType : Expr} {tType' : VExpr} {I cn : Name} {ls : List Level}
    {v : InductiveVal} {w : ConstructorVal},
    c.TrExprS tType tType' → tType.getAppFn = .const I ls →
    c.env.find? I = some (.inductInfo v) →
    v.isRec = false → v.ctors = [cn] → v.numIndices = 0 →
    c.env.find? cn = some (.ctorInfo w) → w.numFields = 0 →
    ∃ D j T C us ps, tType' = (VExpr.const I us).mkApp ps ∧
      c.venv.IsStructureG I D j T C ∧ T.indices = [] ∧ C.fields = [] ∧
      us.length = D.uvars ∧ (∀ l ∈ us, l.WF c.lparams.length) ∧ ps.length = D.np ∧
      c.venv.HasArgs c.lparams.length c.vlctx.toCtx (D.params.map (VExpr.instL us)) ps

/-- The old bridge implies the new one, at `j = 0`, by `VEnv.IsStructure.toG`.  So
`UnitLikeBridgeG` is a *weaker* obligation than `UnitLikeBridge` and nothing that would have
proved the latter is wasted. -/
theorem UnitLikeBridge.toG {c : VContext} (h : UnitLikeBridge c) : UnitLikeBridgeG c := by
  intro _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨D, T, C, us, ps, hEq, hIS, rest⟩ := h h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨D, 0, T, C, us, ps, hEq, hIS.toG, rest⟩

/-- **`isDefEqUnitLike.WF` from the widened pair.**

`isDefEqUnitLike.WF_of_structEta` (`Verify/TypeChecker/IsDefEq.lean`) is the same statement from
`c.venv.StructEta` and `UnitLikeBridge c`; this is it from `c.venv.UnitEta` and
`UnitLikeBridgeG c`.  The proof is that one's, verbatim, with the widened destructuring and
`VEnv.UnitEta.unitLike` in place of `VEnv.StructEta.unitLike`.

**Why this is the version to use.**  `UnitLikeBridge` is *false* once `AddInduct` is non-empty
(ledger row 99c), so `WF_of_structEta` reduces `isDefEqUnitLike.WF` to a pair one of whose
members cannot be proved.  `UnitLikeBridgeG` is not known false, and is satisfiable at exactly
the configuration that refutes `UnitLikeBridge` (`MutNonRec.decl2Env_unitEta_premises`).  The
price is the stronger eta assumption `UnitEta` — the trade ledger row 99d approves, and the one
both kernels' gates actually license.

Like `WF_of_structEta` this proof **enters** the `.inductInfo`/`.ctorInfo` arm rather than
killing it with `TrEnv.not_inductInfo`, so it survives the `AddInduct` flip verbatim.  It
inherits `inferType.WF`'s four holes (`weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`,
`NormalEq.descend`) and adds none — see `isDefEqUnitLike.WF_prop`'s docstring for why the
alignment is load-bearing whenever the conclusion mentions `e₁'`. -/
theorem isDefEqUnitLike.WF_of_unitEta {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hSE : c.venv.UnitEta) (hbr : UnitLikeBridgeG c) :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold isDefEqUnitLike
  refine (inferType.WF he₁).bind fun ty _ _ ⟨ty', _, _, hty, hT⟩ => ?_
  refine (whnf.WF hty).bind fun tType _ _ ⟨_, _, htT, hdefeq⟩ => ?_
  split <;> [skip; exact .pure nofun]
  rename_i I ls heq
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
  split <;> [skip; exact .pure nofun]
  refine (M.WF.liftExcept hget).lift.bind fun ci₂ _ _ hcc => ?_
  split <;> [skip; exact .pure nofun]
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, _, _, _, hS⟩ => ?_
  refine (isDefEqCore.WF htT ‹_›).mono fun _ _ _ h hb => ?_
  obtain ⟨D, j, T, C, us, ps, hEq, hIS, hidx, hnf, hus, huswf, hps, hpsA⟩ :=
    hbr htT heq hci rfl rfl rfl hcc rfl
  subst hEq
  exact ⟨_, hSE.unitLike hIS hidx hnf hus huswf hps hpsA
    (hT.defeqU_r c.Ewf c.Δwf hdefeq.symm) (hS.defeqU_r c.Ewf c.Δwf (h hb).symm)⟩

end TypeChecker.Inner

/-! ## Audit

**Axioms.**  Every declaration above is `[propext, Classical.choice, Quot.sound]` — the two
`Prop`-only ones (`VIndCtor.recFields_of_fields_nil`, `VEnv.unitEta_rhs_eq`) are `[propext]` —
**except** `isDefEqUnitLike.WF_of_unitEta`, which carries `sorryAx`.

**And that `sorryAx` is entirely borrowed, none of it new.**  Measured hole cones (transitive
`getUsedConstantsAsSet` sweep, filtering to declarations whose *value* mentions `sorryAx`):

| seed | cone | holes |
|---|---|---|
| `isDefEqUnitLike.WF_of_structEta` | 10920 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend` |
| `isDefEqUnitLike.WF_of_unitEta` | 10917 | **the same four** |
| `VEnv.StructEta.unitLike` | 764 | none |
| `VEnv.UnitEta.unitLike` | 603 | none |
| `MutNonRec.decl2_WF` | 3676 | none |
| `MutNonRec.decl2Env_unitEta_premises` | 3757 | none |
| `UnitLikeBridge.toG` | 2611 | none |

All four holes enter through `inferType.WF`'s single appeal to `TrExprS.uniq`, exactly as they do
in `WF_of_structEta`; the swap *removes* three constants from the cone (the `etaExpansion`/
`projAll` layer that the zero-field right-hand side no longer mentions) and adds no hole.

**Firing status, per instrument 7 of `docs/vacuity-ledger.md` §0 — stated per declaration,
because it is not uniform.**

* *Fires today, non-vacuously:* `MutNonRec.decl2Env_unitEta` and `MutNonRec.decl2Env_unitLike`.
  Every premise of `UnitEta` is discharged outright at `decl2Env` — `IsStructureG`, both `rfl`
  side conditions, the level and parameter lengths, the `HasArgs`, and the `HasType` — so the only
  hypothesis left is `H : decl2Env.UnitEta` itself, and the conclusion is a *specific*
  `IsDefEq` between two syntactically distinct terms.  `decl2Env_unitEta_premises` is that audit
  as a single conjunction, and its last conjunct (`decl2.types.length = 2`) is the point: the
  instance is at a **two-type mutual block in `Type`**, which is both what `isDefEqUnitLike`
  actually fires at and what `UnitLikeBridge`'s conclusion cannot describe.
* *Fires today:* `VEnv.UnitEta.unitLike_of_isStructure` and `.structEta_at_no_fields` — at
  `bazEnv`'s zero-field analogue they would, and unconditionally they are applications of
  `unitLike`, so they carry no unsatisfiable hypothesis of their own.
* **Does *not* fire today, and this is structural:** `isDefEqUnitLike.WF_of_unitEta` and
  `UnitLikeBridge.toG`.  The first takes `c.TrExprS e₁ e₁'`, which carries `AddInduct`'s
  emptiness in, so its `.inductInfo` arm is unreachable *in the proof layer* until the flip —
  the same status as `WF_of_structEta`, and the reason it is worth having is that it does not
  *use* the emptiness (`TrEnv.not_inductInfo` appears nowhere in it), so it survives the flip
  verbatim.  The second takes `UnitLikeBridge c`, which is unproved today and false after the
  flip; it is here as the polarity certificate (old obligation ⟹ new obligation), not as a
  usable step.

**What this file does *not* repair.**  Only the zero-field path.  `tryEtaStructCore.WF`'s
residual `EtaStructSpine` (`Verify/TypeChecker/IsDefEq.lean`) has the same `IsStructure.types`
defect (ledger row 99c, "Same for `EtaStructSpine`"), and repairing *it* means restating
`VEnv.StructEta` itself over `IsStructureG` **with** the projection terms — which does need
`projTermG` and the `Verify/Typing/ProjGen*` swap (`docs/handoff-projections.md` §0.5), because
with fields present a recursor is back in the statement and `MutNonRec.projCore_arity_wrong`
bites again.  That is why the zero-field path is the cheap one and why it was taken first.

**One obligation this widening does grow, and it should be recorded rather than glossed.**
`UnitEta` is a strictly stronger assumption than `StructEta`'s zero-field instance, so whatever
eventually discharges it — the set model, as for `quotDefEq` — must validate surjective pairing
at members of *mutual* blocks, not only at singleton ones.  Nothing here shows that it does.
What is shown is that the strengthening is (i) consistent (`VEnv.empty_unitEta`), (ii) satisfiable
at the configuration that matters (`decl2Env_unitEta_premises`), and (iii) exactly what both
kernels' gates license, since neither reads `InductiveVal.all`. -/

end Lean4Lean
