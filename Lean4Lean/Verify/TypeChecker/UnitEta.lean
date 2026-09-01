import Lean4Lean.Verify.Typing.ProjGen
import Lean4Lean.Verify.StructureBridge
import Lean4Lean.Verify.TypeChecker.IsDefEq

/-!
# Zero-field structure eta: the widened bridge, and the two-type firing witness

`docs/vacuity-ledger.md` row 99c: `isDefEqUnitLike.WF`'s residual `UnitLikeBridge`
(`Verify/TypeChecker/IsDefEq.lean`) is not merely unproved but **false** once `AddInduct` stops
being empty, because it concludes `VEnv.IsStructure I D T C`, whose `types` field is
`D.types = [T]`, while `isDefEqUnitLike` fires at a member of a **two-type mutual block**
(`FM1`, `Verify/TypeChecker/FiringWitness.lean`).  Row 99d rules that the repair is to *widen
the abstract premise*, not to narrow the checker.

**The abstract half of that widening moved to `Theory/`.**  `VEnv.UnitEta` — the zero-field eta
rule over `VEnv.IsStructureG` — and its four lemmas (`unitEta_rhs_eq`, `UnitEta.unitLike`,
`.unitLike_of_isStructure`, `.structEta_at_no_fields`, plus `VEnv.empty_unitEta` and
`VIndCtor.recFields_of_fields_nil`) are now in `Theory/Inductive/StructureEta.lean`, beside the
`VEnv.StructEta` they generalise, and `VEnv.IsStructureG` itself is in
`Theory/Inductive/Structure.lean` beside `VEnv.IsStructure` (ledger row 102d, decided
2026-09-01).  Nothing about the statements changed in the move.

**What is left here is what genuinely belongs under `Verify/`:**

* the **two-type firing witness** (`MutNonRec.decl2_WF` … `decl2Env_unitLike`), because it is
  built on `MutNonRec.decl2` from `Verify/StructureBridge.lean`;
* `UnitLikeBridgeG`, the widened bridge, and `UnitLikeBridge.toG`;
* `isDefEqUnitLike.WF_of_unitEta`.

The costing of the widening — `noRec` free at zero fields, `types` the whole content, and the
*discharge* burden it grows (surjective pairing at mutual blocks, ledger row 102a) — is recorded
where the rule now lives.
-/

namespace Lean4Lean

open VExpr

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

**Axioms.**  Every declaration above is `[propext, Classical.choice, Quot.sound]` —
**except** `isDefEqUnitLike.WF_of_unitEta`, which carries `sorryAx`.  (The two `Prop`-only ones,
`VIndCtor.recFields_of_fields_nil` and `VEnv.unitEta_rhs_eq`, are `[propext]`; they moved to
`Theory/Inductive/StructureEta.lean` on 2026-09-01 and their axiom sets are unchanged by the
move, re-measured there.)

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
`VEnv.StructEta` itself over `IsStructureG` **with** the projection terms.

**CORRECTION, 2026-09-01, and the correction is this paragraph's own.**  An earlier edition said
that repair needs the `Verify/Typing/ProjGen*` swap "because with fields present a recursor is
back in the statement and `MutNonRec.projCore_arity_wrong` bites again".  The first half is right
and the *reason* is wrong.  `projCore_arity_wrong` is inert against a rule stated over
`projTermG`, because `recArity_eq_projCoreG` is unconditional — machine-checked at a two-type
block *with a field*, `MutField.projCore_arity_wrong_here` and
`MutField.projCoreG_arity_right_here` (`Verify/TypeChecker/EtaStructG.lean`).  `VEnv.StructEtaG`
is that rule, and its whole assembly (`unitLike`, `congrSpine`, `congrProj`,
`congrProj_at_projAllG`) went through with **no arity side condition anywhere** and no new hole.
What actually blocks the positive-field path is two other things: `projTerm_hasType` has no
`IsStructureG` counterpart (remainder: `iota_law` at an arbitrary constructor, and
`realMinor_app` — `docs/handoff-projections.md` §0**.1, owned elsewhere), and — the one nothing
had recorded — **`TrProj` itself carries `VEnv.IsStructure`** (`TrProj.isStructure`), so the
bridge's `TrExprS (.proj …)` clause is no more satisfiable at a mutual block after the widening
than before it.  See `EtaStructG.lean`'s header for the three walls stated apart.

**One obligation this widening does grow, and it should be recorded rather than glossed.**
`UnitEta` is a strictly stronger assumption than `StructEta`'s zero-field instance, so whatever
eventually discharges it — the set model, as for `quotDefEq` — must validate surjective pairing
at members of *mutual* blocks, not only at singleton ones.  Nothing here shows that it does.
What is shown is that the strengthening is (i) consistent (`VEnv.empty_unitEta`), (ii) satisfiable
at the configuration that matters (`decl2Env_unitEta_premises`), and (iii) exactly what both
kernels' gates license, since neither reads `InductiveVal.all`.

`VEnv.StructEtaG` (`Verify/TypeChecker/EtaStructG.lean`) is the positive-field rule over the same
widened predicate, and it grows the obligation **by exactly the same one step and no more**:
surjective pairing at members of mutual blocks, now with the projections present.  It keeps
`C.recFields = []` as an explicit premise rather than inheriting `IsStructureG`'s omission of it —
see its docstring for the two reasons, one of which is that dropping it is not known to be *safe*
rather than merely strong.  `StructEtaG.toStructEta` is the polarity certificate. -/

end Lean4Lean
