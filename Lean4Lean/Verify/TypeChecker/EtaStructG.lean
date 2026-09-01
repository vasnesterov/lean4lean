import Lean4Lean.Verify.Typing.ProjGen
import Lean4Lean.Verify.TypeChecker.IsDefEq

/-!
# Positive-field structure eta over the **widened** shape predicate, and where it stops

`Verify/TypeChecker/UnitEta.lean` repaired the **zero-field** half of `docs/vacuity-ledger.md`
row 99c: `VEnv.UnitEta` (`Theory/Inductive/StructureEta.lean`) is the eta rule over
`VEnv.IsStructureG`, satisfiable at a member of a two-type mutual block, which is what the
checker actually fires at.  Row 102c records that the **positive-field** half —
`tryEtaStructCore.WF`'s residual `EtaStructSpine` (`Verify/TypeChecker/IsDefEq.lean`) — has the
same `IsStructure.types` defect and is harder, because with fields present a recursor is back in
the statement.

This file is that half, taken as far as it goes, with the wall named and machine-checked.

## The three walls, separated — because the brief's single one is not the operative one

Row 102c and `UnitEta.lean`'s audit both say the blocker is `MutNonRec.projCore_arity_wrong`.
**That is one wall of three, and it is the one that is already down.**  Stated apart:

1. **`projCore`'s arity.**  Real, and it is exactly why the rule must not be widened *keeping
   `projTerm`*: `MutNonRec.projCore_arity_wrong` (`Verify/StructureBridge.lean`) exhibits a
   two-type block at which `projCore`'s spine is short by `D.nm + D.nmin - 2`.  But
   `VInductDecl'.projTermG` (`Verify/Typing/ProjGen.lean`) pads both blocks, and
   `recArity_eq_projCoreG` is **unconditional**, so `projCore_arity_wrong` is *inert* against a
   rule stated over `projTermG` (`MutNonRec.projCoreG_arity_right'`).  `VEnv.StructEtaG` below
   is stated over `projTermG`, and every piece of the assembly — `unitLike`, `congrSpine`,
   `congrProj`, the round-trip check — goes through **verbatim**, with no arity side condition
   anywhere.  So wall 1 does **not** block the repair; reporting it as the blocker would send
   the next reader at a problem that was solved eight rounds ago.
2. **`projTermG`'s typing.**  This is the operative wall for the abstract rule.
   `tryEtaStructCore.WF_of_structEta` *derives* its `hprojty` premise from the bridge, by
   `projTerm_hasType` (`Verify/Typing/Lemmas.lean`) — and that lemma is stated at
   `VEnv.IsStructure` and uses `H.nm_eq`, `H.nmin_eq` and `H.noRec`, through `projMinor_hasType`
   → `iota_law` (`Verify/Typing/Lemmas.lean`, at its `iota_law hord hI H h3 h7 H.nm_eq H.nmin_eq
   H.noRec` call).  There is **no** `projTermG_hasType`; `docs/handoff-projections.md` §0**.1
   reports the chain down to two open lemmas, `iota_law` at an arbitrary constructor of an
   arbitrary block and `realMinor_app`, both owned elsewhere.  So this file **cannot** derive
   the projections' typing at a widened block, and `EtaStructSpineG` carries it as a conjunct
   (`ProjHasTypeG`, `Verify/Typing/ProjGenMotive.lean`) instead — see that predicate's docstring
   for why that is honest bookkeeping rather than a hidden assumption.
3. **`TrProj`.**  And this is the one nothing had recorded, and it is bigger than either of the
   others.  `EtaStructSpine`'s per-iteration clause is `c.TrExprS (.proj I k t) (…)`, and
   `TrExprS`'s `.proj` constructor goes through `TrProj` (`Verify/Typing/Expr.lean`), whose
   *only* constructor `TrProj.mk` carries `env.IsStructure S D T C` and produces
   `D.projTerm T C us ps ιs i e`.  Both halves bite: at a two-type block `IsStructure` is
   unavailable (`MutNonRec.decl2_not_isStructure`), so **no `.proj` node can be translated at
   all**, and the abstract term `TrProj` produces is `projTerm`, not `projTermG`.  The clause is
   in *positive* position inside the bridge, so this is not a weakening that costs nothing: the
   widened bridge is **as unsatisfiable at a two-type block as the narrow one** until `TrProj`
   itself is widened.  `TrProj` is not this file's to change, and widening it touches
   `TrExprS`, `TrProj.wf`, `TrProj.uniq`, `TrProj.weak'_inv` and `inferProj.WF`.

**Correction, 2026-09-01 (ledger row 107b): walls 2 and 3 are NOT separable — wall 2 gates
wall 3.**  The list above presents them as three independent obstructions.  That is wrong about
the last two, and the error would misdirect anyone who tried to take wall 3 first.
`TrExprS.wf`'s `proj` case is `h2.wf …`, so **`TrProj.wf` must cover every `TrProj`
derivation**; hence any widening of `TrProj` that admits a derivation at a member of a mutual
block makes `TrProj.wf` *assert* that `projTermG … j` is well typed — and that assertion **is**
wall 2, `projTermG_hasType`.  So `iota_law` at an arbitrary constructor of an arbitrary block
and `realMinor_app` are **prerequisites** of the `TrProj` widening, not parallel to it, and wall
2 gates `TrExprS.wf`'s 158 transitive users rather than one conjunct of this file's bridge.  The
one route that relocates rather than removes it is ledger row 107d's option (d) — carry the
target's typing as an extra field of `TrProj.mk` — which moves wall 2 onto `inferProj.WF`.

**Consequence, stated plainly.**  The abstract rule generalises cleanly and is delivered here.
The *bridge* does not become satisfiable at a mutual block by being restated — unlike
`UnitLikeBridgeG`, which does, because `isDefEqUnitLike` never builds a `.proj` node and so
never touches `TrProj`.  That asymmetry between the zero-field and positive-field cases is the
finding, and it is not the asymmetry row 102c predicted.

## The discharge cost, which is one field and not two

`docs/vacuity-ledger.md` row 102a records that `VEnv.UnitEta`'s widening already obliges whatever
discharges it — the set model, as for `quotDefEq` — to validate surjective pairing at members of
**mutual** blocks, not only singleton ones.  `VEnv.StructEtaG` inherits exactly that obligation
and adds nothing to it: it keeps `C.recFields = []` as an explicit premise (see its docstring), so
the only field of `VEnv.IsStructure` it actually relaxes is `types`, the same one `UnitEta`
relaxes.  What it does do is make the obligation *bigger in extent* rather than in kind — the
right-hand side now contains `C.fields.length` recursor applications instead of none, so the model
must validate the pairing equation, not merely the uniqueness of a nullary constructor.  Nothing
here shows that it does.

Consistency and non-degenerate satisfiability are shown: `VEnv.empty_structEtaG`, and
`MutField.declEnv_structEtaG_premises` — every premise discharged at once at a member of a
**two-type mutual block with a field**, in `Type`, at block index `1`.
-/

namespace Lean4Lean

open VExpr

namespace VInductDecl'

variable (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)

/-- `[projG 0 e, …, projG (n-1) e]` at block index `j`: `VInductDecl'.projAll`
(`Theory/Inductive/StructureEta.lean`) with `projTerm` replaced by `projTermG`.

The index list stays `[]` for the same reason it does there: structure eta applies only to a
block with no indices. -/
def projAllG (ps : List VExpr) (j : Nat) (e : VExpr) : List VExpr :=
  (List.range C.fields.length).map fun i => D.projTermG T C us ps [] i j e

@[simp] theorem length_projAllG {ps j e} : (D.projAllG T C us ps j e).length = C.fields.length := by
  simp [projAllG]

@[simp] theorem projAllG_nil {ps j e} (h : C.fields = []) : D.projAllG T C us ps j e = [] := by
  simp [projAllG, h]

/-- The η-expansion at block index `j`. -/
def etaExpansionG (ps : List VExpr) (j : Nat) (e : VExpr) : VExpr :=
  (VExpr.const C.name us).mkApp (ps ++ D.projAllG T C us ps j e)

/-- At zero fields the η-expansion is the bare constructor applied to the parameters, exactly as
in the narrow case — this is why `VEnv.UnitEta` needed none of this file's machinery. -/
theorem etaExpansionG_of_no_fields {ps j e} (h : C.fields = []) :
    D.etaExpansionG T C us ps j e = (VExpr.const C.name us).mkApp ps := by
  simp [etaExpansionG, projAllG_nil _ _ _ _ h]

/-! ### The collapse tests

`projTermG … 0 = projTerm` at a narrow block (`projTermG_eq_projTerm`), so the two definitions
above are `projAll`/`etaExpansion` there.  These are what make `StructEtaG` a *generalisation*
of `StructEta` rather than a different rule. -/

theorem projAllG_eq_projAll {ps e} (htypes : D.types = [T]) (hctors : T.ctors = [C])
    (hrec : C.recFields = []) (hus : us.length = D.uvars) :
    D.projAllG T C us ps 0 e = D.projAll T C us ps e := by
  simp only [projAllG, projAll]
  exact List.map_congr_left fun i _ =>
    D.projTermG_eq_projTerm T C us ps [] i e htypes hctors hrec hus

theorem etaExpansionG_eq_etaExpansion {ps e} (htypes : D.types = [T]) (hctors : T.ctors = [C])
    (hrec : C.recFields = []) (hus : us.length = D.uvars) :
    D.etaExpansionG T C us ps 0 e = D.etaExpansion T C us ps e := by
  rw [etaExpansionG, etaExpansion, projAllG_eq_projAll D T C us htypes hctors hrec hus]

end VInductDecl'

/-- **Structure eta over `VEnv.IsStructureG`.**

`VEnv.StructEta` (`Theory/Inductive/StructureEta.lean`) clause for clause, with `IsStructure`
replaced by `IsStructureG` — so a block index `j` appears, and `D.types = [T]` becomes
`D.types[j]? = some T` — and `etaExpansion` replaced by `etaExpansionG`, which is the same term
built from the **padded** recursor spine.

**`noRec` is put back as an explicit premise, and that is deliberate — the widening here is
exactly one field wide.**  `IsStructureG` drops `noRec` as well as narrowing `types`, but the
zero-field rule got `noRec` for free (`VIndCtor.recFields_of_fields_nil`) and this one must not
simply drop it, for two independent reasons:

* *Nothing needs it dropped.*  `tryEtaStructCore`'s gate is `isNonRecStructure`, which **does**
  read `InductiveVal.isRec` — unlike `infer_proj`, which does not, and which is why
  `IsStructure.noRec` is a recorded narrowing on the *projection* path and not on this one.  So
  the bridge can supply `C.recFields = []` at every site the rule fires, and asking for it costs
  the repair nothing.  (This is `IsStructure.noRec`'s own docstring, taken at its word.)
* *Dropping it is not known to be safe.*  `VEnv.IsDefEq` implies both sides are well typed, so if
  `projTermG` were **not** typeable at a recursive one-constructor block, the rule would be
  *false* there and `tryEtaStructCore.WF_of_structEtaG` would be vacuous — blindness 7 of
  `docs/vacuity-ledger.md` §0, one field deeper.  Whether it is typeable turns on
  `realMinor_hasType_gen` (`Verify/Typing/ProjGenMinor.lean`), which is not this file's to settle.
  A hypothesis that might be `False` is worth strictly less than one that is one field narrower,
  so the narrow one is what is stated.

So the *entire* semantic content of this widening is `types : D.types = [T]` ↝
`D.types[j]? = some T` — the same single field as `VEnv.UnitEta`'s, and exactly row 99c's defect.

Every binder is pinned by a hypothesis, exactly as in `StructEta`: `S`, `D`, `j`, `T`, `C` by
`IsStructureG`, `us` and `ps` by the length and `HasArgs` clauses, `e` by the `HasType` clause. -/
def VEnv.StructEtaG (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat} {T : VIndType}
    {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e : VExpr},
    env.IsStructureG S D j T C →
    T.indices = [] →
    C.recFields = [] →
    us.length = D.uvars → (∀ l ∈ us, l.WF U) →
    ps.length = D.np →
    env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps →
    env.HasType U Γ e ((VExpr.const S us).mkApp ps) →
    (D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero) →
    env.IsDefEq U Γ e (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps)

namespace VEnv

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
  {T : VIndType} {C : VIndCtor} {us : List VLevel} {ps : List VExpr} {e e₁ e₂ : VExpr}

namespace StructEtaG

/-- **Nothing is lost: the widened rule implies the narrow one.**

This is the polarity certificate.  `StructEta`/`StructEtaG` sit in *negative* position in the
`.WF` obligations, so replacing one by the other is only legitimate if the new one is at least as
strong; this says it is.  Both ingredients are `IsStructure`'s two extra fields:
`IsStructure.toG` gives the shape at `j = 0`, and `etaExpansionG_eq_etaExpansion` (which needs
`types`, `ctors` **and** `noRec`) identifies the two right-hand sides. -/
theorem toStructEta (H : env.StructEtaG) : env.StructEta := by
  intro U Γ S D T C us ps e hS hidx hus husWF hps hpsA he hF17
  rw [← D.etaExpansionG_eq_etaExpansion T C us hS.types hS.ctors hS.noRec hus]
  exact H hS.toG hidx hS.noRec hus husWF hps hpsA he hF17

/-- **What `isDefEqUnitLike` needs**, from the widened rule — `StructEta.unitLike`'s proof with
`etaExpansionG_of_no_fields` in place of `etaExpansion_of_no_fields`.

At zero fields this is `VEnv.UnitEta.unitLike` reached the long way round, and that is worth
noting rather than deleting: it means `StructEtaG` subsumes `UnitEta` *and* `StructEta`, so the
two widenings are one rule, not two competing ones. -/
theorem unitLike (H : env.StructEtaG) (hS : env.IsStructureG S D j T C)
    (hidx : T.indices = []) (hnf : C.fields = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he₁ : env.HasType U Γ e₁ ((VExpr.const S us).mkApp ps))
    (he₂ : env.HasType U Γ e₂ ((VExpr.const S us).mkApp ps)) :
    env.IsDefEq U Γ e₁ e₂ ((VExpr.const S us).mkApp ps) := by
  have hF17 : D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero := .inr (by simp [hnf])
  have hrec : C.recFields = [] := VIndCtor.recFields_of_fields_nil hnf
  have h1 := H hS hidx hrec hus husWF hps hpsA he₁ hF17
  have h2 := H hS hidx hrec hus husWF hps hpsA he₂ hF17
  rw [D.etaExpansionG_of_no_fields T C us hnf] at h1 h2
  exact h1.trans h2.symm

/-- **What `tryEtaStructCore` needs**, spine half — `StructEta.congrSpine` verbatim over
`projAllG`.  Note what is *absent*: no `nm`, no `nmin`, no arity side condition.  The padded
spine is what buys that. -/
theorem congrSpine (H : env.StructEtaG) (hS : env.IsStructureG S D j T C)
    (hidx : T.indices = []) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps))
    (hF17 : D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero)
    {Tel : List VExpr} {B : VExpr} {args : List VExpr}
    (hctor : env.HasType U Γ (VExpr.const C.name us) (VExpr.mkPi Tel B))
    (hargs : env.HasArgsDF U Γ Tel (ps ++ D.projAllG T C us ps j e) (ps ++ args))
    (hB : VExpr.instAll B (ps ++ D.projAllG T C us ps j e) = (VExpr.const S us).mkApp ps) :
    env.IsDefEq U Γ e ((VExpr.const C.name us).mkApp (ps ++ args))
      ((VExpr.const S us).mkApp ps) := by
  have h1 := H hS hidx hrec hus husWF hps hpsA he hF17
  have h2 := VEnv.IsDefEq.mkAppDF hargs hctor
  rw [hB] at h2
  exact h1.trans h2

/-- **The step `tryEtaStructCore` performs, assembled** — `StructEta.congrProj` verbatim over
`projTermG`.

`hprojty` is the one premise whose *provenance* changes.  In the narrow case the call site
derives it by `projTerm_hasType`; at a widened block there is no such lemma, and supplying it is
what `docs/handoff-projections.md` §0**.1's two open lemmas (`iota_law` at an arbitrary
constructor, `realMinor_app`) are for.  Everything else in this proof is bookkeeping that does
not care which of `projTerm`/`projTermG` it is threading. -/
theorem congrProj (H : env.StructEtaG) (hS : env.IsStructureG S D j T C)
    (hidx : T.indices = []) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps))
    (hF17 : D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero)
    {args : List VExpr} (hargl : args.length = C.fields.length)
    (hprojty : ∀ k, k < C.fields.length →
      env.HasType U Γ (D.projTermG T C us ps [] k j e)
        (VExpr.instAll ((C.fields.getD k default).type.instL us)
          (ps ++ (List.range k).map fun m => D.projTermG T C us ps [] m j e)))
    (hdef : ∀ k, k < C.fields.length →
      env.IsDefEqU U Γ (D.projTermG T C us ps [] k j e) (args.getD k default))
    {B : VExpr}
    (hctor : env.HasType U Γ (VExpr.const C.name us)
      (VExpr.mkPi (D.params.map (VExpr.instL us) ++
        C.fields.map (fun F => F.type.instL us)) B))
    (hB : VExpr.instAll B (ps ++ D.projAllG T C us ps j e) = (VExpr.const S us).mkApp ps)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    env.IsDefEq U Γ e ((VExpr.const C.name us).mkApp (ps ++ args))
      ((VExpr.const S us).mkApp ps) := by
  have hgetD : ∀ k, k < C.fields.length →
      (C.fields.map fun F => VExpr.instL us F.type).getD k default
        = VExpr.instL us (C.fields.getD k default).type := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  have hargsEq : (List.range C.fields.length).map (fun k => args.getD k default) = args := by
    refine List.ext_getElem (by simp [hargl]) fun n h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]
  have hfields := VEnv.HasArgsDF.ofMap (env := env) (U := U) (Γ := Γ)
    (As := C.fields.map fun F => VExpr.instL us F.type) (as := ps)
    (f := fun k => D.projTermG T C us ps [] k j e) (g := fun k => args.getD k default)
    (i := C.fields.length) (by simp) (fun k hk => by
      rw [hgetD k hk]; exact (hdef k hk).of_l henv hΓ (hprojty k hk))
  rw [List.take_of_length_le (by simp), hargsEq] at hfields
  exact H.congrSpine hS hidx hrec hus husWF hps hpsA he hF17 hctor
    (VEnv.HasArgsDF.append hpsA.toDF hfields) hB

/-- **Round-trip check on the assembly**, at the identity spine: `congrProj` must reproduce the
rule it is built from.  Same test as `StructEta.congrProj_at_projAll`, and it catches the same
misalignments (wrong telescope, wrong instantiation spine, off-by-one in the `range`) — now with
the block index threaded, which is the new thing that could be misaligned. -/
theorem congrProj_at_projAllG (H : env.StructEtaG) (hS : env.IsStructureG S D j T C)
    (hidx : T.indices = []) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) (husWF : ∀ l ∈ us, l.WF U)
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp ps))
    (hF17 : D.isLE = true ∨ ∀ k, k < C.fields.length →
      (C.fields.getD k default).lvl.inst us ≈ .zero)
    (hprojty : ∀ k, k < C.fields.length →
      env.HasType U Γ (D.projTermG T C us ps [] k j e)
        (VExpr.instAll ((C.fields.getD k default).type.instL us)
          (ps ++ (List.range k).map fun m => D.projTermG T C us ps [] m j e)))
    {B : VExpr}
    (hctor : env.HasType U Γ (VExpr.const C.name us)
      (VExpr.mkPi (D.params.map (VExpr.instL us) ++
        C.fields.map (fun F => F.type.instL us)) B))
    (hB : VExpr.instAll B (ps ++ D.projAllG T C us ps j e) = (VExpr.const S us).mkApp ps)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) :
    env.IsDefEq U Γ e (D.etaExpansionG T C us ps j e) ((VExpr.const S us).mkApp ps) := by
  have hgetD : ∀ k, k < C.fields.length →
      (D.projAllG T C us ps j e).getD k default = D.projTermG T C us ps [] k j e := by
    intro k hk
    have hk' : k < (List.range C.fields.length).length := by simpa using hk
    simp only [VInductDecl'.projAllG, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some, List.getElem_range]
  refine H.congrProj hS hidx hrec hus husWF hps hpsA he hF17 (D.length_projAllG T C us)
    hprojty (fun k hk => ?_) hctor hB henv hΓ
  rw [hgetD k hk]
  exact ⟨_, hprojty k hk⟩

end StructEtaG

/-- `StructEtaG` is consistent: the empty environment declares no block, so every instance is
vacuous there.  Same shape as `empty_structEta` and `empty_unitEta`, with `IsStructureG.types`'
`getElem?` form in place of the singleton equation. -/
theorem empty_structEtaG : VEnv.empty.StructEtaG := by
  intro U Γ S D j T C us ps e hS _ _ _ _ _ _ _ _
  obtain ⟨env₀, env₁, _, hadd, hle⟩ := hS.decl
  have h := hle.constants
    (VEnv.addInduct'_types (T := T) hadd (List.getElem?_eq_some_iff.1 hS.types |>.2 ▸ (by
      exact List.getElem_mem _)))
  simp [VEnv.empty] at h

end VEnv

/-! ## The firing instance: a **two-type mutual block with a field**

`UnitEta.lean`'s witness is a two-type block at **zero** fields, which is all
`isDefEqUnitLike` needs and which exercises none of the projection machinery.  The acceptance
criterion for `StructEtaG` is stricter: its premises must be jointly satisfiable at a member of a
mutual block that *has* a field, because that is where `projTermG`'s padding is doing work and
where `MutNonRec.projCore_arity_wrong` would bite if the rule had been stated over `projTerm`.

`MutField.decl` below is that block: `mutual inductive A | mk : A; inductive B | mk : (f : ∀ p :
Prop, p) → B end`, in `Type`.  The projected member is **`B`, at index `j = 1`** — deliberately
not index 0, so that the padded motive and minor blocks are non-degenerate and a wrong slot would
show up.

The field type is `∀ p : Prop, p` (`Lean4Lean.bazField`, reused from
`Theory/Inductive/StructureEta.lean`) for the same reason it is used there: the empty environment
has no other closed type, and its level `imax 1 0 ≈ 0` satisfies `StructEtaG`'s F17 clause in the
small-elimination branch, which is the branch that has to be discharged since `isLE = false`.
-/

namespace MutField

/-- `A`'s constructor: zero fields. -/
def aCtor : VIndCtor := { name := `MutField.A.mk, params := [], fields := [], args := [] }

/-- **`B`'s constructor: one field**, of type `∀ p : Prop, p`.  This is what makes the witness
more than `MutNonRec.decl2` renamed. -/
def bCtor : VIndCtor :=
  { name := `MutField.B.mk, params := [], fields := [bazField], args := [] }

def aTy : VIndType :=
  { name := `MutField.A, type := .sort (.succ .zero), indices := [], ctors := [aCtor] }

def bTy : VIndType :=
  { name := `MutField.B, type := .sort (.succ .zero), indices := [], ctors := [bCtor] }

/-- The block: two types, in `Type`, neither recursive, `isLE = false`. -/
def decl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  types := [aTy, bTy]
  isLE := false

theorem decl_nm : decl.nm = 2 := rfl
theorem decl_nmin : decl.nmin = 2 := rfl
theorem bCtor_fields_length : bCtor.fields.length = 1 := rfl

/-- **The block is well formed.**  Assembled from `MutNonRec.decl2_WF`'s skeleton
(`Verify/TypeChecker/UnitEta.lean`) and `bazDecl_WF`'s field clause
(`Theory/Inductive/StructureEta.lean`); the only new work is the level constraint
`imax (imax 1 0) 1 ≤ 1`, which holds because `imax _ 0` evaluates to `0`. -/
theorem decl_WF : decl.WF .empty where
  types_ne := by simp [decl]
  params := trivial
  types := by
    intro T hT
    simp [decl] at hT
    rcases hT with rfl | rfl <;>
      exact { indices := trivial
              isType := ⟨_, .sortDF trivial trivial (.refl _)⟩
              canon := ⟨_, .sortDF trivial trivial (.refl _)⟩ }
  ctors := by
    intro env₁ he j T hT C hC
    have hA : env₁.constants `MutField.A = some ⟨0, .sort (.succ .zero)⟩ :=
      VEnv.addConstList_constants he (`MutField.A, ⟨0, .sort (.succ .zero)⟩)
        (by simp [VInductDecl'.typeConsts, decl, aTy, bTy])
    have hB : env₁.constants `MutField.B = some ⟨0, .sort (.succ .zero)⟩ :=
      VEnv.addConstList_constants he (`MutField.B, ⟨0, .sort (.succ .zero)⟩)
        (by simp [VInductDecl'.typeConsts, decl, aTy, bTy])
    match j, hT with
    | 0, hT =>
      simp [decl] at hT; subst hT; simp [aTy] at hC; subst hC
      exact { params_len := rfl, params_eq := .zero, fields := nofun,
              args_len := rfl, args_fresh := by simp [aCtor], args_ty := .nil,
              result := .constDF hA nofun nofun rfl .nil }
    | 1, hT =>
      simp [decl] at hT; subst hT; simp [bTy] at hC; subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_,
               args_len := rfl, args_fresh := by simp [bCtor], args_ty := .nil,
               result := .constDF hB nofun nofun rfl .nil }
      intro i F hF
      have hpos : ∃ A, decl.NoBlock A ∧
          env₁.IsDefEqType decl.uvars
            (((bCtor.fields.take i).map (·.type)).reverse ++ decl.params.reverse)
            bazField.type A :=
        ⟨bazField.type, by simp [VInductDecl'.NoBlock, VExpr.NoConsts, bazField],
          _, bazField_hasType⟩
      match i, hF with
      | 0, hF =>
        simp [bCtor] at hF
        subst hF
        exact { hasType := bazField_hasType
                level := fun ls => by simp [VLevel.eval, decl, bazField, Lean.Nat.imax]
                binders_indep := nofun
                pos := hpos }
  isLE := by simp [decl]

theorem declEnv_eq : ∃ e, VEnv.empty.addInduct' decl = some e := ⟨_, rfl⟩

noncomputable def declEnv : VEnv := declEnv_eq.choose

/-- **`IsStructureG` at the second member of the two-type block — the one with the field.** -/
theorem declEnv_IsStructureG : declEnv.IsStructureG `MutField.B decl 1 bTy bCtor where
  types := rfl
  name := rfl
  ctors := rfl
  decl := ⟨.empty, declEnv, decl_WF, declEnv_eq.choose_spec, VEnv.LE.rfl⟩

/-- **`VEnv.IsStructure` is unavailable at this block, for any `S`, `T`, `C`** — the `types`
field alone refutes it.  So the *narrow* rule `VEnv.StructEta` says nothing here, and this is
exactly the configuration ledger row 99c is about, now with a field present. -/
theorem decl_not_isStructure {S T C} : ¬ declEnv.IsStructure S decl T C := by
  intro h; have := h.types; simp [decl] at this

theorem declEnv_B : declEnv.constants `MutField.B = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addInduct'_types (T := bTy) declEnv_eq.choose_spec (by simp [decl])

/-- The context `(x : B)`. -/
def bCtx : List VExpr := [.const `MutField.B []]

/-- `B`'s only field is a proof, so `StructEtaG`'s F17 clause holds in its small-elimination
form.  (`decl.isLE` is `false`, so the `.inl` disjunct is unavailable — this is the branch that
has to be discharged.) -/
theorem bCtor_field_prop : ∀ k, k < bCtor.fields.length →
    (bCtor.fields.getD k default).lvl.inst [] ≈ .zero := by
  intro k hk
  match k, hk with
  | 0, _ =>
    simp [bCtor, bazField, VLevel.inst, VLevel.equiv_def, VLevel.eval, Lean.Nat.imax]

/-- **Every premise of `VEnv.StructEtaG`, satisfied at once, at a member of a two-type mutual
block *with a field*, in `Type`.**

The last three conjuncts are the point: the block has two types, the projected member is at
index **1**, and its constructor has **one** field.  Compare `bazEnv_structEta_premises`
(`Theory/Inductive/StructureEta.lean`), the same audit at a singleton block, and
`MutNonRec.decl2Env_unitEta_premises` (`Verify/TypeChecker/UnitEta.lean`), the same audit at a
mutual block with **no** fields.  This one is the conjunction of both directions. -/
theorem declEnv_structEtaG_premises :
    declEnv.IsStructureG `MutField.B decl 1 bTy bCtor ∧
    bTy.indices = [] ∧
    bCtor.recFields = [] ∧
    ([] : List VLevel).length = decl.uvars ∧
    (∀ l ∈ ([] : List VLevel), l.WF 0) ∧
    ([] : List VExpr).length = decl.np ∧
    declEnv.HasArgs 0 bCtx (decl.params.map (VExpr.instL [])) [] ∧
    declEnv.HasType 0 bCtx (.bvar 0) ((VExpr.const `MutField.B []).mkApp []) ∧
    (decl.isLE = true ∨ ∀ k, k < bCtor.fields.length →
      (bCtor.fields.getD k default).lvl.inst [] ≈ .zero) ∧
    decl.types.length = 2 ∧ bCtor.fields.length = 1 :=
  ⟨declEnv_IsStructureG, rfl, rfl, rfl, nofun, rfl, .nil, .bvar (.zero ..),
    .inr bCtor_field_prop, rfl, rfl⟩

/-- **The rule, fired at that witness**: `x ≡ B.mk x.f` for `x : B`, where `B` is the second
member of a two-type mutual block.  This is the instance `VEnv.StructEta` cannot state. -/
theorem declEnv_structEtaG (H : declEnv.StructEtaG) :
    declEnv.IsDefEq 0 bCtx (.bvar 0) (decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0))
      (.const `MutField.B []) :=
  H declEnv_IsStructureG rfl rfl rfl nofun rfl .nil (.bvar (.zero ..)) (.inr bCtor_field_prop)

/-- …and the term it produces is a *one*-element constructor spine whose entry is a genuine
`projTermG`.  So the firing is not the zero-field case in disguise. -/
theorem declEnv_etaExpansionG_eq :
    decl.etaExpansionG bTy bCtor [] [] 1 (.bvar 0)
      = (VExpr.const `MutField.B.mk []).mkApp
          [decl.projTermG bTy bCtor [] [] [] 0 1 (.bvar 0)] := rfl

/-! ### Wall 1, measured at this very block: `projCore` is wrong here and `projCoreG` is right

`MutNonRec.projCore_arity_wrong` (`Verify/StructureBridge.lean`) is stated at `decl2`, a block
with no fields, so it never had to be re-run somewhere the projection is non-degenerate.  Here it
is, at `MutField.decl`. -/

/-- **`projCore`'s spine is short at this block.**  `recArity_eq_projCore_iff` turns the
mismatch into `¬ (nm + nmin = 2)`, and here `nm = nmin = 2`, so the narrow spine supplies 3
arguments where the recursor needs 5.  This is why `VEnv.StructEtaG` is **not** stated over
`projTerm`. -/
theorem projCore_arity_wrong_here :
    decl.nm + decl.nmin = 4 ∧
    decl.recArity bTy = 5 ∧
    decl.np + 2 + bTy.indices.length + 1 = 3 ∧
    ¬ decl.recArity bTy = decl.np + 2 + bTy.indices.length + 1 :=
  ⟨rfl, rfl, rfl, fun h => by
    rw [decl.recArity_eq_projCore_iff bTy] at h; exact absurd h (by decide)⟩

/-- **…and `projCoreG`'s spine is exactly `recArity` at the same block**, with no side
condition.  So `projCore_arity_wrong` is *inert* against `StructEtaG`: wall 1 is down, and
reporting it as what blocks the positive-field repair would be a bad citation. -/
theorem projCoreG_arity_right_here (i : Nat) (earlier : List VExpr) (e : VExpr) :
    ([] ++ decl.padMotives bTy bCtor [] [] [] i 1 earlier e ++
        decl.padMinors (decl.projLvls bCtor [] i) []
          (decl.padMotives bTy bCtor [] [] [] i 1 earlier e)
          ((bTy.projMotive bCtor [] [] [] i earlier).mkApp ([] ++ [e])) i 1 ++ [] ++
        [e]).length
      = decl.recArity bTy :=
  decl.recArity_eq_projCoreG bTy bCtor [] rfl rfl

end MutField

/-! ## Wall 3, machine-checked: `TrProj` is the real obstruction

Blindness 4 of `docs/vacuity-ledger.md` §0 — "a false negative asserted as established" — is the
expensive one, so the claim that `TrProj` blocks the *bridge* is proved rather than argued.

`TrProj` has one constructor, and it carries `env.IsStructure S D T C`.  So every translated
`.proj` node certifies the **narrow** predicate at its structure's name, whatever the widened
bridge says. -/

/-- **Every `TrProj` derivation carries `VEnv.IsStructure` at the projected name.**  One-line
case analysis, and it is the whole of wall 3. -/
theorem TrProj.isStructure {env : VEnv} {U : Nat} {Γ : List VExpr} {S : Lean.Name} {i : Nat}
    {e e' : VExpr} (h : TrProj env U Γ S i e e') : ∃ D T C, env.IsStructure S D T C := by
  cases h; exact ⟨_, _, _, ‹_›⟩

/-- **Consequence at the witness block.**  In `MutField.declEnv`, a `.proj MutField.B k x` node
can be translated only by certifying `IsStructure` for the name `MutField.B` at some block
`D ≠ MutField.decl` — which `MutField.decl_not_isStructure` rules out for `decl` itself, and
which nothing in the tree supplies for any other `D` (that would be ledger G4, uniqueness of
blocks per name, which is *absent*).

So the per-iteration clause of `EtaStructSpineG`, which asks for exactly such a translation, is
no more satisfiable at this block than `EtaStructSpine`'s is.  **Widening the bridge is necessary
and not sufficient**; `TrProj` must be widened to `IsStructureG`/`projTermG` too, and that is a
change to a predicate consumed by `TrExprS`, `TrProj.wf` (**`Verify/Typing/Lemmas.lean`** — not
`ProjSkip.lean`, which holds the syntactic core of its live route; corrected per ledger row
107f(iii)), `TrProj.uniq`, `TrProj.weak'_inv` and `inferProj.WF`.  And `TrProj.wf` is proved only
in the sense that its *local* proof has no `sorry`: its **cone carries two**, `weakN_iff` and
`forallE_inv_stratified`, via `projTerm_hasType` (row 107f(i)).  Its statement must survive a
widening either way, and by `TrExprS.wf`'s `proj` case — `h2.wf henv hΔ.toCtx (ih hΔ)`,
`Verify/Typing/Lemmas.lean` — a widened `TrProj.wf` would have to *assert* `projTermG`'s typing,
which is wall 2.  That is why the two walls are not separable. -/
theorem trProj_at_MutField_needs_other_block {U : Nat} {Γ : List VExpr} {i : Nat}
    {e e' : VExpr} (h : TrProj MutField.declEnv U Γ `MutField.B i e e') :
    ∃ D T C, MutField.declEnv.IsStructure `MutField.B D T C ∧ D ≠ MutField.decl := by
  obtain ⟨D, T, C, hD⟩ := h.isStructure
  exact ⟨D, T, C, hD, fun hEq => MutField.decl_not_isStructure (hEq ▸ hD)⟩

/-! ## The widened bridge, and `tryEtaStructCore.WF` over it -/

namespace TypeChecker.Inner
open Lean hiding Environment Exception

variable {e₁ e₂ : Expr} {e₁' e₂' : VExpr}

/-- **`EtaStructSpine`, widened to `IsStructureG`.**

Conjunct for conjunct identical to `EtaStructSpine` (`Verify/TypeChecker/IsDefEq.lean`) except:

* the existential carries a block index `j` and concludes `c.venv.IsStructureG w.induct D j T C`
  in place of `c.venv.IsStructure w.induct D T C`;
* `projAll`/`projTerm` become `projAllG`/`projTermG` at that index, in `hB` and in the
  per-iteration clause;
* `C.recFields = []` becomes an explicit conjunct, because `IsStructureG` no longer carries it
  and `VEnv.StructEtaG` asks for it — see there for why keeping it is strictly better than
  dropping it.  It costs a narrow bridge nothing (`IsStructure.noRec`) and it is what
  `isNonRecStructure`, the checker's own gate, already tests;
* **one conjunct is added**: the projections' typing.

That last point is the honest accounting, and it goes the *wrong* way for this theorem, so it is
stated rather than buried.  `EtaStructSpine`'s docstring explains that it deliberately omits the
projections' typing because `projTerm_hasType` (`Verify/Typing/Lemmas.lean`) *derives* it from
`IsStructure` plus the universe data plus F17 — and `projTerm_hasType` is exactly the lemma that
has no `IsStructureG` counterpart, because its proof runs through `projMinor_hasType` →
`iota_law` at `H.nm_eq`, `H.nmin_eq`, `H.noRec`.  `docs/handoff-projections.md` §0**.1 has the
chain down to two open lemmas (`iota_law` at an arbitrary constructor of an arbitrary block, and
`realMinor_app`), both owned elsewhere.  So the conjunct is carried here.

**Its shape is the minimal one**, the specific instance `StructEtaG.congrProj` consumes, not the
`Γ`/`ps`/`ιs`/`e`-quantified `ProjHasTypeG` (`Verify/Typing/ProjGenMotive.lean`).  A bridge is a
hypothesis; asking for the quantified predicate would strengthen it for no gain.  When
`projTermG_hasType` lands, `ProjHasTypeG … j k` will discharge this conjunct at every `k`, and
the conjunct can be deleted rather than re-derived.

**And a warning that belongs on this definition rather than in a document.**  Unlike
`UnitLikeBridgeG`, this predicate does **not** become satisfiable at a member of a two-type
mutual block by being widened.  Its per-iteration clause asks for `c.TrExprS (.proj I k t) …`,
and `TrExprS`'s `.proj` constructor goes through `TrProj` (`Verify/Typing/Expr.lean`), whose only
constructor carries `env.IsStructure` — unavailable at such a block
(`MutNonRec.decl2_not_isStructure`, `Verify/TypeChecker/UnitEta.lean`) — and produces `projTerm`,
not `projTermG`.  That clause sits in *positive* position inside the bridge.  So widening
`EtaStructSpine` is necessary and not sufficient: `TrProj` must be widened too, and that is a
change to a predicate `TrExprS`, `TrProj.wf`, `TrProj.uniq`, `TrProj.weak'_inv` and
`inferProj.WF` all consume. -/
def EtaStructSpineG (c : VContext) (t s : Expr) (t' s' : VExpr) : Prop :=
  ∀ {f : Name} {w : ConstructorVal},
    (∃ us, s.getAppFn = .const f us) →
    c.env.find? f = some (.ctorInfo w) →
    (s.getAppNumArgs == w.numParams + w.numFields) = true →
    c.env.isNonRecStructure w.induct = true →
    ∃ (D : VInductDecl') (j : Nat) (T : VIndType) (C : VIndCtor) (us : List VLevel)
      (ps args : List VExpr) (B : VExpr),
      c.venv.IsStructureG w.induct D j T C ∧ C.name = f ∧ T.indices = [] ∧
      C.recFields = [] ∧
      us.length = D.uvars ∧ (∀ l ∈ us, l.WF c.lparams.length) ∧ ps.length = D.np ∧
      w.numParams = D.np ∧ C.fields.length = w.numFields ∧
      args.length = C.fields.length ∧
      c.venv.HasArgs c.lparams.length c.vlctx.toCtx (D.params.map (VExpr.instL us)) ps ∧
      c.venv.HasType c.lparams.length c.vlctx.toCtx t'
        ((VExpr.const w.induct us).mkApp ps) ∧
      (D.isLE = true ∨ ∀ k, k < C.fields.length →
        (C.fields.getD k default).lvl.inst us ≈ .zero) ∧
      s' = (VExpr.const C.name us).mkApp (ps ++ args) ∧
      c.venv.HasType c.lparams.length c.vlctx.toCtx (VExpr.const C.name us)
        (VExpr.mkPi (D.params.map (VExpr.instL us) ++
          C.fields.map (fun F => VExpr.instL us F.type)) B) ∧
      VExpr.instAll B (ps ++ D.projAllG T C us ps j t') = (VExpr.const w.induct us).mkApp ps ∧
      (∀ k, k < C.fields.length →
        c.venv.HasType c.lparams.length c.vlctx.toCtx (D.projTermG T C us ps [] k j t')
          (VExpr.instAll ((C.fields.getD k default).type.instL us)
            (ps ++ (List.range k).map fun m => D.projTermG T C us ps [] m j t'))) ∧
      (∀ i (h : i < s.getAppArgs.size), w.numParams ≤ i →
        c.TrExprS (.proj w.induct (i - w.numParams) t)
          (D.projTermG T C us ps [] (i - w.numParams) j t') ∧
        c.TrExprS s.getAppArgs[i] (args.getD (i - w.numParams) default))

/-- **The old bridge implies the new one**, at `j = 0` — the polarity certificate, so nothing
that would have proved `EtaStructSpine` is wasted.

Three steps, and the middle one is the interesting one:

* `VEnv.IsStructure.toG` for the shape;
* `projTermG_eq_projTerm` / `projAllG_eq_projAll` for every occurrence of the projection terms —
  these need `IsStructure`'s `types`, `ctors` **and** `noRec`, all of which the narrow bridge
  hands over, which is why the implication holds in this direction and not the other;
* `projTerm_hasType` for the added conjunct, with the two-branch level argument
  (`WF_of_structEta`'s own, and `TrProj.wf`'s) turning the narrow bridge's F17 clause into the
  elimination-level premise.  This is the derivation `EtaStructSpine` was relying on, run once
  here so that the added conjunct costs a *narrow* bridge nothing at all. -/
theorem EtaStructSpine.toG {c : VContext} {t s : Expr} {t' s' : VExpr}
    (hbr : EtaStructSpine c t s t' s') : EtaStructSpineG c t s t' s' := by
  intro f w h1 h2 h3 h4
  obtain ⟨D, T, C, us, ps, args, B, hIS, hCname, hidx, hus, huswf, hps, hnp, hnfl, hargl,
    hpsA, hty1, hF17, hs'eq, hctor, hB, hiter⟩ := hbr h1 h2 h3 h4
  have heqT : ∀ (ps' is' : List VExpr) (k : Nat) (e : VExpr),
      D.projTermG T C us ps' is' k 0 e = D.projTerm T C us ps' is' k e :=
    fun ps' is' k e =>
      D.projTermG_eq_projTerm T C us ps' is' k e hIS.types hIS.ctors hIS.noRec hus
  have heqA : D.projAllG T C us ps 0 t' = D.projAll T C us ps t' :=
    D.projAllG_eq_projAll T C us hIS.types hIS.ctors hIS.noRec hus
  refine ⟨D, 0, T, C, us, ps, args, B, hIS.toG, hCname, hidx, hIS.noRec, hus, huswf, hps, hnp,
    hnfl, hargl, hpsA, hty1, hF17, hs'eq, hctor, by rw [heqA]; exact hB, fun k hk => ?_,
    fun i hi hge => ?_⟩
  · simp only [heqT]
    refine projTerm_hasType c.Ewf hIS hus huswf k hk ?_ c.Δwf ?_ hps ?_ hpsA ?_
    · intro m _ _
      by_cases hLE : D.isLE = true
      · simp only [VInductDecl'.elimLvl, VInductDecl'.projLvls, hLE, if_true, VLevel.inst,
          List.getD_cons_zero]
        rfl
      · simp only [Bool.not_eq_true] at hLE
        rw [VInductDecl'.elimLvl, VInductDecl'.projLvls, if_neg (by simp [hLE]),
          if_neg (by simp [hLE])]
        rcases hF17 with hh | hh
        · exact absurd hh (by simp [hLE])
        · exact hh m (by omega)
    · simpa using hty1
    · simp [hidx]
    · simp [hidx]; exact .nil
  · simp only [heqT]; exact hiter i hi hge

/-- **`tryEtaStructCore.WF` from the widened pair.**

`tryEtaStructCore.WF_of_structEta` (`Verify/TypeChecker/IsDefEq.lean`) is this statement from
`c.venv.StructEta` and `EtaStructSpine c`; this is it from `c.venv.StructEtaG` and
`EtaStructSpineG c`.  The proof is that one's, verbatim, with two changes: the destructuring
carries `j`, and the `hprojty` block — nine lines deriving the projections' typing by
`projTerm_hasType` — is replaced by the bridge's conjunct, because there is no
`projTermG_hasType` to derive it with.  `VEnv.StructEtaG.congrProj` closes it in place of
`VEnv.StructEta.congrProj`.

Like `WF_of_structEta` it **enters** the `.ctorInfo` arm rather than killing it with
`TrEnv.not_ctorInfo`, so it survives the `AddInduct` flip verbatim, and it inherits
`inferType.WF`'s four holes (`weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`,
`NormalEq.descend`) and adds none.

**What this buys, and what it does not.**  It buys: `tryEtaStructCore.WF` now reduces to a pair
whose *first* member is not refuted by the mutual-block witness, and whose second member is
weaker than `EtaStructSpine` (`EtaStructSpine.toG`).  It does not buy satisfiability of that
second member at a mutual block — see `EtaStructSpineG`'s docstring, wall 3. -/
theorem tryEtaStructCore.WF_of_structEtaG {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hSE : c.venv.StructEtaG) (hbr : EtaStructSpineG c e₁ e₂ e₁' e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold tryEtaStructCore
  split <;> [skip; exact .pure nofun]
  rename_i f us heq
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
  split <;> [skip; exact .pure nofun]
  rename_i fInfo hfi
  split <;> [skip; exact .pure nofun]
  rename_i hnum
  split <;> [skip; exact .pure nofun]
  rename_i hnrs
  obtain ⟨D, j, T, C, us', ps, args, B, hIS, hCname, hidx, hrec, hus, huswf, hps, hnp, hnf,
    hargl, hpsA, hty1, hF17, he₂eq, hctor, hB, hprojty, hiter⟩ := hbr ⟨us, heq⟩ hci hnum hnrs
  refine (inferType.WF he₁).bind fun _ _ _ ⟨_, _, _, ht1, _⟩ => ?_
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, _, _, ht2, _⟩ => ?_
  refine (isDefEq.WF ht1 ht2).bind fun b _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine (RecM.WF.forIn'Prefix
    (Inv := fun ys st _ => st.1 = none ∧ ∀ a ∈ ys,
      c.IsDefEqU (D.projTermG T C us' ps [] (a - hfi.numParams) j e₁')
        (args.getD (a - hfi.numParams) default))
    (Br := fun st _ => st.1 = some false)
    (pre := []) ?_ ⟨rfl, nofun⟩).bind fun r _ _ hr => ?_
  · intro ys a ha bb ss ⟨_, hb2⟩
    have hlt : a < e₂.getAppArgs.size := by simp [List.mem_range'] at ha; omega
    have hge : hfi.numParams ≤ a := by simp [List.mem_range'] at ha; omega
    obtain ⟨hp, hq⟩ := hiter a hlt hge
    refine (isDefEq.WF hp hq).bind fun _ _ _ hres => ?_
    split
    · rename_i hrt
      refine .pure ⟨rfl, ?_⟩
      intro x hx
      simp at hx
      rcases hx with hx | rfl
      · exact hb2 x hx
      · exact hres hrt
    · exact .pure rfl
  · rcases hr with ⟨h1, h2⟩ | h1
    · rw [h1]
      refine .pure fun _ => ?_
      have hkey : ∀ k, k < C.fields.length →
          c.IsDefEqU (D.projTermG T C us' ps [] k j e₁') (args.getD k default) := by
        intro k hk
        have hmem : hfi.numParams + k ∈
            [] ++ List.range' hfi.numParams [hfi.numParams:e₂.getAppArgs.size].size := by
          simp [List.mem_range']
          have hsz : e₂.getAppArgs.size = hfi.numParams + hfi.numFields := by
            have h0 : e₂.getAppArgs.toList.length = e₂.getAppNumArgs := by
              rw [Expr.getAppArgs_toList_rev, List.length_reverse, ← Expr.getAppNumArgs_eq]
            simp only [Array.length_toList] at h0
            rw [h0]; simpa using hnum
          omega
        simpa using h2 _ hmem
      exact ⟨_, he₂eq ▸ hSE.congrProj hIS hidx hrec hus huswf hps hpsA hty1 hF17 hargl
        hprojty hkey hctor hB c.Ewf c.Δwf⟩
    · rw [h1]; exact .pure nofun

/-! ### A bridge that `TrProj.isStructure` cannot refute — and what that does and does not buy

Ledger row 107.  The measurement behind this block is that `WF_of_structEtaG` uses the
per-iteration `TrExprS` **pair** for exactly one thing: feeding `isDefEq.WF` so as to read off
its postcondition.  So the bridge can carry the postcondition directly, and then it mentions no
translation relation at all.
-/

/-- **`EtaStructSpineG` with the per-iteration `TrExprS` pair replaced by the call's
postcondition.**

Conjunct for conjunct `EtaStructSpineG`, except the last: instead of

    c.TrExprS (.proj w.induct (i - w.numParams) t) (D.projTermG … (i - w.numParams) j t') ∧
    c.TrExprS s.getAppArgs[i] (args.getD (i - w.numParams) default)

it asks, at every state, for the `RecM.WF` of the call `tryEtaStructCore` actually makes.  That
is *exactly* what `WF_of_structEtaG` derives from the pair (by `isDefEq.WF`) and all it derives
from it, so this is the weakest form of that conjunct the theorem can consume —
`EtaStructSpineG.toCall` is the implication and it is hole-free.

**Why it is worth stating.**  Wall 3 (`TrProj.isStructure`) refutes `EtaStructSpineG` at a
member of a mutual block by refuting its `TrExprS (.proj …)` clause.  This predicate's constant
cone contains **neither `TrProj` nor `TrExprS` nor `VEnv.IsStructure`** (measured: 3130
constants, none of the three; `EtaStructSpineG`'s cone contains all three), so that refutation
does not reach it.

**Why that is a relocation and not a repair, which is the honest label.**  `isDefEq.WF`
(`Verify/EquivManager.lean`) is the *only* WF lemma for `isDefEq` in the tree, and its contract
takes a `c.TrExprS` per argument.  So the only route to this conjunct that anything can
currently walk is `toCall`, i.e. the refuted pair.  What the swap achieves is therefore precise
and small: **a refuted hypothesis becomes a not-refuted one.**  No proof fires that did not fire
before, and the obstruction moves from the bridge's *satisfiability* to its *discharge*.
Blindness 4 cuts both ways — a machine-checked refutation that no longer applies is worth
recording — but this is not satisfiability, and it is not a proof.

**Two caveats that belong on the definition.**

* `RecM.WF` is partial correctness (`∀ m, m.WF → M.WF …`, and `M.WF` speaks only about runs that
  return `.ok`), so this conjunct is also discharged by a call that *throws*.  That is aligned
  rather than sloppy — the conclusion of `WF_of_structEtaGC` is a `RecM.WF` in the same currency,
  and a throwing `isDefEq` makes `tryEtaStructCore` throw too — but it means the conjunct is
  strictly weaker than "the projections really are defeq to the arguments".  It is not
  *trivially* true: `Methods.WF` is inhabited (`Methods.withFuel.WF`) at every fuel, so the
  `∀ m` is not an empty quantifier.
* The cone contains `TypeChecker.Methods.WF`, whose **fields** mention `c.TrExprS` — in negative
  position, as hypotheses of the method contracts.  So "mentions no translation relation" is a
  claim about what the predicate *asserts*, which is what `TrProj.isStructure` can attack, and
  not about what its unfolding contains. -/
def EtaStructSpineGC (c : VContext) (t s : Expr) (t' s' : VExpr) : Prop :=
  ∀ {f : Name} {w : ConstructorVal},
    (∃ us, s.getAppFn = .const f us) →
    c.env.find? f = some (.ctorInfo w) →
    (s.getAppNumArgs == w.numParams + w.numFields) = true →
    c.env.isNonRecStructure w.induct = true →
    ∃ (D : VInductDecl') (j : Nat) (T : VIndType) (C : VIndCtor) (us : List VLevel)
      (ps args : List VExpr) (B : VExpr),
      c.venv.IsStructureG w.induct D j T C ∧ C.name = f ∧ T.indices = [] ∧
      C.recFields = [] ∧
      us.length = D.uvars ∧ (∀ l ∈ us, l.WF c.lparams.length) ∧ ps.length = D.np ∧
      w.numParams = D.np ∧ C.fields.length = w.numFields ∧
      args.length = C.fields.length ∧
      c.venv.HasArgs c.lparams.length c.vlctx.toCtx (D.params.map (VExpr.instL us)) ps ∧
      c.venv.HasType c.lparams.length c.vlctx.toCtx t'
        ((VExpr.const w.induct us).mkApp ps) ∧
      (D.isLE = true ∨ ∀ k, k < C.fields.length →
        (C.fields.getD k default).lvl.inst us ≈ .zero) ∧
      s' = (VExpr.const C.name us).mkApp (ps ++ args) ∧
      c.venv.HasType c.lparams.length c.vlctx.toCtx (VExpr.const C.name us)
        (VExpr.mkPi (D.params.map (VExpr.instL us) ++
          C.fields.map (fun F => VExpr.instL us F.type)) B) ∧
      VExpr.instAll B (ps ++ D.projAllG T C us ps j t') = (VExpr.const w.induct us).mkApp ps ∧
      (∀ k, k < C.fields.length →
        c.venv.HasType c.lparams.length c.vlctx.toCtx (D.projTermG T C us ps [] k j t')
          (VExpr.instAll ((C.fields.getD k default).type.instL us)
            (ps ++ (List.range k).map fun m => D.projTermG T C us ps [] m j t'))) ∧
      (∀ i (_ : i < s.getAppArgs.size), w.numParams ≤ i → ∀ st : VState,
        RecM.WF c st (isDefEq (.proj w.induct (i - w.numParams) t) s.getAppArgs[i])
          fun b _ => b → c.IsDefEqU (D.projTermG T C us ps [] (i - w.numParams) j t')
            (args.getD (i - w.numParams) default))

/-- **The `TrExprS` pair implies the call's postcondition** — one `isDefEq.WF` per iteration and
nothing else, so this is the whole of the swap's cost.

**Hole-free** (cone 9592, no `sorryAx`), but *not* axiom-free: it carries `Classical.choice` and
the three frozen `Lean.*` axioms of guard 1's whitelist (`Lean.Expr.eqv_eq`,
`Lean.Level.instLawfulBEqLevel`, `Lean.Syntax.structEq_eq`), all of them through `isDefEq.WF`.
That is the same set `WF_of_structEtaG` already carried, so nothing new is trusted here. -/
theorem EtaStructSpineG.toCall {c : VContext} {t s : Expr} {t' s' : VExpr}
    (hbr : EtaStructSpineG c t s t' s') : EtaStructSpineGC c t s t' s' := by
  intro f w h1 h2 h3 h4
  obtain ⟨D, j, T, C, us, ps, args, B, hIS, hCname, hidx, hrec, hus, huswf, hps, hnp, hnfl,
    hargl, hpsA, hty1, hF17, hs'eq, hctor, hB, hprojty, hiter⟩ := hbr h1 h2 h3 h4
  refine ⟨D, j, T, C, us, ps, args, B, hIS, hCname, hidx, hrec, hus, huswf, hps, hnp,
    hnfl, hargl, hpsA, hty1, hF17, hs'eq, hctor, hB, hprojty, fun i hi hge _ => ?_⟩
  obtain ⟨hp, hq⟩ := hiter i hi hge
  exact isDefEq.WF hp hq

/-- **The GC bridge is satisfiable today, vacuously** — established rather than asserted, since
an unproved claim of vacuity is worth nothing (ledger §0, blindness 4).

The route is `tryEtaStructCore_never_true`'s: a translated `s` puts its head constant in
`c.venv`, and `TrEnv.not_ctorInfo` then forbids `c.env.find?` from answering `.ctorInfo` while
`AddInduct` is empty.  So the second premise is refuted and every instance is vacuous — exactly
the status `EtaStructSpine`'s docstring records for the narrow bridge, and unchanged by the
swap.  This is *why* `WF_of_structEtaGC` does not fire: its remaining hypothesis
`c.venv.StructEtaG` is an abstract rule nothing discharges. -/
theorem EtaStructSpineGC.today {c : VContext} {t s : Expr} {t' s' : VExpr}
    (hs : c.TrExprS s s') : EtaStructSpineGC c t s t' s' := by
  intro f w h1 h2 _ _
  obtain ⟨us, heq⟩ := h1
  obtain ⟨f', hf⟩ := head_tr hs
  rw [heq] at hf
  let .const hc _ _ := hf
  exact absurd h2 fun hh => c.trenv.not_ctorInfo ⟨_, hc⟩ hh

/-- **`tryEtaStructCore.WF` from the GC bridge.**

`WF_of_structEtaG`'s proof with **one line changed**: `refine (hiter a hlt hge ss).bind …` in
place of destructuring the pair and calling `isDefEq.WF`.  Measured axiom set: **identical to
`WF_of_structEtaG`'s**, and the same four holes (`weakN_iff`, `forallE_inv_stratified`,
`rigidShapeUniqNS`, `NormalEq.descend`), and the cone is the **same size**, 12439 — the GC
bridge's statement adds the executable `isDefEq` and the `RecM.WF`/`Methods.WF` layer, all of
which `WF_of_structEtaG`'s own proof already reached.

**Read this together with `EtaStructSpineGC`'s docstring, which says what it is worth.**  The
statement is strictly stronger than `WF_of_structEtaG` (weaker hypothesis, by `toCall`), and its
hypothesis is not refuted at a member of a mutual block.  It is still not satisfiable there,
because `isDefEq.WF` is the only producer of the conjunct and it asks for the refuted pair.  The
wall has moved from satisfiability to discharge; it has not come down. -/
theorem tryEtaStructCore.WF_of_structEtaGC {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hSE : c.venv.StructEtaG) (hbr : EtaStructSpineGC c e₁ e₂ e₁' e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold tryEtaStructCore
  split <;> [skip; exact .pure nofun]
  rename_i f us heq
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
  split <;> [skip; exact .pure nofun]
  rename_i fInfo hfi
  split <;> [skip; exact .pure nofun]
  rename_i hnum
  split <;> [skip; exact .pure nofun]
  rename_i hnrs
  obtain ⟨D, j, T, C, us', ps, args, B, hIS, hCname, hidx, hrec, hus, huswf, hps, hnp, hnf,
    hargl, hpsA, hty1, hF17, he₂eq, hctor, hB, hprojty, hiter⟩ := hbr ⟨us, heq⟩ hci hnum hnrs
  refine (inferType.WF he₁).bind fun _ _ _ ⟨_, _, _, ht1, _⟩ => ?_
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, _, _, ht2, _⟩ => ?_
  refine (isDefEq.WF ht1 ht2).bind fun b _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine (RecM.WF.forIn'Prefix
    (Inv := fun ys st _ => st.1 = none ∧ ∀ a ∈ ys,
      c.IsDefEqU (D.projTermG T C us' ps [] (a - hfi.numParams) j e₁')
        (args.getD (a - hfi.numParams) default))
    (Br := fun st _ => st.1 = some false)
    (pre := []) ?_ ⟨rfl, nofun⟩).bind fun r _ _ hr => ?_
  · intro ys a ha bb ss ⟨_, hb2⟩
    have hlt : a < e₂.getAppArgs.size := by simp [List.mem_range'] at ha; omega
    have hge : hfi.numParams ≤ a := by simp [List.mem_range'] at ha; omega
    refine (hiter a hlt hge ss).bind fun _ _ _ hres => ?_
    split
    · rename_i hrt
      refine .pure ⟨rfl, ?_⟩
      intro x hx
      simp at hx
      rcases hx with hx | rfl
      · exact hb2 x hx
      · exact hres hrt
    · exact .pure rfl
  · rcases hr with ⟨h1, h2⟩ | h1
    · rw [h1]
      refine .pure fun _ => ?_
      have hkey : ∀ k, k < C.fields.length →
          c.IsDefEqU (D.projTermG T C us' ps [] k j e₁') (args.getD k default) := by
        intro k hk
        have hmem : hfi.numParams + k ∈
            [] ++ List.range' hfi.numParams [hfi.numParams:e₂.getAppArgs.size].size := by
          simp [List.mem_range']
          have hsz : e₂.getAppArgs.size = hfi.numParams + hfi.numFields := by
            have h0 : e₂.getAppArgs.toList.length = e₂.getAppNumArgs := by
              rw [Expr.getAppArgs_toList_rev, List.length_reverse, ← Expr.getAppNumArgs_eq]
            simp only [Array.length_toList] at h0
            rw [h0]; simpa using hnum
          omega
        simpa using h2 _ hmem
      exact ⟨_, he₂eq ▸ hSE.congrProj hIS hidx hrec hus huswf hps hpsA hty1 hF17 hargl
        hprojty hkey hctor hB c.Ewf c.Δwf⟩
    · rw [h1]; exact .pure nofun

end TypeChecker.Inner

/-! ## Audit

**Axioms** (`#print axioms`, run with `Experimental/ConeJoin.lean` co-imported, which is also the
duplicate-name check).  Every declaration here has the **same axiom set as its narrow
counterpart**, declaration for declaration:

| declaration | axioms | narrow counterpart |
|---|---|---|
| `projAllG_eq_projAll`, `etaExpansionG_eq_etaExpansion` | `[propext, Quot.sound]` | — |
| `length_projAllG`, `projAllG_nil`, `etaExpansionG_of_no_fields`, `declEnv_etaExpansionG_eq` | `[propext]` | — |
| `StructEtaG.toStructEta`, `.unitLike`, `.congrSpine`, `empty_structEtaG` | `[propext, Quot.sound]` | `StructEta.congrSpine`, `.unitLike`: same |
| `StructEtaG.congrProj`, `.congrProj_at_projAllG` | `+ sorryAx, Classical.choice` | `StructEta.congrProj`, `.congrProj_at_projAll`: **identical** |
| `MutField.decl_WF`, `declEnv_IsStructureG`, `decl_not_isStructure`, `declEnv_structEtaG_premises`, `declEnv_structEtaG`, `projCore_arity_wrong_here` | `[propext, Classical.choice, Quot.sound]` | `MutNonRec.decl2_WF`: same |
| `TrProj.isStructure`, `MutField.projCoreG_arity_right_here`, `bCtor_field_prop` | `[propext, Quot.sound]` | — |
| `EtaStructSpine.toG` | `+ sorryAx, Classical.choice` | — |
| `tryEtaStructCore.WF_of_structEtaG` | `+ sorryAx, Classical.choice, Lean.Expr.eqv_eq, Lean.Level.instLawfulBEqLevel, Lean.Syntax.structEq_eq` | `WF_of_structEta`: **identical, including the three `Lean.*` ones** |
| `EtaStructSpineG.toCall`, `EtaStructSpineGC.today` | `[propext, Classical.choice, Quot.sound, Lean.Expr.eqv_eq, Lean.Level.instLawfulBEqLevel, Lean.Syntax.structEq_eq]` — **no `sorryAx`**, but three **frozen** axioms of guard 1's whitelist, all via `isDefEq.WF` | — |
| `tryEtaStructCore.WF_of_structEtaGC` | `+ sorryAx, Classical.choice, Lean.Expr.eqv_eq, Lean.Level.instLawfulBEqLevel, Lean.Syntax.structEq_eq` | `WF_of_structEtaG`: **identical, axiom for axiom and hole for hole** |

**Hole cones** (transitive `getUsedConstantsAsSet` sweep, filtered to declarations whose value
mentions `sorryAx`).  **No new hole anywhere:**

| seed | cone | holes |
|---|---|---|
| `tryEtaStructCore.WF_of_structEta` | 12425 | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS`, `NormalEq.descend` |
| `tryEtaStructCore.WF_of_structEtaG` | 12439 | **the same four** |
| `EtaStructSpine.toG` | 8960 | `weakN_iff`, `forallE_inv_stratified` — both via `projTerm_hasType`, which is where the narrow bridge's own conjunct comes from |
| `VEnv.StructEta.congrProj` | 3496 | `forallE_inv_stratified` |
| `VEnv.StructEtaG.congrProj` | 3507 | **the same one** |
| `VEnv.StructEta.congrProj_at_projAll` | 3498 | `forallE_inv_stratified` |
| `VEnv.StructEtaG.congrProj_at_projAllG` | 3509 | **the same one** |
| `VEnv.StructEtaG.congrSpine` | 1567 | none |
| `VEnv.StructEtaG.toStructEta` | 1929 | none |
| `VEnv.StructEtaG.unitLike` | 820 | none |
| `VEnv.empty_structEtaG` | 1183 | none |
| `MutField.decl_WF` | 3714 | none |
| `MutField.declEnv_structEtaG_premises` | 3795 | none |
| `MutField.projCore_arity_wrong_here` | 1481 | none |
| `MutField.projCoreG_arity_right_here` | 1528 | none |
| `TrProj.isStructure` | 690 | none |
| `trProj_at_MutField_needs_other_block` | 993 | none |
| `EtaStructSpineG.toCall` | 9592 | none |
| `EtaStructSpineGC` (the definition) | 3130 | none — and it contains **no `TrProj`, no `TrExprS`, no `VEnv.IsStructure`**, where `EtaStructSpineG`'s cone contains all three |
| `tryEtaStructCore.WF_of_structEtaGC` | 12439 | **the same four as `WF_of_structEtaG`**, and the same cone size |

`StructEtaG.congrProj`'s single hole is `HasArgsDF.ofMap`'s, i.e. the narrow `congrProj`'s, and the
G-version's cone is eleven constants larger purely because `projTermG` is a longer definition than
`projTerm`.

**Firing status, per instrument 7 of `docs/vacuity-ledger.md` §0 — per declaration, because it is
not uniform.**

* *Fires today, non-vacuously, at the configuration that matters:*
  `MutField.declEnv_structEtaG`.  Every premise of `StructEtaG` is discharged outright at
  `MutField.declEnv` — `IsStructureG`, the three `rfl` side conditions, the level and parameter
  lengths, the `HasArgs`, the `HasType`, and the F17 clause in its *small-elimination* branch
  (`isLE = false`, so `.inl` is unavailable) — so the only hypothesis left is
  `H : declEnv.StructEtaG` itself, and the conclusion is a specific `IsDefEq`.
  `declEnv_structEtaG_premises` is that audit as one conjunction; its last three conjuncts are the
  point (two types, index `1`, one field), and `decl_not_isStructure` is the matching negative.
* *Fires today, hole-free:* `TrProj.isStructure` (case analysis, no hypotheses beyond the
  derivation), `trProj_at_MutField_needs_other_block`,
  `MutField.projCore_arity_wrong_here`/`projCoreG_arity_right_here` (both closed by `rfl`/`decide`,
  no hypotheses at all), `StructEtaG.toStructEta`, `empty_structEtaG`, and the four collapse/shape
  lemmas.
* *Fires today only under a hypothesis that is itself satisfiable:* `StructEtaG.unitLike`,
  `.congrSpine`, `.congrProj`, `.congrProj_at_projAllG`.  Their non-`StructEtaG` hypotheses are
  the constructor's declared telescope, the `HasArgsDF`, and `hprojty`; `hprojty` is the one with
  no producer at a widened block (wall 2), so these are *assemblies awaiting an ingredient*, not
  vacuous statements — `congrProj_at_projAllG` is the round-trip test that they are wired
  correctly.
* **Does *not* fire today, and this is structural:** `tryEtaStructCore.WF_of_structEtaG` and
  `EtaStructSpine.toG`.  The first takes `c.TrExprS e₁ e₁'`, which carries `AddInduct`'s emptiness
  in, so its `.ctorInfo` arm is unreachable *in the proof layer* until the flip — the same status
  as `WF_of_structEta`, and it is worth having for the same reason: `TrEnv.not_ctorInfo` appears
  nowhere in it, so it survives the flip verbatim.  The second takes `EtaStructSpine c`, which is
  trivially true today (its premise asks for a `.ctorInfo` under the head of a translated term)
  and unproved after the flip; it is here as the polarity certificate, not as a usable step.

**Per-consumer satisfiability for the weakened hypothesis** (`EtaStructSpineG` is weaker than
`EtaStructSpine`, by `EtaStructSpine.toG`).  It has exactly **one** consumer,
`tryEtaStructCore.WF_of_structEtaG`, and the honest reading is:

* *today*: satisfiable for every `c`, vacuously, exactly as `EtaStructSpine` is;
* *after the flip, at a singleton non-recursive block*: satisfiable iff `EtaStructSpine` is —
  `EtaStructSpine.toG` gives one direction, and the added `hprojty` conjunct is discharged by
  `projTerm_hasType`, so nothing is lost;
* *after the flip, at a member of a mutual block*: **not** satisfiable, and this is wall 3
  (`TrProj.isStructure`, `trProj_at_MutField_needs_other_block`).  This is the one place the
  positive-field repair differs from the zero-field one, where `UnitLikeBridgeG` *is* satisfiable
  there (`MutNonRec.decl2Env_unitEta_premises`).

So the count of residual hypotheses of `tryEtaStructCore.WF` is unchanged at **two**, one of them
is no longer refuted by the mutual-block witness, and the remaining obstruction has moved from
`IsStructure` in the bridge to `IsStructure` in `TrProj`.

**And the `GC` block, labelled honestly** (ledger row 107).  `EtaStructSpineGC` /
`EtaStructSpineG.toCall` / `WF_of_structEtaGC` replace the per-iteration `TrExprS` pair by the
`isDefEq` call's own postcondition, which is the only thing `WF_of_structEtaG` ever reads off it.

* *What is measured*: `toCall` is hole-free; `WF_of_structEtaGC`'s axiom set and hole set are
  identical to `WF_of_structEtaG`'s; and `EtaStructSpineGC`'s cone mentions none of `TrProj`,
  `TrExprS`, `VEnv.IsStructure`, so `TrProj.isStructure` cannot refute it.
* *What that is worth*: **a refuted hypothesis becomes a not-refuted one.**  It is a
  **relocation of the wall from the bridge's satisfiability to the bridge's discharge**, not a
  repair: `isDefEq.WF` is the only WF lemma for `isDefEq`, its contract still asks for a
  `TrExprS` per argument, and so the only route to the GC conjunct is `toCall` — from the very
  pair that is refuted.  **No proof fires that did not fire before.**
* *Instrument 7, both directions.*  Satisfiability: `EtaStructSpineGC.today` proves the
  hypothesis holds for every `c` and every translated `s`, vacuously, by `TrEnv.not_ctorInfo` —
  so `WF_of_structEtaGC` is not vacuous as an implication, and its one remaining hypothesis is
  `c.venv.StructEtaG`.  The dual (a weakened hypothesis that is trivially true): `RecM.WF` is
  partial correctness and quantifies over `Methods.WF`, so the conjunct is also met by a call
  that *throws* — but `Methods.WF` is inhabited (`Methods.withFuel.WF`), so the quantifier is
  not empty and the conjunct is not trivially true.  The one qualifier the swap needs: the cone
  does contain `TypeChecker.Methods.WF`, whose **fields** mention `c.TrExprS` in *negative*
  position; "mentions no translation relation" is a claim about what the predicate asserts. -/

end Lean4Lean
