import Lean4Lean.Theory.Inductive.NestedBuild

/-!
# Ledger row 117e: `VNestedOcc.field` at the redex the nested elimination manufactures

**This file changes no implementation, weakens no statement, and reinstates no `Canonical`.**
It is the measurement-and-repair round for ledger row **117e**, whose assignment was: *"`Built`
is still false at `Lean.Json`, and `member` (not canonicity) is the failing clause."*

## What the round actually found — three corrections to that assignment

1. **`VInductDecl'.Built` alone is NOT false**, at `Lean.Json` or anywhere else.  `Built.member`
   is `T = (occ j).member D.header R`, and `D`'s **companion** members are pinned by *nothing
   else*: `TrIndDeclN.trCtors`/`ctorName_own` are quantified over `types[j]? = some t`, i.e. over
   the *user's* members only, and `VInductDecl'.ctorConstsCR`/`typeConstsC` **filter the
   companion members out**.  So a caller may take `D.types[j]` to *be* the built member, and
   `member` then holds by `rfl` — which is exactly what `mr_member_built` does at the witness
   below.  `Built` is **un-refuted**, not true (`SemResidue.member` is a hypothesis of every
   bridge, with no producer in general — see the verdict section).
2. **The failing conjunct is `Built.member` *together with* `VIndField.WF.pos`'s `none`
   branch**, i.e. `VEnv.AddNestedB`'s first two conjuncts jointly.  `VNestedOcc.field` computes
   `recArg = none` at the manufactured redex (`mr_field1`, and abstractly
   `field_eq_none_branch` + `recog_none_of_lamHead`), and the `none` branch of `pos` then needs a
   **block-free** `A` definitionally equal to a term whose β-normal form is the freshly declared
   block constant — `CGMEscape` (`Verify/Inductive/CanonGapMeasure.lean` §6) back verbatim.
   `built_wf_forces_escape` proves this.  **So ruling 116d's "no Church–Rosser, no escape
   hypothesis" is true of a *hand-written* block, where one may record `recArg = some r`
   (`ROWit.ro_field_WF`), and false at the *built* companion member, where `field` decides
   `recArg` and decides it `none`.**
3. **There is a second, *unconditional* refutation, and it is about the recursor, not the
   field.**  Lean's own kernel gives the manufactured redex field an **induction hypothesis**:
   `isRecArg` and `mkRecInfos.loopUArgs` both read `whnf` of the stored domain
   (`Lean4Lean/Inductive/Add.lean`), so the stored companion recursor's minor premise is
   `(k : Prop) → (a : (fun x => MJ) k) → motive_1 a → motive_2 (MDep.node k a)` — **three**
   binders.  With `recArg = none` the specification computes **two** (`mr_minor_arity_none`
   vs `mr_minor_arity_ground`).  `VInductDecl'.recConstsR` does **not** filter `K`, so that
   type is *declared*, and `AddInductStagesR`'s third stage carries a `TrConstant`, which goes
   through `TrExprS` and has no defeq slack.  This needs no escape at all.

## The repair, and its price — **LANDED**

The repair is now `VNestedOcc.field` itself (`Theory/Inductive/NestedBuild.lean`); this file
retains the measurement, the witness and the refutations, and §3 carries the name map for anyone
following a ledger citation to `MRedex.fieldB`.  `field` is `fieldO` — the pre-repair function,
kept beside it so conservativity stays a statement with content — plus **one** change: when the
recogniser fails on the substituted type it is asked again on the type's **head-β contraction**,
and if *that* fires the field is stored **verbatim** (`type := S`, the redex) with
`recArg := some r`.  Consequences, all proved:

* it is **conservative**: `field = fieldO` wherever the first recognition succeeds
  (`VNestedOcc.field_eq_fieldO_of_some`) or the second fails (`field_eq_fieldO_of_none`);
* `field_typeR` holds with the **same four hypotheses** as `fieldO_typeR` — the new branch is
  `VIndRestore.restore_noK` against `Built.fields_noK`, so ruling 116d's cost does not grow;
* `VNestedOcc.bindersIndep` stays **unconditional**: `field_binders` gives the two readings of
  `r.binders` and `VExpr.skips_betaHead` carries independence across the contraction;
* at the witness the residue of `VIndField.WF.pos` is **one `IsDefEq.beta`** (`mr_pos_beta`),
  which is what 116d promised and what the built member did not deliver;
* the minor-premise arity now matches Lean's stored recursor (`mr_minor_arity_someB`), and the
  built companion member moved from `mrAuxNode` to `mrAuxNodeB` (`mr_member_built`,
  `mr_member_not_built_old`).

**It is a specification-side change only** — the implementation is untouched and the stored field
type is *more* faithful than before, not less — so **it is not a divergence and needs no
`divergences.md` entry**.  What it cost is stated and machine-checked: `VIndCtor.Canonical`
becomes **FALSE** at the repaired companion constructor (`mr_auxNodeB_not_canonical`, and
`mr_ctor_built` shows that constructor is the one the construction produces), so
`VNestedOcc.ctor_Canonical`, `VNestedOcc.member_Canonical` and `VInductDecl'.Built.canonical` are
**deleted**.

Where their four consumers went, and this is the part worth checking rather than trusting:

* `VEnv.ctorConstsCR_wf_of_np_zero'` (`Theory/Inductive/RestoreBridge.lean`) took
  `hcanon : D.Canonical` and now takes `hcanon : D.CanonicalOwn K`.  This is a **weakening of a
  hypothesis, not a burden moved into one**: the proof feeds `hcanon` to
  `VEnv.ctorConstsCR_wf_of_substC`'s `hbridge`, which is quantified over `T.name ∉ K`, so the
  companion members were never in its range.  `VInductDecl'.CanonicalOwn.on` is the one-line
  re-keying from `getD` to `types[j]?`.
* `nfnAux_canonicalOwn` (`NestedBuild.lean`) and `nfnAuxDirty_canonicalOwn`
  (`RestoreBridge.lean`) applied `member_Canonical` at the companion index.  They did not need
  to: that index's name is in `nfnK`, so `CanonicalOwn`'s `∉ K` premise refutes the branch.
* `ElimNestedInductive.Result.RestoreData.mkRestore_canonical`
  (`Verify/Inductive/NestedRestoreWit.lean`) and its `OccData` wrapper
  (`Verify/Inductive/NestedOccData.lean`) concluded `D.Canonical` from `CanonicalOwn`.  Both had
  **zero consumers** and are deleted rather than restated, the conclusion being what became false.

## Coverage, measured rather than assumed

`Verify/Inductive/MemberRedexScan.lean` §2 classifies every auxiliary constructor field in the
running environment by three predicates: the **syntactic** one `VIndRestore.recogAt` uses, the
**head-β** one `fieldB` adds, and the **whnf** loop `AddInductive.isRecArg` itself uses.  Result:
**47** safe blocks with a nested-shaped field, **790** auxiliary constructor fields;
**3** fields in **3** blocks are misclassified today (`Lean.Json`, `Lean.PrefixTreeNode`, and this
file's own `MRWit.MJ`); **3 of 3** are fixed by one head-β step; **0** residual.

So the repair is adequate on the population that matters, and it is *narrower than `isRecArg` in
principle*: a redex sitting **under a binder** (`∀ y, (fun x => I) y`) or one that needs **δ** would
need `isRecArg`'s full loop — whnf at every pi-stripping step — and `fieldB` as written would miss
it.  That residue is **named, not measured away**, and it is the one place a stronger `fieldB`
would be needed.

## What the repair still owes, named

`mr_pos_beta` discharges `VIndField.WF.pos`'s last conjunct **at the witness**, by one
`IsDefEq.beta`.  The *general* statement — `env.IsDefEqType D.uvars Γ S (betaHead S)` for a
well-typed `S` — is **not proved here**: it is `IsDefEq.beta` iterated along the spine, and getting
the domain and codomain of each step needs application inversion.  So the repair's `WF.pos`
obligation is discharged concretely and reduced-but-not-closed in general.  Stating that is the
point: an unproved positive marked as such is cheaper than a green theorem hiding it.

**Instrument caveat, new and load-bearing.**  `vconst(type_of% ·)` **β-reduces**: the node minor
premise of `MJ.rec_1` comes back with the field domain `MJ`, while the type Lean *stores* has the
redex `(fun x => MJ) k` there (`mr_vconst_beta_reduces`; the stored form is printed by
`Verify/Inductive/MemberRedexScan.lean`).  So the tree's usual ground-truth anchor is **blind in
exactly this corner**, and every claim here that depends on the stored form is anchored on
`piArity` — which β-reduction of a *domain* cannot change — or on an executed read of the
environment, never on a `vconst` equation.
-/

namespace Lean4Lean
namespace MRedex

open VExpr (mkPi mkLams mkApp bvars instAll splitPis betaSpine betaHead)

/-! ## 0. Head β-contraction

`VExpr.betaSpine` / `VExpr.betaHead` **moved to `Theory/Inductive/NestedBuild.lean`** when the
repair landed, because `VNestedOcc.field` now calls them; they are only `open`ed here.
`VExpr.skips_betaHead` — independence survives head β — went with them, and it is what keeps
`VNestedOcc.bindersIndep` unconditional (see §3). -/

/-! ## 1. The recogniser is blind to a redex-headed field

`VIndRestore.recogAt` splits `S`'s leading pis and asks whether what remains is
`.const (R.tyName k) (R.tyLvls k)` applied to a spine.  A β-redex's spine head is a `.lam`, so
the test fails at *every* member — no arithmetic, no arity, no levels involved. -/

theorem recogAt_none_of_lamHead {R : VIndRestore} {i k : Nat} {S A b : VExpr}
    (h : (splitPis S.piArity S).2.spineFn = .lam A b) : R.recogAt i k S = none := by
  unfold VIndRestore.recogAt
  simp only []
  rw [if_neg]
  rintro ⟨h1, -⟩
  rw [h] at h1
  exact absurd h1 nofun

theorem recog_none_of_lamHead {R : VIndRestore} {nm i : Nat} {S A b : VExpr}
    (h : (splitPis S.piArity S).2.spineFn = .lam A b) : R.recog nm i S = none := by
  rw [VIndRestore.recog]
  exact List.findSome?_eq_none_iff.2 fun k _ => recogAt_none_of_lamHead h

/-- …so the **pre-repair** field function takes the `none` branch: the stored type is the redex
verbatim, and `recArg` is `none`.  The first half is faithfulness (the implementation stores
exactly this); the second half was the defect.

Since the repair landed, `VNestedOcc.field` needs **both** recognitions to fail before it lands
here (`VNestedOcc.field_eq_none_branch`), and that extra hypothesis is exactly the *residue* of
the repair: a redex under a binder, or one needing δ.  Measured empty in the running environment
(row 119c), and named rather than measured away. -/
theorem fieldO_eq_none_branch {N : VNestedOcc} {H : VIndHeader} {R : VIndRestore} {i : Nat}
    {F₀ : VIndField}
    (h : R.recog H.nm i (VExpr.instAll (F₀.type.instL N.lvls) N.args i) = none) :
    N.fieldO H R i F₀ =
      { type := VExpr.instAll (F₀.type.instL N.lvls) N.args i,
        lvl := F₀.lvl.inst N.lvls, recArg := none } := by
  rw [VNestedOcc.fieldO]; simp only [h]

/-! ## 2. What that costs, as a theorem: the escape is back at the built member

`VIndField.WF.pos`'s `none` branch is `∃ A, D.NoBlock A ∧ IsDefEqType Γ F.type A`.  At the
manufactured redex `F.type` β-reduces to a *block* constant, so this is `CGMEscape`
(`Verify/Inductive/CanonGapMeasure.lean` §6) — the residue ruling 116d was adopted to remove.

Stated with the escape as a **conclusion** and then, in `built_wf_of_escape_false`, as a
**hypothesis**: ledger row 116g's discipline, so that the residue is visible to a reader rather
than hidden inside a green axiom set. -/
theorem built_wf_forces_escape {env env₁ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Lean.Name} {occ : Nat → VNestedOcc}
    (hb : D.Built R K env occ) (hwf : D.WF env)
    (hst : env.addIndTypes D = some env₁)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {C₀ : VIndCtor} (hC₀ : C₀ ∈ (occ j).src.ctors)
    {i : Nat} {F₀ : VIndField} (hF₀ : C₀.fields[i]? = some F₀)
    (hnone : R.recog D.header.nm i
      (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i) = none)
    (hnone2 : R.recog D.header.nm i
      (betaHead (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i)) = none) :
    ∃ A, D.NoBlock A ∧ env₁.IsDefEqType D.uvars
      ((((((occ j).ctor D.header R C₀).fields.take i).map (·.type)).reverse) ++ D.params.reverse)
      (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i) A := by
  have hmem : (occ j).ctor D.header R C₀ ∈ T.ctors := by
    rw [hb.member j T hT hK, VNestedOcc.member]
    exact List.mem_map_of_mem hC₀
  have hCwf := hwf.ctors env₁ hst j T hT _ hmem
  have hFi : ((occ j).ctor D.header R C₀).fields[i]? = some ((occ j).field D.header R i F₀) := by
    rw [VNestedOcc.ctor, (occ j).getElem?_fieldsFrom D.header R 0 C₀.fields i, hF₀,
      Nat.zero_add]
    rfl
  have hfwf := hCwf.fields i _ hFi
  have hf := VNestedOcc.field_eq_none_branch (N := occ j) (H := D.header) (R := R) (i := i)
    (F₀ := F₀) hnone hnone2
  have := hfwf.pos
  rw [show ((occ j).field D.header R i F₀).recArg = none from by rw [hf]] at this
  rw [show ((occ j).field D.header R i F₀).type
      = VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i from by rw [hf]] at this
  exact this

/-- The same fact contrapositively: **if the escape is false, `Built ∧ WF` is false** — so
`VEnv.AddNestedB` is refuted at any block with a redex-headed companion field, modulo exactly one
named `Prop` and nothing else. -/
theorem built_wf_of_escape_false {env env₁ : VEnv} {D : VInductDecl'} {R : VIndRestore}
    {K : List Lean.Name} {occ : Nat → VNestedOcc}
    (hst : env.addIndTypes D = some env₁)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {C₀ : VIndCtor} (hC₀ : C₀ ∈ (occ j).src.ctors)
    {i : Nat} {F₀ : VIndField} (hF₀ : C₀.fields[i]? = some F₀)
    (hnone : R.recog D.header.nm i
      (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i) = none)
    (hnone2 : R.recog D.header.nm i
      (betaHead (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i)) = none)
    (hesc : ¬ ∃ A, D.NoBlock A ∧ env₁.IsDefEqType D.uvars
      ((((((occ j).ctor D.header R C₀).fields.take i).map (·.type)).reverse) ++ D.params.reverse)
      (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i) A) :
    ¬ (D.WF env ∧ D.Built R K env occ) :=
  fun ⟨hwf, hb⟩ => hesc (built_wf_forces_escape hb hwf hst hT hK hC₀ hF₀ hnone hnone2)

/-! ## 3. The repair — **landed**, in `Theory/Inductive/NestedBuild.lean`

`fieldB` and its four lemmas used to be defined here as a *proposal*.  They are gone: the body
is now `VNestedOcc.field` itself, and the lemmas moved with it, so that nothing in the tree
computes the pre-repair reading by accident.  The map, for anyone following a ledger citation:

| was, here | is, in `NestedBuild.lean` |
|---|---|
| `MRedex.fieldB` | `VNestedOcc.field` (the definition) |
| — | `VNestedOcc.fieldO` (the *pre-repair* function, kept so conservativity has content) |
| `MRedex.fieldB_eq_field_of_some` | `VNestedOcc.field_eq_fieldO_of_some` |
| `MRedex.fieldB_eq_field_of_none` | `VNestedOcc.field_eq_fieldO_of_none` |
| `MRedex.fieldB_new_branch` | `VNestedOcc.field_new_branch` |
| `MRedex.fieldB_typeR` | `VNestedOcc.field_typeR` (the old one is `fieldO_typeR`) |
| `MRedex.field_eq_none_branch` | `VNestedOcc.field_eq_none_branch` (**two** hypotheses now) |
| `MRedex.betaSpine` / `betaHead` | `VExpr.betaSpine` / `VExpr.betaHead` |

Two things the move cost, both discharged rather than deferred:

* `VNestedOcc.bindersIndep` read `r.binders` off `splitPis` of the *substituted* type, and the
  new branch's `r` comes from the head-β contraction.  `VNestedOcc.field_binders` states the
  disjunction and `VExpr.skips_betaHead` closes the new side, so the clause stays
  **unconditional** — no hypothesis was added to it.
* `VIndCtor.Canonical` is now false at the repaired constructor, so `VNestedOcc.ctor_Canonical`,
  `VNestedOcc.member_Canonical` and `VInductDecl'.Built.canonical` are **deleted**.  See §4. -/

/-! ## 4. The price, as a theorem: `VIndCtor.Canonical` becomes false

`VNestedOcc.ctor_Canonical` used to be *true with no hypotheses* — and that was precisely
because `fieldO` reports `recArg = none` at the redex, so `Canonical` had nothing to check there.
The repair records the field as recursive, and then the stored type is a β-redex while
`r.canonType D i` never is.  This is ledger row 116g's trap in its cleanest form: the
hypothesis-free green theorem was green because the definition mis-modelled the kernel. -/

theorem spineFn_canonType (r : VIndRecArg) (D : VInductDecl') (i : Nat) :
    ∀ A b, (r.canonType D i).spineFn ≠ .lam A b := by
  intro A b
  cases hb : r.binders with
  | cons B Bs => rw [VIndRecArg.canonType, hb, VExpr.mkPi]; exact nofun
  | nil =>
    rw [VIndRecArg.canonType, hb, VExpr.mkPi, VIndRecArg.canonResult, VInductDecl'.tyApp,
      VExpr.spineFn_mkApp, VExpr.spineFn_const]
    exact nofun

/-- **A canonical recursive-field type is never redex-headed** — at any `D.np`, any `r.args`,
any block: the obstruction is the spine head.  (The `Theory/`-side counterpart of
`CGMAbstract.cgm_canonType_ne_redex`, which lives in `Verify/` and cannot be imported here.) -/
theorem canonType_ne_of_lamHead {D : VInductDecl'} {r : VIndRecArg} {i : Nat} {e A b : VExpr}
    (h : e.spineFn = .lam A b) : r.canonType D i ≠ e :=
  fun he => spineFn_canonType r D i A b (by rw [he, h])


/-! ## 5. The witness: the real shape, from the empty environment

`MDep`/`MJ` is `CGMNestWit.cgmDep`/`cgmJ` (`Verify/Inductive/CanonGapMeasure.lean` §5) as an
actual Lean declaration, so **Lean's own kernel** runs the nested elimination and stores the
companion recursor `MJ.rec_1`.  It is the same pattern as `Lean.Json`/`Lean.PrefixTreeNode`
(both nest through `Std.DTreeMap.Internal.Impl (α) (β : α → Type v)`, whose `inner` constructor
has a field `β k`), reproduced small enough for `decide`.

`MDep`'s own block is transcribed and checked against the environment first — three `rfl`s
including its recursor — so a later mismatch is a fact about the companion member and not about
the transcription. -/

namespace MRWit

inductive MDep (α : Type) (β : α → Type) : Type where
  | node : (k : α) → β k → MDep α β

/-- A perfectly ordinary nested inductive: nothing the user writes is a redex. -/
inductive MJ : Type where
  | obj : MDep Prop (fun _ => MJ) → MJ

/-! ### `MDep`'s block, anchored on the environment -/

def mrNode : VIndCtor where
  name := ``MDep.node
  params := [.sort (.succ .zero), .forallE (.bvar 0) (.sort (.succ .zero))]
  fields :=
    [{ type := .bvar 1, lvl := .succ .zero, recArg := none },
     { type := .app (.bvar 1) (.bvar 0), lvl := .succ .zero, recArg := none }]
  args := []

def mrDepType : VIndType where
  name := ``MDep
  type := .forallE (.sort (.succ .zero))
    (.forallE (.forallE (.bvar 0) (.sort (.succ .zero))) (.sort (.succ .zero)))
  indices := []
  ctors := [mrNode]

def mrDepDecl : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero), .forallE (.bvar 0) (.sort (.succ .zero))]
  lvl := .succ .zero
  isLE := true
  types := [mrDepType]

example : mrDepType.type = (vconst(type_of% @MDep)).type := rfl
example : mrNode.type mrDepDecl 0 = (vconst(type_of% @MDep.node)).type := rfl
example : mrDepDecl.recType 0 = (vconst(type_of% @MDep.rec)).type := rfl

/-! ### `MJ`'s auxiliary block

`ElimNestedInductive.run` produces members `[MJ, _nested.MDep_1]`; the companion's `node`
constructor has field `1` stored as the β-redex `(fun x : Prop => MJ) #0`, whose head-β is the
**own** member `MJ`.  `mrAux` is parameterised by that constructor so that the two candidate
readings of the field can be compared side by side and nothing else moves. -/

def mrNestedName : Lean.Name := `_nested.MDep_1

/-- The field the elimination manufactures: `(fun x : Prop => MJ) #0`. -/
def mrRedex : VExpr := .app (.lam (.sort .zero) (.const ``MJ [])) (.bvar 0)

/-- The companion constructor **as `VNestedOcc.field` computes it today**. -/
def mrAuxNode : VIndCtor where
  name := `_nested.MDep_1.node
  params := []
  fields :=
    [{ type := .sort .zero, lvl := .succ .zero, recArg := none },
     { type := mrRedex, lvl := .succ .zero, recArg := none }]
  args := []

/-- …and **as `fieldB` computes it**: the same stored type, recorded as recursive. -/
def mrAuxNodeB : VIndCtor where
  name := `_nested.MDep_1.node
  params := []
  fields :=
    [{ type := .sort .zero, lvl := .succ .zero, recArg := none },
     { type := mrRedex, lvl := .succ .zero,
       recArg := some { binders := [], idx := 0, args := [] } }]
  args := []

def mrObj : VIndCtor where
  name := ``MJ.obj
  params := []
  fields := [{ type := .const mrNestedName [], lvl := .succ .zero,
               recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

def mrAux (Cn : VIndCtor) : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := true
  types :=
    [{ name := ``MJ, type := .sort (.succ .zero), indices := [], ctors := [mrObj] },
     { name := mrNestedName, type := .sort (.succ .zero), indices := [], ctors := [Cn] }]

def mrK : List Lean.Name := [mrNestedName]

def mrRestore : VIndRestore where
  tyName j := if j = 1 then ``MDep else ``MJ
  tyLvls _ := []
  tyArgs j := if j = 1 then [.sort .zero, .lam (.sort .zero) (.const ``MJ [])] else []
  ctorName n := if n = `_nested.MDep_1.node then ``MDep.node else n
  recName n := if n = `_nested.MDep_1.rec then ``MJ.rec_1 else n

def mrOcc : VNestedOcc where
  decl := mrDepDecl
  idx := 0
  lvls := []
  args := [.sort .zero, .lam (.sort .zero) (.const ``MJ [])]
  auxName := mrNestedName
  ctorName n := if n = ``MDep.node then `_nested.MDep_1.node else n

/-- The user's member and its constructor are the ones the environment holds — the
transcription anchor for the *declared* half.  (Both are redex-free, so the `vconst` caveat of
the module docstring does not apply to them.) -/
example : ((mrAux mrAuxNode).types.getD 0 default).type = (vconst(type_of% @MJ)).type := rfl

theorem mr_obj_declared :
    (mrObj.typeR (mrAux mrAuxNode) mrRestore 0).substC
      (mrRestore.csubstTy (mrAux mrAuxNode) mrK) = (vconst(type_of% @MJ.obj)).type := rfl

example : (mrAux mrAuxNode).recUvars = (vconst(type_of% @MJ.rec)).uvars := rfl

/-! ### The defect, at the witness -/

/-- The substituted source field **is** the redex — `instantiateForallParams` has no β step. -/
theorem mr_subst_field1 :
    VExpr.instAll ((mrNode.fields.getD 1 default).type.instL mrOcc.lvls) mrOcc.args 1
      = mrRedex := rfl

/-- The recogniser fails, at every member. -/
theorem mr_recog_none : mrRestore.recog (mrAux mrAuxNode).header.nm 1 mrRedex = none := rfl

/-- **The pre-repair reading**: the built field was the redex with `recArg = none`. -/
theorem mr_fieldO1 :
    mrOcc.fieldO (mrAux mrAuxNode).header mrRestore 1 (mrNode.fields.getD 1 default)
      = { type := mrRedex, lvl := .succ .zero, recArg := none } := rfl

/-- **`Built.member` is SATISFIED here** — the companion member of `mrAux mrAuxNodeB` *is* the
value the construction computes, by `rfl`.  This was row 117e's first correction (`member` is not
the false clause) and it survives the repair verbatim, at the *other* candidate constructor:
before the repair `member` was satisfied at `mrAuxNode` and forced `recArg = none`; now it is
satisfied at `mrAuxNodeB` and forces `recArg = some r`, which is what Lean stores. -/
theorem mr_member_built :
    (mrAux mrAuxNodeB).types[1]? = some (mrOcc.member (mrAux mrAuxNodeB).header mrRestore) := rfl

/-- …and **the repair moved it**: the pre-repair member is no longer what the construction
computes.  So the change is a repair rather than a re-labelling — `mrAuxNode` was the reading
`mr_minor_arity_none` shows the kernel does *not* store. -/
theorem mr_member_not_built_old :
    (mrAux mrAuxNode).types[1]? ≠ some (mrOcc.member (mrAux mrAuxNode).header mrRestore) := by
  intro h
  exact absurd (congrArg (fun o : Option VIndType =>
      (((o.getD default).ctors.getD 0 default).fields.getD 1 default).recArg.isSome) h)
    (by decide)

/-! ### The second, unconditional route: the companion recursor's minor premise

Lean's stored `MJ.rec_1` gives the redex field an **induction hypothesis** — `isRecArg` and
`mkRecInfos.loopUArgs` both read `whnf` of the stored domain.  The `node` minor premise therefore
has **three** binders, and `recArg = none` computes **two**.

The comparison is on `piArity`, not on an expression: `vconst(type_of% ·)` β-reduces the *domain*
`(fun x => MJ) k` to `MJ` (`mr_vconst_beta_reduces`), and a domain's β-reduction cannot change how
many binders the premise has.  `Verify/Inductive/MemberRedexScan.lean` prints the stored `Expr`. -/

/-- **Ground truth**: three binders — `k`, the field, and its induction hypothesis. -/
theorem mr_minor_arity_ground :
    ((VExpr.splitPis 4 (vconst(type_of% @MJ.rec_1)).type).1.getD 3 default).piArity = 3 := rfl

/-- The specification, with `field`'s `recArg = none`: **two**.  So the type
`VInductDecl'.recConstsR` declares for the companion recursor is not the one the kernel stores,
and `AddIndConsts`' `TrConstant` — which goes through `TrExprS` — cannot bridge it. -/
theorem mr_minor_arity_none :
    ((VExpr.splitPis 4 ((mrAux mrAuxNode).recTypeR mrRestore 1)).1.getD 3 default).piArity
      = 2 := rfl

/-- …and with the repair: **three**. -/
theorem mr_minor_arity_someB :
    ((VExpr.splitPis 4 ((mrAux mrAuxNodeB).recTypeR mrRestore 1)).1.getD 3 default).piArity
      = 3 := rfl

theorem mr_recTypeR_ne :
    (mrAux mrAuxNode).recTypeR mrRestore 1 ≠ (mrAux mrAuxNodeB).recTypeR mrRestore 1 := by
  decide

/-- **The instrument caveat, machine-checked.**  `vconst` hands back `MJ` where the environment
stores `(fun x => MJ) #0`, so a `vconst` equation is *not* ground truth in this corner. -/
theorem mr_vconst_beta_reduces :
    (VExpr.splitPis 3
        ((VExpr.splitPis 4 (vconst(type_of% @MJ.rec_1)).type).1.getD 3 default)).1.getD 1 default
      = .const ``MJ [] := rfl

/-! ### The repair, at the witness -/

theorem mr_betaHead_redex : betaHead mrRedex = .const ``MJ [] := rfl

theorem mr_recogB :
    mrRestore.recog (mrAux mrAuxNodeB).header.nm 1 (betaHead mrRedex)
      = some { binders := [], idx := 0, args := [] } := rfl

/-- **`field` stores the redex and records it as recursive** — which is what the kernel does.
(Was `mr_fieldB1`, before the repair became the definition.) -/
theorem mr_field1 :
    mrOcc.field (mrAux mrAuxNodeB).header mrRestore 1 (mrNode.fields.getD 1 default)
      = { type := mrRedex, lvl := .succ .zero,
          recArg := some { binders := [], idx := 0, args := [] } } := rfl

/-- **The built constructor *is* `mrAuxNodeB`** — so `mr_auxNodeB_not_canonical` below is a
statement about what the construction now produces, not about a hand-written rival. -/
theorem mr_ctor_built : mrOcc.ctor (mrAux mrAuxNodeB).header mrRestore mrNode = mrAuxNodeB := rfl

/-- The canonical type of the recognised `r` is the block constant. -/
theorem mr_canonType :
    ({ binders := [], idx := 0, args := [] } : VIndRecArg).canonType (mrAux mrAuxNodeB) 1
      = .const ``MJ [] := rfl

/-- **The residue of `VIndField.WF.pos`'s `some` branch is one `IsDefEq.beta`** — ruling 116d's
promise, delivered at the *built* companion member rather than at a hand-written block.  The
context is the field context of field `1`: one earlier field, `Prop`, and no parameters. -/
theorem mr_pos_beta {env : VEnv}
    (hT : env.HasType 0 [VExpr.sort .zero, VExpr.sort .zero]
      (.const ``MJ []) (.sort (.succ .zero))) :
    env.IsDefEqType 0 [VExpr.sort .zero] mrRedex
      (({ binders := [], idx := 0, args := [] } : VIndRecArg).canonType (mrAux mrAuxNodeB) 1) :=
  ⟨.succ .zero, .beta hT (.bvar .zero)⟩

/-- …and its hypothesis is inhabited whenever the environment holds the member's own type
constant, which is what `VInductDecl'.WF.ctors`' staged environment supplies. -/
theorem mr_const_hasType {env : VEnv} {Γ : List VExpr}
    (hc : env.constants ``MJ = some ⟨0, .sort (.succ .zero)⟩) :
    env.HasType 0 Γ (.const ``MJ []) (.sort (.succ .zero)) :=
  .constDF hc nofun nofun rfl .nil

/-! ### The price -/

/-- **`VIndCtor.Canonical` is FALSE at the repaired companion constructor**, which by
`mr_ctor_built` is the one the construction produces.  It used to be `True` only because the
pre-repair `fieldO` reported `recArg = none` there, i.e. because the built member mis-modelled the
kernel — so `VNestedOcc.ctor_Canonical`, `member_Canonical` and `VInductDecl'.Built.canonical`
are **deleted**, and row 117d(iv)'s four consumers of the last one are re-plumbed.  Where they
went: `VEnv.ctorConstsCR_wf_of_np_zero'` now takes `D.CanonicalOwn K` (strictly weaker, and it
never applied the hypothesis at a companion member — its `hbridge` is quantified over
`T.name ∉ K`); `nfnAux_canonicalOwn` / `nfnAuxDirty_canonicalOwn` close the companion index from
that same `∉ K` premise; and both `mkRestore_canonical`s had zero consumers and are gone.  That is
the whole bill for the repair. -/
theorem mr_auxNodeB_not_canonical : ¬ mrAuxNodeB.Canonical (mrAux mrAuxNodeB) := by
  intro h
  exact absurd (h 1 _ _ rfl rfl) (by decide)

/-- **…and at the block level**, which is the form every downstream hypothesis is stated in
(`VInductDecl'.Canonical`, the `hcanon` of `Theory/Inductive/NestedRules.lean`'s iota section and
of `NestedTele.lean`, and a conjunct of the `AddInductive.run` specification in
`Verify/Inductive/RunIdentity.lean`).  So at a block whose companion carries a redex-headed
recursive field — three in the running environment, per
`Verify/Inductive/MemberRedexScan.lean` — **every one of those statements is vacuous**, and the
`run` specification's `D.Canonical` conjunct is unprovable.  That is the deletion's real cost,
and it is a cost the deletion *revealed* rather than created: the lemma that used to discharge it
was proving something false. -/
theorem mr_auxNodeB_block_not_canonical : ¬ (mrAux mrAuxNodeB).Canonical :=
  fun h => mr_auxNodeB_not_canonical (h 1 mrAuxNodeB
    (by rw [show (mrAux mrAuxNodeB).ctorsAll = [((0 : Nat), mrObj), (1, mrAuxNodeB)] from rfl]
        exact List.Mem.tail _ (List.Mem.head _)))

/-- …and the general reason, with no witness in it: a redex-headed stored type is never
`r.canonType`. -/
theorem mr_not_canonical_general {D : VInductDecl'} {C : VIndCtor} {i : Nat} {F : VIndField}
    {r : VIndRecArg} {A b : VExpr} (hF : C.fields[i]? = some F) (hr : F.recArg = some r)
    (hlam : F.type.spineFn = .lam A b) : ¬ C.Canonical D :=
  fun h => canonType_ne_of_lamHead hlam (h i F r hF hr).symm

end MRWit

/-! ## 5a. The existing witnesses and the negative control survive the repair

`field` differs from `fieldO` only where the recogniser fails *and* the head-β contraction is
recognised, so every `rfl`/`decide` in the tree that computes a field of a redex-free block is
untouched.  Checked here rather than asserted, at the two places that would notice:
`_nested.List_1.cons`'s two fields, and `listOcc_recog_field1_fails` — the **negative control**
that deletes the head generalisation and asserts the recogniser does *not* fire.  Its substituted
type is `.const`-headed, so `betaHead` is the identity on it and the second chance fails too: the
control still controls. -/

section
open InductiveDeclExamples

theorem listOcc_field_eq_fieldO_0 :
    listOcc.field ntreeAux.header ntreeRestore 0 (listCons.fields.getD 0 default)
      = listOcc.fieldO ntreeAux.header ntreeRestore 0 (listCons.fields.getD 0 default) := rfl

theorem listOcc_field_eq_fieldO_1 :
    listOcc.field ntreeAux.header ntreeRestore 1 (listCons.fields.getD 1 default)
      = listOcc.fieldO ntreeAux.header ntreeRestore 1 (listCons.fields.getD 1 default) := rfl

/-- **The negative control still fails under the second chance.** -/
theorem listOcc_betaHead_control :
    { ntreeRestore with tyArgs := fun _ => VExpr.bvars 0 1 }.recog ntreeAux.header.nm 1
        (betaHead (VExpr.instAll ((listCons.fields.getD 1 default).type.instL listOcc.lvls)
          listOcc.args 1))
      = none := rfl

end

/-! ## 6. Instrument 7 and its dual

**Instrument 7** (green because the hypotheses are unsatisfiable): `recogAt_none_of_lamHead`,
`recog_none_of_lamHead`, `fieldO_eq_none_branch`, and `NestedBuild.lean`'s
`VNestedOcc.field_eq_fieldO_of_some` / `field_eq_fieldO_of_none` / `field_new_branch` all have
hypotheses that are **discharged by `rfl` at a witness in this file** (`mr_recog_none`,
`mr_recogB`, and `listOcc_betaHead_control` for the `none`-`none` pair), so none is vacuous.
`spineFn_canonType`, `canonType_ne_of_lamHead` and every `mr_*` theorem outside
`mr_pos_beta`/`mr_const_hasType` are hypothesis-free.  `mr_pos_beta`'s single hypothesis is
inhabited by `mr_const_hasType`.

**Its dual** (green because the difficulty moved into an uninhabited hypothesis — ledger row
116g, and `BuiltFresh` the most recent instance):

* `built_wf_forces_escape` has the escape as a **conclusion**, and
  `built_wf_of_escape_false` restates it with the escape as a **hypothesis**, so the residue is
  visible on the page.  Neither is claimed to refute anything on its own: the escape is a
  `Prop` with **no known inhabitant and no known refutation**, and refuting it is
  Church–Rosser strength.  What is proved is that it is the *sole* residue of route A.
* **Both escape theorems gained a hypothesis when the repair landed** — `hnone2`, that the
  head-β contraction is *also* unrecognised.  That is not bookkeeping: it is the honest statement
  of what the repair bought.  The escape is no longer forced at the fields the repair covers, and
  it is still forced at the residue (a redex under a binder, or one needing δ), which is
  **measured empty in the running environment** but is not a theorem.  Read the pair as: route A
  is closed on the measured population and open in general.
* `VNestedOcc.field_typeR` gains **no** hypothesis over `fieldO_typeR`: same four, and the new
  branch consumes `hS` (= `Built.fields_noK`, row 117c's clause with no general producer) exactly
  as the old `some` branch already did.  So the repair does **not** enlarge ruling 116d's
  uninhabited-premise bill — but it does not shrink it either, and `fields_noK` still has no
  producer except `decide` at a concrete block.
* **`mr_auxNodeB_not_canonical` is the dual read in reverse**: `VNestedOcc.ctor_Canonical` was a
  hypothesis-free green theorem, and it was green *because* the pre-repair `none` branch made
  `Canonical` vacuous at the very field this file is about.  A green theorem can be worse than a
  red one when the definition it quantifies over is the wrong one.  It is now deleted, and the
  one thing that genuinely needed it — `ctorConstsCR_wf_of_np_zero'` — asks for `CanonicalOwn K`
  instead, i.e. **no burden moved into a hypothesis: the hypothesis got weaker.**
-/

/-! ## 7. Non-vacuity of the repair's own statements, at the degenerate instance

Ledger blindness 7: *a statement can be green because its hypotheses are unsatisfiable at the
degenerate instance — nil telescope, zero grade, empty context — while being perfectly good at the
general one.*  Every statement the repair added or changed is instantiated here, and the verdicts
are **not uniform**, which is the point of doing it.

`dgOcc` is the smallest occurrence that reaches `field` at all: zero universe parameters, **nil**
parameter telescope, **nil** nested spine, one member, one constructor, one field.  A zero-field
constructor would make `fieldsFrom` the empty list and every `field` statement vacuous by
emptiness, which is why the field is there. -/

namespace DgWit

def dgMk : VIndCtor where
  name := `DgJ.mk
  params := []
  fields := [{ type := .sort .zero, lvl := .succ .zero, recArg := none }]
  args := []

def dgType : VIndType where
  name := `DgJ
  type := .sort (.succ .zero)
  indices := []
  ctors := [dgMk]

def dgDecl : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := true
  types := [dgType]

def dgOcc : VNestedOcc where
  decl := dgDecl
  idx := 0
  lvls := []
  args := []
  auxName := `_nested.DgJ_1
  ctorName := id

def dgH : VIndHeader where
  uvars := 0
  params := []
  nm := 1
  names _ := `DgI

def dgR : VIndRestore where
  tyName _ := `DgJ
  tyLvls _ := []
  tyArgs _ := []
  ctorName := id
  recName := id

/-- The nil spine really is nil: `instAll e [] 0 = e`, so the degenerate instance is degenerate. -/
theorem dg_subst :
    VExpr.instAll ((dgMk.fields.getD 0 default).type.instL dgOcc.lvls) dgOcc.args 0
      = .sort .zero := rfl

/-- **`field_eq_fieldO_of_none` / `field_eq_none_branch`: hypotheses SATISFIABLE, and satisfied,
at the degenerate instance.**  Both recognitions fail on a `.sort`, and `betaHead` is the identity
on it. -/
theorem dg_recog_none :
    dgR.recog dgH.nm 0 (VExpr.instAll ((dgMk.fields.getD 0 default).type.instL dgOcc.lvls)
      dgOcc.args 0) = none := rfl

theorem dg_recog_betaHead_none :
    dgR.recog dgH.nm 0 (betaHead (VExpr.instAll
      ((dgMk.fields.getD 0 default).type.instL dgOcc.lvls) dgOcc.args 0)) = none := rfl

/-- …so the two conclusions **fire** here rather than being asserted of an empty hypothesis set. -/
theorem dg_field_eq_fieldO :
    dgOcc.field dgH dgR 0 (dgMk.fields.getD 0 default)
      = dgOcc.fieldO dgH dgR 0 (dgMk.fields.getD 0 default) :=
  dgOcc.field_eq_fieldO_of_none dg_recog_none dg_recog_betaHead_none

theorem dg_field_none_branch :
    dgOcc.field dgH dgR 0 (dgMk.fields.getD 0 default)
      = { type := .sort .zero, lvl := .succ .zero, recArg := none } :=
  dgOcc.field_eq_none_branch dg_recog_none dg_recog_betaHead_none

/-- …and the conclusion is **not** trivially true: it is an equation with a computed right-hand
side, and the *other* branch's value differs. -/
theorem dg_field_none_branch_nontrivial :
    ({ type := .sort .zero, lvl := .succ .zero, recArg := none } : VIndField)
      ≠ { type := .sort .zero, lvl := .succ .zero,
          recArg := some { binders := [], idx := 0, args := [] } } := by
  intro h
  exact absurd (congrArg (fun F : VIndField => F.recArg.isSome) h) (by decide)

/-- **`field_binders`: hypothesis NOT satisfiable at the degenerate instance**, and it cannot be —
`recArg = some r` needs a *recognised* field, and recognition needs a real block name in the
spine head, which a nil spine over a `.sort` cannot supply.  Recorded rather than hidden; the
witnesses that do satisfy it are `mr_field1` (the new branch) and `listOcc` field `1` (the old
one), both below/above. -/
theorem dg_field_recArg_none : (dgOcc.field dgH dgR 0 (dgMk.fields.getD 0 default)).recArg = none :=
  rfl

/-- **`VExpr.skips_betaHead`: hypothesis satisfiable *with the contraction non-trivial*.**  A
witness where `betaHead` is the identity would prove nothing, so the witness is the manufactured
redex itself: it mentions de Bruijn index `0` and nothing at `1`, and its contraction is the bare
block constant. -/
theorem dg_skips_redex : (MRWit.mrRedex).Skips 1 1 := rfl

theorem dg_skips_betaHead_fires : (betaHead MRWit.mrRedex).Skips 1 1 :=
  VExpr.skips_betaHead dg_skips_redex

theorem dg_betaHead_nontrivial : betaHead MRWit.mrRedex ≠ MRWit.mrRedex := by decide

end DgWit

/-! ### The verdicts, one line each

| statement | hypotheses at the degenerate instance | witness |
|---|---|---|
| `VNestedOcc.field_eq_fieldO_of_none` | **satisfiable**, satisfied | `DgWit.dg_field_eq_fieldO` |
| `VNestedOcc.field_eq_none_branch` | **satisfiable**, satisfied, conclusion non-trivial | `DgWit.dg_field_none_branch`, `dg_field_none_branch_nontrivial` |
| `VNestedOcc.field_eq_fieldO_of_some` | **not** satisfiable there (needs recognition) | fires at `listOcc` field `1`: `listOcc_field_eq_fieldO_1` computes the same equation by `rfl` |
| `VNestedOcc.field_new_branch` | **not** satisfiable there (needs a redex) | `MRWit.mr_recog_none` + `mr_recogB` ⟹ `mr_field1` |
| `VNestedOcc.field_binders` | **not** satisfiable there (`recArg = none`, `dg_field_recArg_none`) | fires at `mr_field1` and at `listOcc` field `1` |
| `VNestedOcc.field_typeR` | four hypotheses, all satisfied at `pfnOcc`/`nfnAux`/`nfnRestore`/`nfnK` — `hH` by `rfl`, `hown` by `nfnRestore_ownId`, `hnd` by `nfnAux_blockNames_nodup`, `hS` by `decide` | `NestedBuild.lean`'s `nfnAux_*` chain, which consumes it |
| `VExpr.skips_betaHead` | **satisfiable with the contraction non-trivial** | `DgWit.dg_skips_betaHead_fires` + `dg_betaHead_nontrivial` |
| `VInductDecl'.CanonicalOwn.on` | satisfied at `nfnAux` index `0` | `nfnAux_canonicalOwn` (its own proof) |
| `VEnv.ctorConstsCR_wf_of_np_zero'` (hypothesis **weakened** to `CanonicalOwn K`) | fully instantiated at two blocks | `nfnAux_ctorConstsCR_wf_general`, `nfnAuxDirty_obligationA` |
| `built_wf_forces_escape` / `built_wf_of_escape_false` (hypothesis **added**) | see below — **the one honest loss** | — |

**The one honest loss, stated rather than buried.**  Both escape theorems gained `hnone2`.  At the
`MRWit` block — the *only* witness in the tree where the escape was a live obligation — `hnone2`
is **FALSE** (`mr_recogB` says the contraction *is* recognised).  So `built_wf_forces_escape` is
now **vacuous at that witness**, which is exactly what the repair was for: the escape is no longer
forced there.  Its hypotheses remain jointly satisfiable elsewhere (any non-recursive block-free
field: both recognitions fail, `betaHead` is the identity), but at every such field the conclusion
is *discharged* by `A := F.type` rather than being a hole.  The reading to carry forward:

* the escape is forced only at a field whose type β-normalises to a block constant while **both**
  recognitions fail — i.e. a redex **under a binder** or one needing **δ**;
* that population is **measured empty** in the running environment
  (`Verify/Inductive/MemberRedexScan.lean`: 3 of 3 defects covered, residual 0), and *measured
  empty is not proved empty*;
* so route A is **closed on the measured population and open in general**, and the theorem that
  says so is now a conditional one.  This is the trade the repair makes, and it is a trade, not a
  free win.
-/


/-! ## 8. The measurement §7 could not make: `Built ∧ WF.pos`'s `none` branch, INSTANTIATED

§7 audits the `field`-level statements one at a time.  What it leaves with an empty witness
column is the row that matters most — `built_wf_forces_escape` / `built_wf_of_escape_false`,
whose hypothesis set is `D.Built ∧ D.WF ∧ addIndTypes ∧ hnone ∧ hnone2` **jointly**.  `DgWit`
cannot fill it: `dgOcc` carries no environment, so `Built.occurs` is unreachable there, and
`MRWit` cannot either, because at `MRWit` the repair makes `hnone2` **false** (`mr_recogB`).
So after the repair **neither existing witness reaches the branch**, and a green
`built_wf_forces_escape` might have been green for want of an instance.

This section supplies the instance.  `QJ`/`QN` is `PFn`/`NFn` (`NestedBuild.lean` Part 9) with
the higher-order field replaced by a **`Prop` field**: a companion field whose substituted type
is block-free and unrecognised, i.e. the one shape that lands in the repaired `none` branch.
The instance is degenerate in every coordinate the ledger's blindness 7 names — `D.params = []`
(nil telescope), `D.uvars = 0` (zero grade), and the field is field `0`, so its context is
`Γ = []` — and it is *not* degenerate by emptiness: the constructor has a second field, which
takes the `some` branch, so `fieldsFrom` is not the empty list and `Built.member` is an equation
between two-field constructors.

Result: `qn_pos_none_forced` is `built_wf_forces_escape` with **every** hypothesis discharged by
computation, so the branch is a real obligation and not an empty one; and `qn_escape_free` shows
its conclusion is *also* provable outright here, so the residue at this instance is **empty** —
which is what makes `qn_not_escape_false` true, i.e. **`built_wf_of_escape_false` has no witness
at this instance either.** -/

namespace QNWit

/-- The source block: a parameterised inductive whose *first* field is `Prop`. -/
inductive QJ (α : Type) where
  | mk : Prop → α → QJ α

/-- …nested. -/
inductive QN where
  | node : QJ QN → QN

def qjMk : VIndCtor where
  name := ``QJ.mk
  params := [.sort (.succ .zero)]
  fields :=
    [{ type := .sort .zero, lvl := .succ .zero, recArg := none },
     { type := .bvar 1, lvl := .succ .zero, recArg := none }]
  args := []

def qjType : VIndType where
  name := ``QJ
  type := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  indices := []
  ctors := [qjMk]

def qjDecl : VInductDecl' where
  uvars := 0
  params := [.sort (.succ .zero)]
  lvl := .succ .zero
  isLE := true
  types := [qjType]

example : qjType.type = (vconst(type_of% @QJ)).type := rfl
example : qjMk.type qjDecl 0 = (vconst(type_of% @QJ.mk)).type := rfl
example : qjDecl.recType 0 = (vconst(type_of% @QJ.rec)).type := rfl

def qnOcc : VNestedOcc where
  decl := qjDecl
  idx := 0
  lvls := []
  args := [.const ``QN []]
  auxName := `_nested.QJ_1
  ctorName n := if n = ``QJ.mk then `_nested.QJ_1.mk else n

def qnRestore : VIndRestore where
  tyName j := if j = 1 then ``QJ else ``QN
  tyLvls _ := []
  tyArgs j := if j = 1 then [.const ``QN []] else []
  ctorName n := if n = `_nested.QJ_1.mk then ``QJ.mk else n
  recName n := if n = `_nested.QJ_1.rec then ``QN.rec_1 else n

def qnNode : VIndCtor where
  name := ``QN.node
  params := []
  fields := [{ type := .const `_nested.QJ_1 [], lvl := .succ .zero,
               recArg := some { binders := [], idx := 1, args := [] } }]
  args := []

/-- The companion constructor, written out — and checked against the construction by
`qjAuxMk_built`.  Field `0` is the **`none` branch** (a `Prop`), field `1` the `some` one. -/
def qjAuxMk : VIndCtor where
  name := `_nested.QJ_1.mk
  params := []
  fields :=
    [{ type := .sort .zero, lvl := .succ .zero, recArg := none },
     { type := .const ``QN [], lvl := .succ .zero,
       recArg := some { binders := [], idx := 0, args := [] } }]
  args := []

def qnAux : VInductDecl' where
  uvars := 0
  params := []
  lvl := .succ .zero
  isLE := true
  types :=
    [{ name := ``QN, type := .sort (.succ .zero), indices := [], ctors := [qnNode] },
     { name := `_nested.QJ_1, type := .sort (.succ .zero), indices := [],
       ctors := [qjAuxMk] }]

def qnK : List Lean.Name := [`_nested.QJ_1]

/-! ### The construction computes the written-out companion, and it is anchored on Lean -/

theorem qjAuxMk_built : qnOcc.ctor qnAux.header qnRestore qjMk = qjAuxMk := rfl

theorem qnAux_member_built :
    qnAux.types[1]? = some (qnOcc.member qnAux.header qnRestore) := rfl

example : qnNode.typeR qnAux qnRestore 0 = (vconst(type_of% @QN.node)).type := rfl
example : qnAux.recTypeR qnRestore 0 = (vconst(type_of% @QN.rec)).type := rfl
example : qnAux.recTypeR qnRestore 1 = (vconst(type_of% @QN.rec_1)).type := rfl

/-! ### The degenerate coordinates, stated so they cannot drift -/

theorem qnAux_params_nil : qnAux.params = [] := rfl
theorem qnAux_uvars_zero : qnAux.uvars = 0 := rfl
theorem qnOcc_args_len : qnOcc.args.length = 1 := rfl

/-- The field's own context is **empty**: no parameters, and it is field `0`. -/
theorem qn_field0_ctx :
    ((((qnOcc.ctor qnAux.header qnRestore qjMk).fields.take 0).map (·.type)).reverse
      ++ qnAux.params.reverse) = [] := rfl

/-- …and the instance is **not** degenerate by emptiness: the constructor has two fields, and
field `1` takes the *other* branch. -/
theorem qjAuxMk_two_fields : (qnOcc.ctor qnAux.header qnRestore qjMk).fields.length = 2 := rfl

theorem qjAuxMk_field1_recArg :
    ((qnOcc.ctor qnAux.header qnRestore qjMk).fields.getD 1 default).recArg
      = some { binders := [], idx := 0, args := [] } := rfl

/-! ### The two recognition hypotheses of the repaired `none` branch -/

theorem qn_recog_none :
    qnRestore.recog qnAux.header.nm 0
      (VExpr.instAll ((qjMk.fields.getD 0 default).type.instL qnOcc.lvls) qnOcc.args 0)
      = none := rfl

theorem qn_recog_betaHead_none :
    qnRestore.recog qnAux.header.nm 0
      (betaHead (VExpr.instAll ((qjMk.fields.getD 0 default).type.instL qnOcc.lvls)
        qnOcc.args 0)) = none := rfl

/-- So `field` lands in the repaired `none`-`none` branch at field `0`. -/
theorem qn_field0_none_branch :
    qnOcc.field qnAux.header qnRestore 0 (qjMk.fields.getD 0 default)
      = { type := .sort .zero, lvl := .succ .zero, recArg := none } :=
  qnOcc.field_eq_none_branch qn_recog_none qn_recog_betaHead_none

/-! ### `WF` and `Built`, at a real environment -/

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' qjDecl = some env₂)
include h

theorem qj_const : env₂.constants ``QJ = some ⟨0, qjType.type⟩ :=
  VEnv.addInduct'_types h (List.Mem.head _)

theorem qjMk_const : env₂.constants ``QJ.mk = some ⟨0, qjMk.type qjDecl 0⟩ :=
  VEnv.addInduct'_ctors h (List.Mem.head _)

omit h in
theorem qn_const_staged {env₃ : VEnv} (hs : env₂.addIndTypes qnAux = some env₃) :
    env₃.constants ``QN = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants hs (``QN, ⟨0, .sort (.succ .zero)⟩) (by exact List.Mem.head _)

omit h in
theorem qjaux_const_staged {env₃ : VEnv} (hs : env₂.addIndTypes qnAux = some env₃) :
    env₃.constants `_nested.QJ_1 = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants hs (`_nested.QJ_1, ⟨0, .sort (.succ .zero)⟩)
    (by exact List.Mem.tail _ (List.Mem.head _))

omit h in
theorem qnAux_WF : qnAux.WF env₂ where
  types_ne := by simp [qnAux]
  params := trivial
  types := by
    intro T hT
    simp only [qnAux, List.mem_cons, List.not_mem_nil, or_false] at hT
    obtain rfl | rfl := hT <;>
      exact { indices := trivial, isType := ⟨_, by type_tac⟩, canon := ⟨_, by type_tac⟩ }
  ctors := by
    intro env₃ hs j T hT C hC
    have hn := qn_const_staged hs
    have hp := qjaux_const_staged hs
    match j, hT with
    | 0, hT =>
      simp only [qnAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_, args_len := rfl,
               args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [qnNode, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, qnAux, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; intro _ _ _ _ _ _ k B hB; simp at hB
                pos := ⟨by decide, rfl, nofun, nofun, trivial, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, ⟨_, by type_tac⟩, by decide⟩ }
      | (_ + 1), hF => simp [qnNode] at hF
    | 1, hT =>
      simp only [qnAux] at hT
      cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC
      refine { params_len := rfl, params_eq := .zero, fields := ?_, args_len := rfl,
               args_fresh := nofun, args_ty := .nil, result := by type_tac }
      intro i F hF
      match i, hF with
      | 0, hF =>
        simp only [qjAuxMk, List.getElem?_cons_zero, Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, qnAux, Lean.Nat.imax]
                binders_indep := nofun
                pos := ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts],
                        ⟨.succ .zero, by type_tac⟩⟩ }
      | 1, hF =>
        simp only [qjAuxMk, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hF
        subst hF
        exact { hasType := by type_tac
                level := fun ls => by simp [VLevel.eval, qnAux, Lean.Nat.imax]
                binders_indep := fun r hr => by
                  cases hr; intro _ _ _ _ _ _ k B hB; simp at hB
                pos := ⟨by decide, rfl, nofun, nofun, ⟨trivial, _, by type_tac⟩, by type_tac,
                        fun T' hT' => by cases hT'; exact .nil, ⟨_, by type_tac⟩, by decide⟩ }
      | (_ + 2), hF => simp [qjAuxMk] at hF
  isLE := fun _ => .inl (by simp [VLevel.IsNeverZero, VLevel.eval, qnAux])

omit h in
theorem qnRestore_ownId : qnRestore.OwnId qnAux qnK where
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [qnAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [qnAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [qnAux] at hT
  recName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [qnAux] at hT
  ctorName := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · cases hT; exact absurd (by decide) hK
    · simp [qnAux] at hT

theorem qnOcc_occurs : qnOcc.Occurs env₂ where
  hist := ⟨_, _, h, .rfl⟩
  idx_lt := by decide
  lvls_len := rfl
  args_len := rfl
  ty_const := qj_const h
  ctor_params := by
    intro C hC
    simp only [show qnOcc.src.ctors = [qjMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC; rfl
  ctor_const := by
    intro C hC
    simp only [show qnOcc.src.ctors = [qjMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC; exact qjMk_const h

omit h in
theorem qnAux_builtFresh : qnAux.BuiltFresh qnK (fun _ => qnOcc) where
  nodup := by decide
  fields_noK := by
    rintro (_ | _ | j) T hT hK C₀ hC₀ k F₀ hF₀
    · cases hT; exact absurd hK (by decide)
    · cases hT
      simp only [show qnOcc.src.ctors = [qjMk] from rfl, List.mem_cons,
        List.not_mem_nil, or_false] at hC₀
      subst hC₀
      rcases k with _ | _ | k
      · cases hF₀
        exact VExpr.noConsts_instAll _ _ (by simp [VExpr.NoConsts, VExpr.instL])
          (by simp [qnOcc, VExpr.NoConsts, qnK])
      · cases hF₀
        exact VExpr.noConsts_instAll _ _ (by simp [VExpr.NoConsts, VExpr.instL])
          (by simp [qnOcc, VExpr.NoConsts, qnK])
      · exact absurd hF₀ nofun
    · simp [qnAux] at hT

theorem qnAux_built : qnAux.Built qnRestore qnK env₂ (fun _ => qnOcc) where
  nodup := qnAux_builtFresh.nodup
  fields_noK := qnAux_builtFresh.fields_noK
  member := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · cases hT; rfl
    · simp [qnAux] at hT
  occurs := fun _ _ _ _ => qnOcc_occurs h
  tyName := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [qnAux] at hT
  tyLvls := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [qnAux] at hT
  tyArgs := by
    rintro (_ | _ | j) T hT hK
    · cases hT; exact absurd hK (by decide)
    · rfl
    · simp [qnAux] at hT
  ctorName_inv := by
    rintro (_ | _ | j) T hT hK C hC
    · cases hT; exact absurd hK (by decide)
    · simp only [show qnOcc.src.ctors = [qjMk] from rfl, List.mem_cons,
        List.not_mem_nil, or_false] at hC
      subst hC; rfl
    · simp [qnAux] at hT
  own := qnRestore_ownId

theorem qn_fresh (n : Lean.Name) (hn : n ∈ [``QN, `_nested.QJ_1]) :
    env₂.constants n = none := by
  rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
  rfl

theorem qnAux_staged_exists : ∃ env₃, env₂.addIndTypes qnAux = some env₃ :=
  VEnv.addConstList_eq_some_iff.2 ⟨fun n hn => qn_fresh h n hn, by decide⟩

/-! ### The measurement

`built_wf_forces_escape`, with **every** hypothesis discharged: `Built` and `WF` at the
environment `QJ` was just declared into, `addIndTypes` by `qnAux_staged_exists`, and the two
recognition hypotheses by `rfl`.  So the repaired `none` branch is a **reachable** obligation and
not an empty one. -/
theorem qn_pos_none_forced {env₃ : VEnv} (hst : env₂.addIndTypes qnAux = some env₃) :
    ∃ A, qnAux.NoBlock A ∧ env₃.IsDefEqType 0 [] (.sort .zero) A :=
  built_wf_forces_escape (K := qnK) (occ := fun _ => qnOcc) (j := 1)
    (qnAux_built h) qnAux_WF hst rfl (by decide) (List.Mem.head _) rfl
    qn_recog_none qn_recog_betaHead_none

omit h in
/-- …and the same statement, existentially in the environment, so no hypothesis is left. -/
theorem qn_pos_none_forced' :
    ∃ (env₂ env₃ : VEnv), VEnv.empty.addInduct' qjDecl = some env₂ ∧
      env₂.addIndTypes qnAux = some env₃ ∧
      ∃ A, qnAux.NoBlock A ∧ env₃.IsDefEqType 0 [] (.sort .zero) A := by
  obtain ⟨e₂, h₂⟩ : ∃ e, VEnv.empty.addInduct' qjDecl = some e := ⟨_, rfl⟩
  obtain ⟨e₃, h₃⟩ := qnAux_staged_exists h₂
  exact ⟨e₂, e₃, h₂, h₃, qn_pos_none_forced h₂ h₃⟩

end

/-- **…and the escape is FREE here, for any environment.**  The stored type is `Prop`, which is
block-free on the nose, so `A := F.type` discharges the `none` branch outright.  This is what
makes the branch *reachable but empty* at this instance: the obligation exists and costs
nothing. -/
theorem qn_escape_free (env : VEnv) :
    ∃ A, qnAux.NoBlock A ∧ env.IsDefEqType 0 [] (VExpr.sort .zero) A :=
  ⟨.sort .zero, by simp [VInductDecl'.NoBlock, VExpr.NoConsts], .succ .zero, by type_tac⟩

/-- **So `built_wf_of_escape_false` has no witness here either.**  Its `hesc` premise is the
negation of `qn_escape_free`, hence false at this instance — exactly as `hnone2` is false at
`MRWit`.  Stated rather than left to be inferred: the two escape theorems are now a matched pair
of *conditionals*, and **neither has a reachable instance in this tree at which its residue is
non-empty.** -/
theorem qn_not_escape_false (env : VEnv) :
    ¬ ¬ ∃ A, qnAux.NoBlock A ∧ env.IsDefEqType 0 [] (VExpr.sort .zero) A :=
  fun hn => hn (qn_escape_free env)

end QNWit

#print axioms Lean4Lean.MRedex.recog_none_of_lamHead
#print axioms Lean4Lean.MRedex.fieldO_eq_none_branch
#print axioms Lean4Lean.MRedex.built_wf_forces_escape
#print axioms Lean4Lean.MRedex.built_wf_of_escape_false
#print axioms Lean4Lean.VNestedOcc.field_eq_fieldO_of_some
#print axioms Lean4Lean.VNestedOcc.field_eq_fieldO_of_none
#print axioms Lean4Lean.VNestedOcc.field_new_branch
#print axioms Lean4Lean.VNestedOcc.field_eq_none_branch
#print axioms Lean4Lean.VNestedOcc.field_binders
#print axioms Lean4Lean.VNestedOcc.field_typeR
#print axioms Lean4Lean.VNestedOcc.fieldO_typeR
#print axioms Lean4Lean.VNestedOcc.bindersIndep
#print axioms Lean4Lean.VExpr.skips_betaHead
#print axioms Lean4Lean.VInductDecl'.CanonicalOwn.on
#print axioms Lean4Lean.MRedex.spineFn_canonType
#print axioms Lean4Lean.MRedex.canonType_ne_of_lamHead
#print axioms Lean4Lean.MRedex.MRWit.mr_member_built
#print axioms Lean4Lean.MRedex.MRWit.mr_member_not_built_old
#print axioms Lean4Lean.MRedex.MRWit.mr_obj_declared
#print axioms Lean4Lean.MRedex.MRWit.mr_minor_arity_ground
#print axioms Lean4Lean.MRedex.MRWit.mr_minor_arity_none
#print axioms Lean4Lean.MRedex.MRWit.mr_minor_arity_someB
#print axioms Lean4Lean.MRedex.MRWit.mr_recTypeR_ne
#print axioms Lean4Lean.MRedex.MRWit.mr_vconst_beta_reduces
#print axioms Lean4Lean.MRedex.MRWit.mr_fieldO1
#print axioms Lean4Lean.MRedex.MRWit.mr_field1
#print axioms Lean4Lean.MRedex.MRWit.mr_ctor_built
#print axioms Lean4Lean.MRedex.MRWit.mr_pos_beta
#print axioms Lean4Lean.MRedex.MRWit.mr_auxNodeB_not_canonical
#print axioms Lean4Lean.MRedex.MRWit.mr_auxNodeB_block_not_canonical
#print axioms Lean4Lean.MRedex.MRWit.mr_not_canonical_general
#print axioms Lean4Lean.MRedex.listOcc_field_eq_fieldO_0
#print axioms Lean4Lean.MRedex.listOcc_field_eq_fieldO_1
#print axioms Lean4Lean.MRedex.listOcc_betaHead_control
#print axioms Lean4Lean.MRedex.DgWit.dg_field_eq_fieldO
#print axioms Lean4Lean.MRedex.DgWit.dg_field_none_branch
#print axioms Lean4Lean.MRedex.DgWit.dg_field_none_branch_nontrivial
#print axioms Lean4Lean.MRedex.DgWit.dg_field_recArg_none
#print axioms Lean4Lean.MRedex.DgWit.dg_skips_betaHead_fires
#print axioms Lean4Lean.MRedex.DgWit.dg_betaHead_nontrivial

/-! §8's declarations: the instantiated `none` branch. -/
#print axioms Lean4Lean.MRedex.QNWit.qjAuxMk_built
#print axioms Lean4Lean.MRedex.QNWit.qnAux_member_built
#print axioms Lean4Lean.MRedex.QNWit.qn_field0_ctx
#print axioms Lean4Lean.MRedex.QNWit.qjAuxMk_two_fields
#print axioms Lean4Lean.MRedex.QNWit.qjAuxMk_field1_recArg
#print axioms Lean4Lean.MRedex.QNWit.qn_recog_none
#print axioms Lean4Lean.MRedex.QNWit.qn_recog_betaHead_none
#print axioms Lean4Lean.MRedex.QNWit.qn_field0_none_branch
#print axioms Lean4Lean.MRedex.QNWit.qnAux_WF
#print axioms Lean4Lean.MRedex.QNWit.qnAux_builtFresh
#print axioms Lean4Lean.MRedex.QNWit.qnAux_built
#print axioms Lean4Lean.MRedex.QNWit.qnOcc_occurs
#print axioms Lean4Lean.MRedex.QNWit.qnAux_staged_exists
#print axioms Lean4Lean.MRedex.QNWit.qn_pos_none_forced
#print axioms Lean4Lean.MRedex.QNWit.qn_pos_none_forced'
#print axioms Lean4Lean.MRedex.QNWit.qn_escape_free
#print axioms Lean4Lean.MRedex.QNWit.qn_not_escape_false

end MRedex
end Lean4Lean
