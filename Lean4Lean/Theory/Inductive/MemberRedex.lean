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

## The repair, and its price

`fieldB` is `VNestedOcc.field` with **one** change: when the recogniser fails on the substituted
type it is asked again on the type's **head-β contraction**, and if *that* fires the field is
stored **verbatim** (`type := S`, the redex) with `recArg := some r`.  Consequences, all proved
below:

* it is **conservative**: `fieldB = field` wherever the first recognition succeeds
  (`fieldB_eq_field_of_some`) or the second fails (`fieldB_eq_field_of_none`);
* `VNestedOcc.field_typeR` survives **with the same four hypotheses** (`fieldB_typeR`) — the new
  branch is `VIndRestore.restore_noK` against `Built.fields_noK`, so ruling 116d's cost does not
  grow;
* at the witness the residue of `VIndField.WF.pos` is **one `IsDefEq.beta`** (`mr_pos_beta`),
  which is what 116d promised and what the built member did not deliver;
* the minor-premise arity now matches Lean's stored recursor (`mr_minor_arity_someB`).

**It is a specification-side change only** — the implementation is untouched and the stored field
type is *more* faithful than before, not less — so **it is not a divergence and needs no
`divergences.md` entry**.  What it costs is stated and machine-checked: `VIndCtor.Canonical`
becomes **FALSE** at the repaired companion constructor (`mr_auxNodeB_not_canonical`), so
`VNestedOcc.ctor_Canonical`, `VNestedOcc.member_Canonical` and `VInductDecl'.Built.canonical` must
go.  Ruling 116d already said those "go away"; row 117d(iv) recorded that `Built.canonical` still
has four consumers.  This file makes the deletion compulsory rather than optional, and that is the
whole bill.

Precisely which sites: `VNestedOcc.ctor_Canonical` / `member_Canonical`
(`Theory/Inductive/NestedBuild.lean`) and `VInductDecl'.Built.canonical`, whose consumers are
`ElimNestedInductive.Result.RestoreData.mkRestore_canonical`
(`Verify/Inductive/NestedRestoreWit.lean`), its `OccData` wrapper
(`Verify/Inductive/NestedOccData.lean`), `nfnAux_canonicalOwn`
(`Theory/Inductive/NestedBuild.lean`) and `nfnAuxDirty_canonicalOwn`
(`Theory/Inductive/RestoreBridge.lean`).  Note the last two are **statements about
redex-free blocks and stay true** — they merely lose their general proof and need a `decide`
instead; what becomes false is the general lemma, and `ctor_Canonical`'s own proof says why
("because that is the only branch the recogniser takes").

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

open VExpr (mkPi mkLams mkApp bvars instAll splitPis)

/-! ## 0. Head β-contraction

`Lean.Expr.headBeta` at the `VExpr` level, written as a structural recursion on the spine so
that it reduces by `rfl`/`decide` (a `termination_by` version does not, which is why this one
recurses on the argument list). -/

def betaSpine : List VExpr → VExpr → VExpr
  | [], f => f
  | a :: as, .lam _ b => betaSpine as (b.inst a)
  | a :: as, f => f.mkApp (a :: as)

def betaHead (e : VExpr) : VExpr := betaSpine e.spineArgs e.spineFn

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

/-- …so the built field takes the `none` branch: **the stored type is the redex verbatim, and
`recArg` is `none`**.  The first half is faithfulness (the implementation stores exactly this);
the second half is the defect. -/
theorem field_eq_none_branch {N : VNestedOcc} {H : VIndHeader} {R : VIndRestore} {i : Nat}
    {F₀ : VIndField}
    (h : R.recog H.nm i (VExpr.instAll (F₀.type.instL N.lvls) N.args i) = none) :
    N.field H R i F₀ =
      { type := VExpr.instAll (F₀.type.instL N.lvls) N.args i,
        lvl := F₀.lvl.inst N.lvls, recArg := none } := by
  rw [VNestedOcc.field]; simp only [h]

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
      (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i) = none) :
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
  have hf := field_eq_none_branch (N := occ j) (H := D.header) (R := R) (i := i) (F₀ := F₀) hnone
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
    (hesc : ¬ ∃ A, D.NoBlock A ∧ env₁.IsDefEqType D.uvars
      ((((((occ j).ctor D.header R C₀).fields.take i).map (·.type)).reverse) ++ D.params.reverse)
      (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args i) A) :
    ¬ (D.WF env ∧ D.Built R K env occ) :=
  fun ⟨hwf, hb⟩ => hesc (built_wf_forces_escape hb hwf hst hT hK hC₀ hF₀ hnone)

/-! ## 3. The repair

One change: a **second chance** for the recogniser, on the head-β contraction, storing the
*stored* type rather than the canonical one. -/

/-- `VNestedOcc.field` with the second chance.  **The reported implementation change is: replace
`VNestedOcc.field`'s body by this one.** -/
def fieldB (N : VNestedOcc) (H : VIndHeader) (R : VIndRestore) (i : Nat)
    (F₀ : VIndField) : VIndField :=
  let S := VExpr.instAll (F₀.type.instL N.lvls) N.args i
  match R.recog H.nm i S with
  | some r => { type := r.canonTypeH H i, lvl := F₀.lvl.inst N.lvls, recArg := some r }
  | none =>
    match R.recog H.nm i (betaHead S) with
    | some r => { type := S, lvl := F₀.lvl.inst N.lvls, recArg := some r }
    | none => { type := S, lvl := F₀.lvl.inst N.lvls, recArg := none }

/-- **Conservative, half one**: where the recogniser already fired, nothing moves. -/
theorem fieldB_eq_field_of_some {N : VNestedOcc} {H : VIndHeader} {R : VIndRestore} {i : Nat}
    {F₀ : VIndField} {r : VIndRecArg}
    (h : R.recog H.nm i (VExpr.instAll (F₀.type.instL N.lvls) N.args i) = some r) :
    fieldB N H R i F₀ = N.field H R i F₀ := by
  rw [fieldB, VNestedOcc.field]; simp only [h]

/-- **Conservative, half two**: where the β-contraction is not recognised either, nothing
moves.  So the two definitions differ on **exactly** the fields the elimination manufactures. -/
theorem fieldB_eq_field_of_none {N : VNestedOcc} {H : VIndHeader} {R : VIndRestore} {i : Nat}
    {F₀ : VIndField}
    (h : R.recog H.nm i (VExpr.instAll (F₀.type.instL N.lvls) N.args i) = none)
    (h2 : R.recog H.nm i (betaHead (VExpr.instAll (F₀.type.instL N.lvls) N.args i)) = none) :
    fieldB N H R i F₀ = N.field H R i F₀ := by
  rw [fieldB, VNestedOcc.field]; simp only [h, h2]

/-- **The new branch stores the type verbatim.**  This is what keeps the construction faithful:
the implementation's `instantiateForallParams` output *is* this term. -/
theorem fieldB_new_branch {N : VNestedOcc} {H : VIndHeader} {R : VIndRestore} {i : Nat}
    {F₀ : VIndField} {r : VIndRecArg}
    (h : R.recog H.nm i (VExpr.instAll (F₀.type.instL N.lvls) N.args i) = none)
    (h2 : R.recog H.nm i (betaHead (VExpr.instAll (F₀.type.instL N.lvls) N.args i)) = some r) :
    fieldB N H R i F₀ =
      { type := VExpr.instAll (F₀.type.instL N.lvls) N.args i,
        lvl := F₀.lvl.inst N.lvls, recArg := some r } := by
  rw [fieldB]; simp only [h, h2]

/-- **`VNestedOcc.field_typeR` survives the repair, with the same four hypotheses.**

This is the load-bearing lemma of ruling 116d's cost accounting (row 117a), and the repair does
not add to it: the new branch is `VIndRestore.restore_noK` against `hS`, which is
`VInductDecl'.Built.fields_noK` — a premise the statement already had. -/
theorem fieldB_typeR (N : VNestedOcc) (H : VIndHeader) (R : VIndRestore) (D : VInductDecl')
    (K : List Lean.Name) (hH : H = D.header) (hown : R.OwnId D K)
    (hnd : D.blockNames.Nodup) (i : Nat) (F₀ : VIndField)
    (hS : VExpr.NoConsts K (VExpr.instAll (F₀.type.instL N.lvls) N.args i)) :
    (fieldB N H R i F₀).typeR D R i = VExpr.instAll (F₀.type.instL N.lvls) N.args i := by
  cases h : R.recog H.nm i (VExpr.instAll (F₀.type.instL N.lvls) N.args i) with
  | some r =>
    rw [fieldB_eq_field_of_some h]
    exact N.field_typeR H R D K hH hown hnd i F₀ hS
  | none =>
    cases h2 : R.recog H.nm i (betaHead (VExpr.instAll (F₀.type.instL N.lvls) N.args i)) with
    | some r =>
      rw [fieldB_new_branch h h2, VIndField.typeR]
      exact VIndRestore.restore_noK hown i _ hS
    | none => rw [fieldB_eq_field_of_none h h2, VIndField.typeR, field_eq_none_branch h]

/-! ## 4. The price, as a theorem: `VIndCtor.Canonical` becomes false

`VNestedOcc.ctor_Canonical` is currently *true with no hypotheses* — and that is precisely
because `field` reports `recArg = none` at the redex, so `Canonical` has nothing to check there.
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

/-- So the built field is the redex with `recArg = none`. -/
theorem mr_field1 :
    mrOcc.field (mrAux mrAuxNode).header mrRestore 1 (mrNode.fields.getD 1 default)
      = { type := mrRedex, lvl := .succ .zero, recArg := none } := rfl

/-- **`Built.member` is SATISFIED here** — the companion member of `mrAux mrAuxNode` *is* the
value the construction computes, by `rfl`.  This is the round's first correction to row 117e:
`member` is not the false clause; it is satisfiable, and what it forces is `recArg = none`. -/
theorem mr_member_built :
    (mrAux mrAuxNode).types[1]? = some (mrOcc.member (mrAux mrAuxNode).header mrRestore) := rfl

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

/-- **`fieldB` stores the redex and records it as recursive** — which is what the kernel does. -/
theorem mr_fieldB1 :
    fieldB mrOcc (mrAux mrAuxNodeB).header mrRestore 1 (mrNode.fields.getD 1 default)
      = { type := mrRedex, lvl := .succ .zero,
          recArg := some { binders := [], idx := 0, args := [] } } := rfl

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

/-- **`VIndCtor.Canonical` is FALSE at the repaired companion constructor.**  It is `True` today
only because `field` reports `recArg = none` there, i.e. because the built member mis-models the
kernel — so `VNestedOcc.ctor_Canonical`, `member_Canonical` and `VInductDecl'.Built.canonical`
must go, and row 117d(iv)'s four remaining consumers of the last one must be re-plumbed.  That is
the whole bill for the repair. -/
theorem mr_auxNodeB_not_canonical : ¬ mrAuxNodeB.Canonical (mrAux mrAuxNodeB) := by
  intro h
  exact absurd (h 1 _ _ rfl rfl) (by decide)

/-- …and the general reason, with no witness in it: a redex-headed stored type is never
`r.canonType`. -/
theorem mr_not_canonical_general {D : VInductDecl'} {C : VIndCtor} {i : Nat} {F : VIndField}
    {r : VIndRecArg} {A b : VExpr} (hF : C.fields[i]? = some F) (hr : F.recArg = some r)
    (hlam : F.type.spineFn = .lam A b) : ¬ C.Canonical D :=
  fun h => canonType_ne_of_lamHead hlam (h i F r hF hr).symm

end MRWit

/-! ## 5a. The existing witnesses and the negative control survive the repair

`fieldB` differs from `field` only where the recogniser fails *and* the head-β contraction is
recognised, so every `rfl`/`decide` in the tree that computes `field` at a redex-free block is
untouched.  Checked here rather than asserted, at the two places that would notice:
`_nested.List_1.cons`'s two fields, and `listOcc_recog_field1_fails` — the **negative control**
that deletes the head generalisation and asserts the recogniser does *not* fire.  Its substituted
type is `.const`-headed, so `betaHead` is the identity on it and the second chance fails too: the
control still controls. -/

section
open InductiveDeclExamples

theorem listOcc_fieldB_eq_0 :
    fieldB listOcc ntreeAux.header ntreeRestore 0 (listCons.fields.getD 0 default)
      = listOcc.field ntreeAux.header ntreeRestore 0 (listCons.fields.getD 0 default) := rfl

theorem listOcc_fieldB_eq_1 :
    fieldB listOcc ntreeAux.header ntreeRestore 1 (listCons.fields.getD 1 default)
      = listOcc.field ntreeAux.header ntreeRestore 1 (listCons.fields.getD 1 default) := rfl

/-- **The negative control still fails under the second chance.** -/
theorem listOcc_fieldB_control :
    { ntreeRestore with tyArgs := fun _ => VExpr.bvars 0 1 }.recog ntreeAux.header.nm 1
        (betaHead (VExpr.instAll ((listCons.fields.getD 1 default).type.instL listOcc.lvls)
          listOcc.args 1))
      = none := rfl

end

/-! ## 6. Instrument 7 and its dual

**Instrument 7** (green because the hypotheses are unsatisfiable): `recogAt_none_of_lamHead`,
`recog_none_of_lamHead`, `field_eq_none_branch`, `fieldB_eq_field_of_some`,
`fieldB_eq_field_of_none`, `fieldB_new_branch` all have hypotheses that are **discharged by
`rfl` at the witness** (`mr_recog_none`, `mr_recogB`), so none is vacuous.  `spineFn_canonType`,
`canonType_ne_of_lamHead` and every `mr_*` theorem outside `mr_pos_beta`/`mr_const_hasType` are
hypothesis-free.  `mr_pos_beta`'s single hypothesis is inhabited by `mr_const_hasType`.

**Its dual** (green because the difficulty moved into an uninhabited hypothesis — ledger row
116g, and `BuiltFresh` the most recent instance):

* `built_wf_forces_escape` has the escape as a **conclusion**, and
  `built_wf_of_escape_false` restates it with the escape as a **hypothesis**, so the residue is
  visible on the page.  Neither is claimed to refute anything on its own: the escape is a
  `Prop` with **no known inhabitant and no known refutation**, and refuting it is
  Church–Rosser strength.  What is proved is that it is the *sole* residue of route A.
* `fieldB_typeR` gains **no** hypothesis over `VNestedOcc.field_typeR`: same four, and the new
  branch consumes `hS` (= `Built.fields_noK`, row 117c's clause with no general producer) exactly
  as the old `some` branch already did.  So the repair does **not** enlarge ruling 116d's
  uninhabited-premise bill — but it does not shrink it either, and `fields_noK` still has no
  producer except `decide` at a concrete block.
* **`mr_auxNodeB_not_canonical` is the dual read in reverse**: `VNestedOcc.ctor_Canonical` is a
  hypothesis-free green theorem today, and it is green *because* `field`'s `none` branch makes
  `Canonical` vacuous at the very field this file is about.  A green theorem can be worse than a
  red one when the definition it quantifies over is the wrong one.
-/

#print axioms Lean4Lean.MRedex.recog_none_of_lamHead
#print axioms Lean4Lean.MRedex.field_eq_none_branch
#print axioms Lean4Lean.MRedex.built_wf_forces_escape
#print axioms Lean4Lean.MRedex.built_wf_of_escape_false
#print axioms Lean4Lean.MRedex.fieldB_eq_field_of_some
#print axioms Lean4Lean.MRedex.fieldB_eq_field_of_none
#print axioms Lean4Lean.MRedex.fieldB_new_branch
#print axioms Lean4Lean.MRedex.fieldB_typeR
#print axioms Lean4Lean.MRedex.spineFn_canonType
#print axioms Lean4Lean.MRedex.canonType_ne_of_lamHead
#print axioms Lean4Lean.MRedex.MRWit.mr_member_built
#print axioms Lean4Lean.MRedex.MRWit.mr_obj_declared
#print axioms Lean4Lean.MRedex.MRWit.mr_minor_arity_ground
#print axioms Lean4Lean.MRedex.MRWit.mr_minor_arity_none
#print axioms Lean4Lean.MRedex.MRWit.mr_minor_arity_someB
#print axioms Lean4Lean.MRedex.MRWit.mr_recTypeR_ne
#print axioms Lean4Lean.MRedex.MRWit.mr_vconst_beta_reduces
#print axioms Lean4Lean.MRedex.MRWit.mr_fieldB1
#print axioms Lean4Lean.MRedex.MRWit.mr_pos_beta
#print axioms Lean4Lean.MRedex.MRWit.mr_auxNodeB_not_canonical
#print axioms Lean4Lean.MRedex.MRWit.mr_not_canonical_general
#print axioms Lean4Lean.MRedex.listOcc_fieldB_eq_1
#print axioms Lean4Lean.MRedex.listOcc_fieldB_control

end MRedex
end Lean4Lean
