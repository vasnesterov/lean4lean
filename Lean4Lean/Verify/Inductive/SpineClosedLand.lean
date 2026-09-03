import Lean4Lean.Verify.Inductive.HargsAttack

/-!
# The flip, made: `TrIndDeclN` now carries the spine datum

`Verify/Inductive/HargsAttack.lean` isolated the nested flip's last leaf (`hargs`) and priced it at
**one clause**.  This file is the flip itself, plus the measurement that says *which* clause it had
to be.

## What is new here, and what changed elsewhere

`Verify/Environment/InductR.lean` gained one field on `TrIndDeclN`, `trSpine`, which is
`VIndRestore.SpineHargsN` (`Verify/Inductive/SpineClause.lean` §5) with `declTele` spelled out.
It is supplied at **all three** of the tree's construction sites of `TrIndDeclN` —
`TrIndDecl.toN` (vacuously, `K = []`), `NestedWit.trIndDeclN_wit` and
`NestedWit.trIndDeclN_wit'` (each by the same seven lines).  Nothing else in the tree needed a
change: `lake build` is green at 1620 jobs.

## §1 is the reason the field is `trSpine` and not the scope clause

An earlier proposal was to carry `VIndRestore.SpineClosedC` (`HargsAttack.lean` §4) instead.  Its
two advertised properties are both true and neither is sufficiency:

* it is **necessary** (`not_spineHargsC_of_not_spineClosedC`), and
* it is **free from the datum** (`spineClosedC_of_spineHargsC`).

But `HargsAt` is a `VEnv.HasArgs` — a *typing* judgement, at an environment — and `SpineClosedC`
mentions no environment at all.  §1 makes that machine-checked at the real parameterised block:
a presented spine that is **closed** and whose *length* disagrees with the presented head's
declared telescope satisfies `SpineClosedC` and refutes the datum
(`spineClosedC_not_sufficient`).  So the scope clause discharges no `hargs` obligation, and
`HargsAttack.lean` §4's own reading — *"if the flip takes `SpineClause.lean` §4's measured
`trSpine` field, the scope clause is not a second clause"* — is the correct one: the datum is the
field, the scope clause is a **corollary** of it (`TrIndDeclN.spineClosedC`, §2).

## §2 is the payoff, §3 the arity-0 witness

§2 derives, from the field alone plus data the consumer already has: the checker-side clause
(`TrIndDeclN.spineHargsC`), `hargs` per companion member (`TrIndDeclN.hargsAt`) — *the hypothesis
eight consumers used to assume* — the scope clause, `(R.csubstTy D K).Closed`, and the whole nested
transport `(R.csubstTy D K).WF`.  §3 runs the field through those general theorems at
`InductiveDeclExamples.ntreeAux` (`uvars = 1`, `params = [Type u]`, spine `[NTree.{u} #0]`), arity 0,
with no block-specific step; `nfnAux` is degenerate (`uvars = 0`, `params = []`) and is not used.

## What this file does NOT establish

A **general producer** of the field.  At `numNested > 0` the field's only producers are the two
`NFn`/`PFn` witnesses and (for the clause text alone) `ntreeAux`.  `ValAtParam.lean` §6 measures
where the general one bottoms out — `VEnv.AxiomConservativityWF`, equivalently the forward
direction of `VEnv.IsDefEqU.weakN_iff`, the `sorry` at `Theory/Typing/UniqueTyping.lean:193` — and
this file does not attempt it.  Nothing here is a step toward that hole; the flip is the *other*
half, and it is now paid.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §1 The scope clause is necessary, free, and **not sufficient**

The engine is one line: `VEnv.HasArgs.length_eq`.  A `HasArgs` forces telescope and spine to have
the same length, and `SpineClosedC` says nothing about either length — it is a predicate on the
spine's *variables*.  So a length mismatch is a refutation of the datum that survives every
strengthening of the scope clause. -/

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {env e : VEnv}

/-- **A LENGTH MISMATCH REFUTES THE DATUM**, at every environment, with no `Ordered`, no `Built`,
no `Faithful` and no inversion.

Stated with the split count pinned to `(R.tyArgs j).length` because that is what `SpineHargsC` —
and hence the new `TrIndDeclN.trSpine` — pins it to; the mismatch is then between the *spine* and
the telescope the presented head's declared type actually yields after that many splits, which is
shorter whenever the head's type runs out of pis first.  (Weaker than a general "no `HasArgs`"
statement on purpose: this form needs only `length_eq`, so it is hole-free, and
`VEnv.HasArgs.of_mkApp` — which reaches `sorryAx` via `VEnv.IsDefEqU.forallE_inv_stratified` and
`VEnv.WF.rigidShapeUniqNS` — is nowhere near it.) -/
theorem not_spineHargsC_of_tele_length {j : Nat} {T : VIndType} {ci : VConstant}
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hci : env.constants (R.tyName j) = some ci)
    (hlen : (R.declTele ci (R.tyArgs j).length j).length ≠ (R.tyArgs j).length) :
    ¬ R.SpineHargsC D K env e :=
  fun hS => hlen (hS j T hT hK ci hci).length_eq

/-- …and a spine of sorts is `ClosedN` at every depth, so the scope clause is *insensitive* to the
mismatch above.  This is the half `SpineClosedC` cannot see. -/
theorem spineClosedC_of_forall_sort (h : ∀ (j : Nat), ∀ a ∈ R.tyArgs j, ∃ l, a = .sort l) :
    R.SpineClosedC D K := by
  intro j _ _ _ a ha
  obtain ⟨l, rfl⟩ := h j a ha
  trivial

end VIndRestore

/-! ### §1a The separation, at the real parameterised block

`ntreeRestore` with **only the spine replaced** — same `tyName`, same `tyLvls`, so the clause's
`∀ ci` premise still fires at the same declared `List` — by a two-element spine of sorts.  Closed,
hence `SpineClosedC`; but `List`'s declared type yields a **one**-binder telescope after two
splits, so the datum is false at every environment. -/

namespace InductiveDeclExamples

/-- `ntreeRestore` with a closed, wrong-length spine.  Not the loose spine of `HargsAttack.lean`
§3/§5: that one is refuted *by* the scope clause, this one **satisfies** it. -/
def ntreeClosedJunkRestore : VIndRestore :=
  { ntreeRestore with tyArgs := fun _ => [.sort .zero, .sort .zero] }

/-- The two differ only in the spine, so nothing that reads `tyName`/`tyLvls` can tell them
apart. -/
theorem ntreeClosedJunkRestore_tyName : ntreeClosedJunkRestore.tyName = ntreeRestore.tyName := rfl

theorem ntreeClosedJunkRestore_tyLvls : ntreeClosedJunkRestore.tyLvls = ntreeRestore.tyLvls := rfl

/-- …and they do differ: the real spine is parameter-dependent and of length `1`. -/
theorem ntreeClosedJunkRestore_tyArgs_ne :
    ntreeClosedJunkRestore.tyArgs 1 ≠ ntreeRestore.tyArgs 1 := by decide

/-- **THE SEPARATION.**  Existentially closed at the block Lean's own kernel runs the nested
elimination on: the scope clause holds, the presented head is genuinely declared (so the datum's
`∀ ci` premise fires and the refutation is not vacuous), and the datum is false **at every target
environment**. -/
theorem ntree_spineClosedC_and_not_spineHargsC :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.constants (ntreeClosedJunkRestore.tyName 1)
        = some ⟨listOcc.decl.uvars, listOcc.src.type⟩ ∧
      ntreeClosedJunkRestore.SpineClosedC ntreeAux ntreeK ∧
      ∀ e : VEnv, ¬ ntreeClosedJunkRestore.SpineHargsC ntreeAux ntreeK env₁ e := by
  obtain ⟨env₁, h, hlook⟩ := ntreeAux_spineHargsC_lookup
  refine ⟨env₁, h, hlook, VIndRestore.spineClosedC_of_forall_sort ?_, fun e => ?_⟩
  · intro j a ha
    have ha' : a ∈ [(VExpr.sort .zero), VExpr.sort .zero] := ha
    exact ⟨.zero, by simpa using ha'⟩
  · exact VIndRestore.not_spineHargsC_of_tele_length
      (show ntreeAux.types[1]? = some _ from rfl) (by decide) hlook (by decide)

end InductiveDeclExamples

/-- **THE SCOPE CLAUSE IS NOT THE DATUM**, as one closed statement.  So a `TrIndDeclN` field
saying `SpineClosedC` would discharge no consumer's `hargs`, at any block. -/
theorem VIndRestore.spineClosedC_not_sufficient :
    ¬ ∀ (R : VIndRestore) (D : VInductDecl') (K : List Name) (env e : VEnv),
        R.SpineClosedC D K → R.SpineHargsC D K env e := by
  intro h
  obtain ⟨env₁, -, -, hcl, hno⟩ := InductiveDeclExamples.ntree_spineClosedC_and_not_spineHargsC
  exact hno VEnv.empty (h _ _ _ env₁ VEnv.empty hcl)

/-! ## §2 What the field buys

Every theorem below takes a `TrIndDeclN` and nothing the consumers do not already hold.  The first
two are pure bookkeeping — the field *is* `SpineHargsN`, because `declTele` is an `abbrev` — and
after that the general theorems of `SpineClause.lean` and `HargsAttack.lean` do the work. -/

variable {env env₁ e₂ : VEnv} {Us : List Name} {np numNested : Nat}
  {types : List Lean.InductiveType} {iu : Bool} {D : VInductDecl'} {K : List Name}
  {R : VIndRestore} {occ : Nat → VNestedOcc}

/-- The field, as `SpineClause.lean` §5 names it.  `rfl`-level: the field text is that definition
with `VIndRestore.declTele` unfolded, and `declTele` is reducible. -/
theorem TrIndDeclN.spineHargsN (h : TrIndDeclN env Us np types iu numNested D K R) :
    R.SpineHargsN D K env types := h.trSpine

/-- **THE CHECKER-SIDE CLAUSE FROM THE FIELD**, with the guard style converted by `companions` and
the staging premise discharged where the consumer has it. -/
theorem TrIndDeclN.spineHargsC (h : TrIndDeclN env Us np types iu numNested D K R)
    (h₁ : env.addIndTypesC D K = some env₁) : R.SpineHargsC D K env env₁ :=
  VIndRestore.spineHargsC_of_spineHargsN h.companions h₁ h.spineHargsN

/-- **`hargs`, PER COMPANION MEMBER, FROM THE TRANSLATION RELATION.**  This is the hypothesis that
was *assumed* at every consumer in the corner: `VIndRestore.HargsAt` is `SpineHargsC`'s body at one
member (`spineHargsC_iff_hargsAt`, an `Iff.rfl`), and it is now a consequence of `TrIndDeclN`. -/
theorem TrIndDeclN.hargsAt (h : TrIndDeclN env Us np types iu numNested D K R)
    (h₁ : env.addIndTypesC D K = some env₁) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) {ci : VConstant}
    (hci : env.constants (R.tyName j) = some ci) :
    R.HargsAt D env₁ (R.tyArgs j).length j ci :=
  h.spineHargsC h₁ j T hT hK ci hci

/-- **THE SCOPE CLAUSE, FREE FROM THE FIELD** — so it is not a second field.  §1 shows the converse
fails, which is why this direction is the only one available.

The three extra inputs are `spineHargsC_closedN`'s own and are not new premises for a consumer:
`Built` is what the nested step carries, `env₁.Ordered` is the stage's own well-formedness, and the
parameter context is `D.WF.params` moved along `env ≤ env₁` (`VInductDecl'.WF.params_le`). -/
theorem TrIndDeclN.spineClosedC (h : TrIndDeclN env Us np types iu numNested D K R)
    (h₁ : env.addIndTypesC D K = some env₁) (he : env₁.Ordered)
    (hparams : OnCtx D.params.reverse (env₁.IsType D.uvars)) (hB : D.Built R K env occ) :
    R.SpineClosedC D K :=
  VIndRestore.spineClosedC_of_spineHargsC he hparams hB (h.spineHargsC h₁)

/-- …hence `(R.csubstTy D K).Closed`, the hypothesis `SpineClause.lean` §4's transport used to
carry separately, is discharged from the translation relation. -/
theorem TrIndDeclN.csubstTy_closed (h : TrIndDeclN env Us np types iu numNested D K R)
    (h₁ : env.addIndTypesC D K = some env₁) (he : env₁.Ordered) (hOrd : env.Ordered)
    (hD : D.WF env) (hB : D.Built R K env occ) : (R.csubstTy D K).Closed :=
  VIndRestore.csubstTy_closed_of_spineHargsC he hOrd hD
    (OnCtx.mono (fun hx => hx.mono (VEnv.addConstList_le h₁)) hD.params) hB (h.spineHargsC h₁)

/-- **THE WHOLE NESTED TRANSPORT, FROM THE TRANSLATION RELATION.**  `(R.csubstTy D K).WF` — the
substitution well-formedness `csubstTy_WF_of_val` needed and only `ValAt` was missing from — with
its spine hypothesis and its closedness hypothesis *both* supplied by the new field. -/
theorem TrIndDeclN.csubstTy_WF (h : TrIndDeclN env Us np types iu numNested D K R)
    (h₁ : env.addIndTypesC D K = some env₁) (hB : D.Built R K env occ)
    (hOrd : env.Ordered) (he : env₁.Ordered) (hD : D.WF env)
    (hf : (R.csubstTy D K).FreshIn env) (h₂ : env.addIndTypes D = some e₂)
    (hlvl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ l ∈ R.tyLvls j, l.WF D.uvars) :
    (R.csubstTy D K).WF e₂ env₁ D.uvars :=
  VIndRestore.csubstTy_WF_of_hargs hB (h.spineHargsC h₁) (VEnv.addConstList_le h₁) hOrd he hD hf
    h₂ h₁ hlvl

/-- **§8.7's `val` OBLIGATION FROM THE TRANSLATION RELATION.**  `tyVal_hasType_of_spineHargsC` with
the clause supplied by the field.  `Faithful` is still an explicit premise: it is *not* a field of
`TrIndDeclN` and §1's separation is not what stops it — `RestoreFaithful.lean` derives it from the
translation plus the step, so it is discharged there rather than here.  Recorded at the statement
so the next reader does not mistake this for the flip's last obligation. -/
theorem TrIndDeclN.tyVal_hasType (h : TrIndDeclN env Us np types iu numNested D K R)
    (h₁ : env.addIndTypesC D K = some env₁) {j : Nat} {T : VIndType}
    (hfa : R.Faithful D env K (fun j => (R.tyArgs j).length))
    (hparams : OnCtx D.params.reverse (env₁.IsType D.uvars))
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars) :
    env₁.HasType D.uvars [] (R.tyVal D j) T.type :=
  VIndRestore.tyVal_hasType_of_spineHargsC hfa (VEnv.addConstList_le h₁) hparams hT hK hlvl
    (h.spineHargsC h₁)

/-- **THE STEP-LEVEL PAYOFF, AND THE POINT OF THE FLIP.**  `InductStepNested` — the nested branch's
own step predicate — now **implies** `hargs`: the staged environment comes from
`AddInductStagesR.addIndTypesC` and the datum from the new field, so a consumer of the step no
longer has to assume the spine is typed.  Before this field there was no derivation of any
`VEnv.HasArgs` from `InductStepNested` at all.

What is *not* here: `(R.csubstTy D K).WF` at the step, because `csubstTy_WF` additionally needs
`D.Built R K venv occ`, `(R.csubstTy D K).FreshIn venv` and the level well-formedness, none of
which `InductStepNested` carries. Those are the flip's *remaining* obligations, and they are
`RestoreData`/`OccResidue` business, not `hargs`. -/
theorem InductStepNested.spineHargsC {m m' : Lean.ConstMap} {venv venv' : VEnv} {lp : List Name}
    (h : InductStepNested m m' venv venv' lp np types numNested) :
    ∃ (D : VInductDecl') (K : List Name) (R : VIndRestore) (env₁ : VEnv),
      venv.addIndTypesC D K = some env₁ ∧ R.SpineHargsC D K venv env₁ ∧
      ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
        ∀ ci : VConstant, venv.constants (R.tyName j) = some ci →
          R.HargsAt D env₁ (R.tyArgs j).length j ci := by
  obtain ⟨D, K, R, htr, -, -, hst⟩ := h
  obtain ⟨env₁, h₁⟩ := hst.addIndTypesC
  exact ⟨D, K, R, env₁, h₁, htr.spineHargsC h₁,
    fun j T hT hK ci hci => htr.hargsAt h₁ hT hK hci⟩

/-! ## §3 The arity-0 witness, at the parameterised block, through the general theorems

`ntreeAux`: `NTree α` with a `List (NTree α)` field, `uvars = 1`, `params = [Type u]`, `np = 1`,
presented spine `[NTree.{u} #0]`.  The field text at this block is
`ValAtParam.lean` §4's `ntreeAux_spineHargsN`, which is **exactly** the new `trSpine`'s content;
everything after it is a general theorem of §1/§2 or of `HargsAttack.lean`, never a computation at
this block.

`nfnAux` is the degenerate sibling (`uvars = 0`, `params = []`, so every context hypothesis is
`trivial`) and is deliberately not the witness. -/

namespace InductiveDeclExamples

/-- **THE WITNESS.**  Existentially closed, and every conjunct reached from the **field text**:

1. the staging, and the field's content at this block (`ntreeAux_spineHargsN`);
2. the checker-side clause, by `spineHargsC_of_spineHargsN` — the same step
   `TrIndDeclN.spineHargsC` takes;
3. **`hargs` at the companion member**, i.e. `VIndRestore.HargsAt`, the datum every consumer used
   to assume — obtained by `spineHargsC_iff_hargsAt`, the same step `TrIndDeclN.hargsAt` takes;
4. the scope clause, by `spineClosedC_of_spineHargsC` — so the clause §1 refutes as a *field* is
   here derived as a *corollary*, at the same block;
5. `(R.csubstTy D K).Closed`, by `csubstTy_closed_of_spineHargsC`;
6. and the separation of §1a at the same environment: a closed spine at which the datum fails, so
   the field is not implied by the scope clause even here. -/
theorem ntreeAux_flip_witness :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      ntreeRestore.SpineHargsN ntreeAux ntreeK env₁ [ntreeIndType] ∧
      ntreeRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ ∧
      ntreeRestore.HargsAt ntreeAux env₃ (ntreeRestore.tyArgs 1).length 1
        ⟨listOcc.decl.uvars, listOcc.src.type⟩ ∧
      ntreeRestore.SpineClosedC ntreeAux ntreeK ∧
      (ntreeRestore.csubstTy ntreeAux ntreeK).Closed ∧
      ntreeClosedJunkRestore.SpineClosedC ntreeAux ntreeK ∧
      ¬ ntreeClosedJunkRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ := by
  obtain ⟨env₁, env₂, env₃, h, h₂, h₃, -⟩ := ntreeAux_spineHargsC
  obtain ⟨env₁', h', hN⟩ := ntreeAux_spineHargsN
  cases Option.some.inj (h'.symm.trans h)
  -- (2): the general bridge, from the field text
  have hS : ntreeRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ :=
    VIndRestore.spineHargsC_of_spineHargsN ntreeAux_companions h₃ hN
  have henv₁ : env₁.Ordered := listEnv_ordered h
  have h₃' : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ := by
    rw [VEnv.addIndTypesC] at h₃; exact h₃
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf ntreeAux_WF') h₃'
  have hB := ntreeAux_built h
  obtain ⟨envJ, hJ, -, hclJ, hnoJ⟩ := ntree_spineClosedC_and_not_spineHargsC
  cases Option.some.inj (hJ.symm.trans h)
  refine ⟨env₁, env₂, env₃, h, h₂, h₃, hN, hS, ?_, ?_, ?_, hclJ, hnoJ env₃⟩
  · -- (3): `hargs` at the companion member, through `spineHargsC_iff_hargsAt`
    exact VIndRestore.spineHargsC_iff_hargsAt.1 hS 1 _
      (show ntreeAux.types[1]? = some _ from rfl) (by decide) _
      (VIndRestore.built_ty_const hB (show ntreeAux.types[1]? = some _ from rfl) (by decide))
  · exact VIndRestore.spineClosedC_of_spineHargsC henv₃ ntreeAux_params_WF hB hS
  · exact VIndRestore.csubstTy_closed_of_spineHargsC henv₃ henv₁ ntreeAux_WF'
      ntreeAux_params_WF hB hS

/-- Non-degeneracy of §3, `decide`-checked, in the three ways it could be uninteresting.  (The
fourth — that the block is the parameterised one — is `ntreeAux.uvars = 1` and
`ntreeAux.params ≠ []`, checked in `ValAtParam.lean` §5.) -/
theorem ntreeAux_flip_witness_nondegenerate :
    ntreeK ≠ [] ∧ ntreeRestore.tyArgs 1 ≠ [] ∧ 0 < ntreeAux.np := by decide

end InductiveDeclExamples

end Lean4Lean

/-! ## §4 Grading: hole-freeness, per declaration

Every line below is hole-freeness and nothing else (`docs/vacuity-ledger.md` §0); inhabitation is
§1a and §3, and non-degeneracy `ntreeAux_flip_witness_nondegenerate`.  Names read off this file's
own `namespace` lines. -/

#print axioms Lean4Lean.VIndRestore.not_spineHargsC_of_tele_length
#print axioms Lean4Lean.VIndRestore.spineClosedC_of_forall_sort
#print axioms Lean4Lean.InductiveDeclExamples.ntreeClosedJunkRestore_tyName
#print axioms Lean4Lean.InductiveDeclExamples.ntreeClosedJunkRestore_tyLvls
#print axioms Lean4Lean.InductiveDeclExamples.ntreeClosedJunkRestore_tyArgs_ne
#print axioms Lean4Lean.InductiveDeclExamples.ntree_spineClosedC_and_not_spineHargsC
#print axioms Lean4Lean.VIndRestore.spineClosedC_not_sufficient
#print axioms Lean4Lean.TrIndDeclN.spineHargsN
#print axioms Lean4Lean.TrIndDeclN.spineHargsC
#print axioms Lean4Lean.TrIndDeclN.hargsAt
#print axioms Lean4Lean.TrIndDeclN.spineClosedC
#print axioms Lean4Lean.TrIndDeclN.csubstTy_closed
#print axioms Lean4Lean.TrIndDeclN.csubstTy_WF
#print axioms Lean4Lean.TrIndDeclN.tyVal_hasType
#print axioms Lean4Lean.InductStepNested.spineHargsC
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_flip_witness
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_flip_witness_nondegenerate
