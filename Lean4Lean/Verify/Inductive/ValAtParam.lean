import Lean4Lean.Verify.Inductive.SpineClause
import Lean4Lean.Verify.Inductive.RestrictStep

/-!
# `ValAt` at the **parameterised** nested block, with no hypothesis left

`Verify/Inductive/SpineClause.lean` §6b instantiated the checker-side clause
`VIndRestore.SpineHargsC` at `ntreeAux` — `NTree α` with a `List (NTree α)` field, `np = 1`,
`uvars = 1`, the block Lean's own kernel runs the nested elimination on — and then stopped, saying
of the consumer:

> `ValAt` from it additionally needs `OnCtx ntreeAux.params.reverse (env₃.IsType 1)`, which is not
> `trivial` at this block and is **not supplied here** — that is the one hypothesis of §4 still
> open at the parameterised witness.

That was stale in two independent ways, and this file closes both.

* **At the witness**: `InductiveDeclExamples.ntreeAux_params_WF`
  (`Theory/Inductive/NestedHead.lean`) *is* that premise, hole-free, and
  `ntreeAux.uvars = 1` literally, so instantiating it at `env := env₃` discharges the hypothesis
  verbatim.  §2 delivers `ValAt` at the parameterised block **unconditionally** — nothing
  hypothesised, the premise gone from the statement rather than moved.
* **In general**: the premise is *redundant* wherever `D.WF env` is available, because
  `VInductDecl'.WF.params` is exactly `OnCtx D.params.reverse (env.IsType D.uvars)` at the
  pre-block environment and `OnCtx.mono` moves it up any `env ≤ e`.  §1 states that, and
  `SpineClause.lean` §4's `csubstTy_WF_of_spineHargsC` is weakened accordingly (it already took
  `D.WF env` and `env ≤ e`, so it never needed `hparams`).

Then §§3–5 push on.  What `ValAt` at the parameterised witness unlocks is the **general route**
run end-to-end there: §3 derives `(ntreeRestore.csubstTy ntreeAux ntreeK).WF env₂ env₃ 1` from the
checker-side clause via `csubstTy_WF_of_val`, where `Theory/Typing/ConstSubstNested.lean`'s
`ntreeSubst_WF` had only a *hand* discharge (`type_tac` on the concrete spine).  The conclusion is
not new; the **route** to it is, and `RestrictCompanion.lean` §8's own prose ("Not a route … Two
witnesses with the transport are still two witnesses") is what that answers.  §4 puts the
`TrIndDeclN` field text (`SpineHargsN`) at the parameterised block, which §6 of `SpineClause.lean`
had only at the degenerate one.  §5 is the vacuity watch, and §6 records where the *general*
statement bottoms out — `VEnv.StrengtheningTarget`, named precisely, and **not** guessed at.

Nothing here makes the `TrIndDeclN` flip, adds a field to any structure, touches
`tryEtaStructCore.WF` / `isDefEqUnitLike.WF` (`docs/vacuity-ledger.md` row 197), or uses
`VEnv.HasArgs.of_mkApp` — this corner stays `PiInv`-free.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §1 The premise is redundant in general, not merely available at the witness

`D.WF env`'s `params` field is the parameter context's `OnCtx` at the *pre-block* environment;
`OnCtx.mono` with `VEnv.IsType.mono` carries it along any `env ≤ e`.  So a consumer that already
has `D.WF env` and `env ≤ e` — which `csubstTy_WF_of_spineHargsC` does — gets the hypothesis for
free.  `RestrictStepCfg.params₁` (`RestrictStep.lean` §0) is the same argument at the bundled
configuration; this is it as a standalone lemma, so that `SpineClause.lean` §4 can drop the
hypothesis without depending on the bundle. -/

/-- **THE PARAMETER CONTEXT, AT ANY EXTENSION.**  `D.WF env`'s own `params` field, moved up. -/
theorem VInductDecl'.WF.params_le {D : VInductDecl'} {env e : VEnv} (hD : D.WF env)
    (hle : env ≤ e) : OnCtx D.params.reverse (e.IsType D.uvars) :=
  OnCtx.mono (fun h => h.mono hle) hD.params

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e : VEnv}
  {occ : Nat → VNestedOcc}

/-- **`ValAt` FROM THE CHECKER-SIDE CLAUSE, WITH NO PARAMETER-CONTEXT HYPOTHESIS.**
`SpineClause.lean` §4's `valAt_of_spineHargsC` with `hparams` replaced by `D.WF env`, which every
consumer of the clause has anyway.  This is the general form of what §2 does at the witness. -/
theorem valAt_of_spineHargsC_of_wf (hB : D.Built R K env occ) (hS : R.SpineHargsC D K env e)
    (hle : env ≤ e) (hD : D.WF env) (h₂ : env.addIndTypes D = some e₂)
    (hlvl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ l ∈ R.tyLvls j, l.WF D.uvars) : R.ValAt D K e₂ e :=
  valAt_of_spineHargsC hB hS hle (hD.params_le hle) h₂ hlvl

end VIndRestore

/-! ## §2 `ValAt` at the parameterised nested block, unconditionally

The producer is `RestrictCompanion.lean` §8's `ntreeAux_datum_at_stage₁` (the datum at exactly
`addIndTypesC`-env), routed through `SpineClause.lean` §3's equivalence into the checker-side
clause, and then through §4's consumer with the parameter-context premise discharged by
`ntreeAux_params_WF`.  Existentially closed in the style of `ntreeAux_spineHargsC`. -/

namespace InductiveDeclExamples

/-- The level condition at this block: `ntreeRestore.tyLvls j = [.param 0]` for every `j`, and
`ntreeAux.uvars = 1`.  (`ValAtPrice.lean` §7 has the `nfnAux` twin; this is the parameterised
one, where the level is a genuine parameter rather than absent.) -/
theorem ntreeAux_tyLvls_wf : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T →
    T.name ∈ ntreeK → ∀ l ∈ ntreeRestore.tyLvls j, l.WF ntreeAux.uvars :=
  fun j _ _ _ => by rw [show ntreeRestore.tyLvls j = [VLevel.param 0] from rfl]; decide

/-- **`ValAt` AT THE PARAMETERISED NESTED BLOCK — NOTHING HYPOTHESISED.**  The hypothesis
`SpineClause.lean` §6b reported open is gone from the statement, not moved: it is
`ntreeAux_params_WF` at `env := env₃`.

Read against §6b: the clause was already there (`ntreeAux_spineHargsC`); what is here is the
**consumer**, at the block with `uvars = 1`, a non-empty parameter telescope and a
parameter-dependent spine `[NTree.{u} #0]`. -/
theorem ntreeAux_valAt :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      ntreeRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ ∧
      ntreeRestore.ValAt ntreeAux ntreeK env₂ env₃ := by
  obtain ⟨env₁, env₂, env₃, h, h₂, h₃, -, hS⟩ := ntreeAux_datum_at_stage₁
  have hB := ntreeAux_built h
  have hC : ntreeRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ :=
    .of_spineHargsK hB (VInductDecl'.SpineHargsK.of_argsTypedK hS)
  have hle : env₁ ≤ env₃ := by
    rw [VEnv.addIndTypesC] at h₃; exact VEnv.addConstList_le h₃
  exact ⟨env₁, env₂, env₃, h, h₂, h₃, hC,
    VIndRestore.valAt_of_spineHargsC hB hC hle ntreeAux_params_WF h₂ ntreeAux_tyLvls_wf⟩

/-- …and the same thing through §1's general form, so that the parameter-context premise is
discharged **without** the witness-specific `ntreeAux_params_WF`: `ntreeAux_WF'` suffices. -/
theorem ntreeAux_valAt_of_wf :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      ntreeRestore.ValAt ntreeAux ntreeK env₂ env₃ := by
  obtain ⟨env₁, env₂, env₃, h, h₂, h₃, hC, -⟩ := ntreeAux_valAt
  have hle : env₁ ≤ env₃ := by
    rw [VEnv.addIndTypesC] at h₃; exact VEnv.addConstList_le h₃
  exact ⟨env₁, env₂, env₃, h, h₂, h₃,
    VIndRestore.valAt_of_spineHargsC_of_wf (ntreeAux_built h) hC hle ntreeAux_WF' h₂
      ntreeAux_tyLvls_wf⟩

end InductiveDeclExamples

/-! ## §3 What that unlocks: the **general route** to the substitution's `WF`, at this block

`RestrictCompanion.lean` §8 says of the parameterised witness:

> **Not a route.**  `ntreeSubst_WF`'s `val` clause is discharged at this witness by `type_tac` on a
> concrete spine (`List.{u} (NTree.{u} #0)` at `Type u → Type u`) […] Two witnesses with the
> transport are still two witnesses.

With `ValAt` in hand the general route *is* available at this block: `csubstTy_WF_of_val` takes the
`val` clause and supplies the other three fields from general facts about the two stagings.  So the
theorem below has the **same conclusion** as `ntreeSubst_WF` (modulo `ntree_csubstTy`) and a
different provenance: the clause, not `type_tac`.  Stated plainly because the conclusion being
already available is exactly why this is a statement about the route. -/

namespace InductiveDeclExamples

/-- **THE WHOLE TRANSPORT AT THE PARAMETERISED BLOCK, FROM THE CHECKER-SIDE CLAUSE.**  The
substitution's `WF`, the residual `ValAt`, and the datum at `addIndTypesC`-env — the three things
`RestrictCompanion.lean` §11 and `ValAtPrice.lean` §3 price against each other — at one block, one
restoration, one staging, with the nine side conditions read off `ntreeAux_restrictStepCfg`.
Nothing hypothesised. -/
theorem ntreeAux_transport_of_clause :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      ntreeRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ ∧
      ntreeRestore.ValAt ntreeAux ntreeK env₂ env₃ ∧
      (ntreeRestore.csubstTy ntreeAux ntreeK).WF env₂ env₃ ntreeAux.uvars ∧
      ntreeAux.ArgsTypedK ntreeK env₃ (fun _ => listOcc) := by
  obtain ⟨env₁, env₂, env₃, h, h₂, h₃, hC, hval⟩ := ntreeAux_valAt
  have h₃' : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ := by
    rwa [VEnv.addIndTypesC] at h₃
  have C := ntreeAux_restrictStepCfg h h₂ h₃'
  exact ⟨env₁, env₂, env₃, h, h₂, h₃, hC, hval,
    VIndRestore.csubstTy_WF_of_val C.ordered C.ordered₁ C.wf C.fresh C.closed C.stage₂ C.stage₁
      hval, ntreeAux_argsTypedK_restrict h h₂ h₃'⟩

/-- …and the substitution's `WF` alone, for a consumer that wants only that conjunct. -/
theorem ntreeAux_csubstTy_WF_of_clause :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      (ntreeRestore.csubstTy ntreeAux ntreeK).WF env₂ env₃ ntreeAux.uvars := by
  obtain ⟨env₁, env₂, env₃, h, h₂, h₃, -, -, hWF, -⟩ := ntreeAux_transport_of_clause
  exact ⟨env₁, env₂, env₃, h, h₂, h₃, hWF⟩

/-! ## §4 The `TrIndDeclN` field text, at the parameterised block

`SpineClause.lean` §5 states the clause as a `TrIndDeclN` field would read it
(`VIndRestore.SpineHargsN`, guarded by `types.length ≤ j` and staged over the `addIndTypesC`
premise), and §6a exhibits it at the **degenerate** block only (`nfnAux_spineHargsN`,
`uvars = 0`, `params = []`).  Here it is at the parameterised one, so the producer side of the
field has a closed instance where the parameter telescope is non-empty. -/

/-- The user's declaration, syntactically:
`inductive NTree (α : Type u) | node : α → List (NTree α) → NTree α`.  Spliced from the real
Lean constant, as `nfnIndType` is, so it cannot drift from `NTree`. -/
def ntreeIndType : Lean.InductiveType :=
  { name := ``NTree, type := exprOf% NTree,
    ctors := [{ name := ``NTree.node, type := exprOf% NTree.node }] }

/-- The two guard styles agree at this block: `NTree` is the declared member (`j = 0`), the
auxiliary `_nested.List_1` is the companion (`j = 1`), and the user's declaration list has
length `1`. -/
theorem ntreeAux_companions : ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T →
    (T.name ∈ ntreeK ↔ ([ntreeIndType] : List Lean.InductiveType).length ≤ j) := by
  rintro (_ | _ | j) T hT <;> simp only [ntreeAux] at hT <;> [skip; skip; simp at hT] <;>
    cases hT <;> simp [ntreeK]

/-- **THE FIELD TEXT IS SATISFIABLE AT THE PARAMETERISED NESTED WITNESS.**  `SpineHargsN` in
`TrIndDeclN`'s own guard style, staged over the `addIndTypesC` premise the way `trCtors` is, at
`uvars = 1` with a non-empty parameter telescope.  Existentially closed. -/
theorem ntreeAux_spineHargsN :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      ntreeRestore.SpineHargsN ntreeAux ntreeK env₁ [ntreeIndType] := by
  obtain ⟨env₁, -, env₃, h, -, h₃, hC, -⟩ := ntreeAux_valAt
  refine ⟨env₁, h, VIndRestore.spineHargsN_of_spineHargsC ntreeAux_companions ?_⟩
  intro env₁' h₁
  cases Option.some.inj (h₁.symm.trans h₃)
  exact hC

/-! ## §5 Vacuity watch: this witness is the non-degenerate one, and every premise fires

`docs/handoff-valat.md` §4 records the sibling block `nfnAux` as degenerate — `uvars = 0`,
`params = []`, so the parameter-context hypotheses are `trivial` there — and that is precisely the
witness this file must **not** silently fall back to.  The four `example`s below are the
non-degeneracy, by computation; then two theorems check that the two premises which could make
§2's statements inert actually have witnesses. -/

/-- Non-degeneracy 1: one universe parameter, so `IsType 1` is not `IsType 0`. -/
example : ntreeAux.uvars = 1 := rfl
/-- Non-degeneracy 2: the parameter telescope is **not** empty, so `OnCtx … (·.IsType 1)` is not
`trivial` — it is the `⟨trivial, _, .sort _⟩` of `ntreeAux_params_WF`. -/
example : ntreeAux.params = [.sort (.succ (.param 0))] := rfl
/-- Non-degeneracy 3: the presented spine at the companion member is **parameter-dependent** —
`NTree.{u} #0` mentions the block's own bound parameter, so the `HasArgs` is a genuine `.cons`
against a one-binder telescope, not `.nil`. -/
example : ntreeRestore.tyArgs 1 = [.app (.const ``NTree [.param 0]) (.bvar 0)] := rfl
/-- Non-degeneracy 4: `ntreeK ≠ []`, so `SpineClause.lean` §6's collapse test does not apply and
the clause is not vacuously true. -/
example : ntreeK = [`_nested.List_1] := rfl

/-- …and for contrast, the block this file is **not** using — the degeneracy
`docs/handoff-valat.md` §4 warns about. -/
example : nfnAux.uvars = 0 ∧ nfnAux.params = [] := ⟨rfl, rfl⟩

/-- **THE CLAUSE'S `∀ ci` PREMISE FIRES HERE.**  `SpineHargsC` reads *"for every `ci` the
pre-block environment declares at the presented head"*, which would be vacuous if the head were
undeclared.  At this witness the presented head is `List`, and `env₁` declares it. -/
theorem ntreeAux_spineHargsC_lookup :
    ∃ env₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.constants (ntreeRestore.tyName 1) = some ⟨listOcc.decl.uvars, listOcc.src.type⟩ := by
  obtain ⟨env₁, -, -, h, -, -, -, -⟩ := ntreeAux_valAt
  exact ⟨env₁, h, VIndRestore.built_ty_const (ntreeAux_built h)
    (show ntreeAux.types[1]? = some _ from rfl) (by decide)⟩

/-- **AND `ValAt` FIRES AT A REAL CONSTANT.**  `ValAt` is a `∀` over `csubstTy`'s domain; if that
domain missed `env₂`'s constants it would hold for nothing.  It does not: `_nested.List_1` is in
the domain with value `ntreeVal`, `env₂` declares it at `Type u → Type u`, and §2's `ValAt`
delivers that typing at `env₃`.  So `ntreeAux_valAt` moves a real judgement. -/
theorem ntreeAux_valAt_fires :
    ∃ env₂ env₃ : VEnv,
      ntreeRestore.csubstTy ntreeAux ntreeK `_nested.List_1 = some ntreeVal ∧
      env₂.constants `_nested.List_1
        = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ ∧
      env₃.HasType 1 [] ntreeVal
        (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) := by
  obtain ⟨_, env₂, env₃, -, h₂, -, -, hval⟩ := ntreeAux_valAt
  exact ⟨env₂, env₃, ntree_csubst_ty_val, nlist_const_staged h₂,
    hval ntree_csubst_ty_val (nlist_const_staged h₂)⟩

end InductiveDeclExamples

/-! ## §6 Where the general statement bottoms out — named, not guessed

§§2–5 are the *witness*.  The general question — the checker-side clause at `addIndTypesC`-env for
an **arbitrary** block — does not follow from anything here, and this section says exactly what it
is instead of guessing.

`RestrictStep.lean` §2 proves `D.ArgsTypedK K e₁ occ ↔ R.ValStrengthen D K e₂ e₁` at a
`RestrictStepCfg` given the datum at `e₂`, and proves both endpoints of `ValStrengthen`'s judgement
`e₁`-clean, so that node is a **plain** instance of `VEnv.AxiomConservativityWF`.  What is added
here is the same equivalence at the **checker-side** form of the clause, which is the form
`TrIndDeclN` can carry: `SpineHargsC` is *also* on that cycle, hence also exactly the
strengthening instance.  So:

* the clause is not a cheaper door than the hole, and
* the hole is `VEnv.AxiomConservativityWF`, which `Theory/Typing/ConstVar.lean`'s
  `VEnv.axiomConservativityWF_iff_target` proves equivalent to `VEnv.StrengtheningTarget`
  (`Theory/Typing/Strengthen.lean`), which is the **forward direction of
  `Lean4Lean.VEnv.IsDefEqU.weakN_iff`** — the `sorry` at `Theory/Typing/UniqueTyping.lean:193`,
  inside the declaration reported at `UniqueTyping.lean:191`.  That is the hole, precisely, and
  this file stops there rather than attempting it.

Note what §2 does **not** claim, then: not that the general clause is proved, only that the one
hypothesis §6b of `SpineClause.lean` reported open was never a hypothesis. -/

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e₁ : VEnv}
  {occ : Nat → VNestedOcc}

/-- **THE CHECKER-SIDE CLAUSE IS ON THE CYCLE TOO** — hence it *is* the strengthening instance,
and no cheaper than it.  `SpineClause.lean` §3's equivalence composed with
`RestrictStep.lean` §2's five-node cycle. -/
theorem spineHargsC_iff_valStrengthen (C : RestrictStepCfg D R K env e₂ e₁ occ)
    (H₂ : D.ArgsTypedK K e₂ occ) :
    R.SpineHargsC D K env e₁ ↔ R.ValStrengthen D K e₂ e₁ :=
  ⟨fun hC => cyc_val_to_strengthen (cyc_spine_to_val C (hC.toSpineHargsK C.built)),
   fun hs => .of_spineHargsK C.built
     (cyc_datum_to_spine (cyc_val_to_datum C H₂ (cyc_strengthen_to_val C H₂ hs)))⟩

end VIndRestore

end Lean4Lean

/-! ## §7 Grading: hole-freeness, per declaration

Every line is hole-freeness and nothing else (`docs/vacuity-ledger.md` §0); inhabitation and
non-degeneracy are §5.  Names read off this file's own `namespace` lines. -/

#print axioms Lean4Lean.VInductDecl'.WF.params_le
#print axioms Lean4Lean.VIndRestore.valAt_of_spineHargsC_of_wf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_tyLvls_wf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_valAt
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_valAt_of_wf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_transport_of_clause
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_csubstTy_WF_of_clause
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_companions
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_spineHargsN
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_spineHargsC_lookup
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_valAt_fires
#print axioms Lean4Lean.VIndRestore.spineHargsC_iff_valStrengthen
#print axioms Lean4Lean.InductiveDeclExamples.ntreeIndType
