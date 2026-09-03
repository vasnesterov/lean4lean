import Lean4Lean.Verify.Inductive.ValAtPrice

/-!
# The checker-side spine clause, in a form `TrIndDeclN` can actually carry

`docs/handoff-valat.md` §5 item 1 settled *what* the checker owes the nested `AddInduct` flip:

> `VInductDecl'.SpineHargsK D K e₁ occ` — for each companion member, **one `HasArgs`** stating that
> the presented spine instantiates the foreign member's parameter telescope, at
> `e₁ = env.addIndTypesC D K`.  State the `TrIndDeclN` / `RestoreData` clause in this form.

This file does that, and the first thing it finds is that **`SpineHargsK` is the right content in
the wrong form**: `SpineHargsK` mentions the occurrence data `occ : Nat → VNestedOcc`, which
`TrIndDeclN` does not carry, and existentialising `occ` is *vacuous* (§2a below is the machine-
checked proof of that, so this is not a stylistic objection).  So the clause has to be restated over
data the checker side has — `R.tyName`, `R.tyLvls`, `R.tyArgs` and the pre-block environment — and
the question is whether the restatement is the same statement.

**It is, exactly, and that is the result** (§3): under `VInductDecl'.Built` the occurrence-free
clause `VIndRestore.SpineHargsC` and `VInductDecl'.SpineHargsK` are **equivalent** — hole-free, no
`VEnv.HasArgs.of_mkApp`, and with **no length side condition**, because `VNestedOcc.Occurs.args_len`
already forces `(occ j).args.length = (occ j).decl.np`.  That last point is what makes the
restatement free: the foreign block's parameter count, the one piece of `occ` the telescope needs,
is `(R.tyArgs j).length`, which is checker-side data.

So the price of the clause is unchanged in content and its form is now statable.  §4 wires it to the
consumers (`ValAt`, hence `csubstTy_WF_of_val`, hence the whole nested transport), §5 states it in
`TrIndDeclN`'s own guard style (`types.length ≤ j` rather than `T.name ∈ K`) and bridges the two,
and §6 instantiates the whole chain at the `NFn`/`PFn` block with nothing hypothesised.

**The flip is not made here**, no field is added to any structure (`docs/handoff-spineclause.md` §4
is the measured ripple of that edit instead), and `tryEtaStructCore.WF` / `isDefEqUnitLike.WF`
(`docs/vacuity-ledger.md` row 197) are untouched.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (splitPis mkPi)

/-! ## §1 One library lemma: `splitPis` is determined by the length it produces

`splitPis n e` truncates silently when `e` runs out of pis, so `n` is *not* recoverable from the
result in general.  What *is* true, and is all §3 needs, is that the telescope's own length
determines the split: if `splitPis n e` produced `m` binders then `splitPis m e` is the same split.
`Theory/Inductive/Decl.lean` has `splitPis_mkPi` (the round trip at a syntactic `mkPi`) but not
this. -/

namespace VExpr

/-- **`splitPis` is idempotent in its count.**  If `n` splits produce `m` binders, then `m` splits
produce the same thing — in both the truncating and the non-truncating case. -/
theorem splitPis_length_self : ∀ (n : Nat) (e : VExpr),
    splitPis (splitPis n e).1.length e = splitPis n e
  | 0, e => rfl
  | n+1, .forallE A B => by
    have ih := splitPis_length_self n B
    rw [splitPis]
    simp only [List.length_cons]
    rw [splitPis, ih]
  | _+1, .bvar _ => rfl
  | _+1, .sort _ => rfl
  | _+1, .const .. => rfl
  | _+1, .app .. => rfl
  | _+1, .lam .. => rfl

/-- …hence a `splitPis` split whose telescope has length `m` **is** the `m`-split, in the form the
rewrite is wanted. -/
theorem splitPis_eq_of_length {n m : Nat} {e : VExpr} (h : (splitPis n e).1.length = m) :
    splitPis m e = splitPis n e := by
  rw [← h]; exact splitPis_length_self n e

end VExpr

/-! ## §2 The clause, over checker-side data only

`VIndRestore.declTele` (`Theory/Inductive/HargsShared.lean` §2) is
`(splitPis np (ci.type.instL (R.tyLvls j))).1` — the presented head's declared telescope after `np`
splits, i.e. exactly `SpineHargsK`'s telescope with `ci.type` in place of `(occ j).src.type` and
`R.tyLvls j` in place of `(occ j).lvls`.  `Built.tyName`/`Occurs.ty_const` identify `ci`, so the
only genuinely `occ`-valued input left is the split count `(occ j).decl.np` — and `Occurs.args_len`
says that is `(occ j).args.length = (R.tyArgs j).length`.

So the clause below mentions **no `occ` and no `npJ`**: it is stated at the pre-block environment
`env` (where the presented head is declared) and the target environment `e` (where the spine is
typed), which are exactly the two environments `TrIndDeclN` has — its own `env` and the `env₁` of
its `addIndTypesC` premise. -/

namespace VIndRestore

/-- **THE CHECKER-SIDE CLAUSE.**  For each companion member `j`: the presented spine `R.tyArgs j`
instantiates the presented head's declared parameter telescope, at the target environment.

`SpineHargsK` (`Verify/Inductive/ValAtPrice.lean` §3) with the occurrence data replaced by the
restoration's own, and the split count read off the spine.  §3 proves the two are the same
statement under `Built`. -/
def SpineHargsC (R : VIndRestore) (D : VInductDecl') (K : List Name) (env e : VEnv) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
      e.HasArgs D.uvars D.params.reverse (R.declTele ci (R.tyArgs j).length j) (R.tyArgs j)

end VIndRestore

/-! ### §2a Why the `occ` form is not available as a clause

Not an argument about taste: `TrIndDeclN` carries no `occ`, so a clause stated as `SpineHargsK`
would have to existentialise it — and the existential is **provably trivial**.  Reported because
"state the clause as `SpineHargsK`" reads as a cheap edit until this is on the page. -/

/-- **`∃ occ, SpineHargsK` IS VACUOUS.**  For every block, every companion list and every
environment.  The witness takes each occurrence to a `0`-parameter block with an empty spine, so
every conjunct is `HasArgs.nil`. -/
theorem VInductDecl'.exists_spineHargsK (D : VInductDecl') (K : List Name) (e : VEnv) :
    ∃ occ : Nat → VNestedOcc, D.SpineHargsK K e occ :=
  ⟨fun _ => { decl := default, idx := 0, lvls := [], args := [],
              auxName := .anonymous, ctorName := id },
   fun _ _ _ _ => .nil⟩

/-! ## §3 The two forms are the same statement, under `Built`

Both directions, hole-free, and neither uses `VEnv.HasArgs.of_mkApp`.  The whole content is
`VNestedOcc.Occurs.args_len` — `(occ j).args.length = (occ j).decl.np`, a field of `Occurs` since it
was `replaceIfNested`'s `assert! I_nparams ≤ args.size` — plus `Occurs.ty_const` to pin the declared
constant.  Note what is *not* needed: no `e.WF`, no `Ordered`, no `hlen` side condition of the kind
`VIndRestore.hargs_of_spineTyped` (`HargsShared.lean` §2) has to take, and no `Faithful`. -/

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e : VEnv}
  {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}

/-- The declared constant behind a companion member's presented head, from `Built`. -/
theorem built_ty_const (hB : D.Built R K env occ) (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    env.constants (R.tyName j) = some ⟨(occ j).decl.uvars, (occ j).src.type⟩ := by
  rw [hB.tyName j T hT hK]; exact (hB.occurs j T hT hK).toOccurs.ty_const

/-- The split count, off `occ` and onto the spine: `Occurs.args_len` with `Built.tyArgs`. -/
theorem built_tyArgs_length (hB : D.Built R K env occ) (hT : D.types[j]? = some T)
    (hK : T.name ∈ K) : (R.tyArgs j).length = (occ j).decl.np := by
  rw [hB.tyArgs j T hT hK]; exact (hB.occurs j T hT hK).toOccurs.args_len

/-- The clause's telescope **is** `SpineHargsK`'s, at the declared constant. -/
theorem declTele_eq_of_built (hB : D.Built R K env occ) (hT : D.types[j]? = some T)
    (hK : T.name ∈ K) :
    R.declTele ⟨(occ j).decl.uvars, (occ j).src.type⟩ (R.tyArgs j).length j
      = (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1 := by
  rw [VIndRestore.declTele, built_tyArgs_length hB hT hK, hB.tyLvls j T hT hK]

/-- **THE CLAUSE ⟹ THE RESIDUAL.**  The direction the consumers need. -/
theorem SpineHargsC.toSpineHargsK (hB : D.Built R K env occ) (hS : R.SpineHargsC D K env e) :
    D.SpineHargsK K e occ := by
  intro j T hT hK
  have h := hS j T hT hK _ (built_ty_const hB hT hK)
  rw [declTele_eq_of_built hB hT hK, hB.tyArgs j T hT hK] at h
  exact h

/-- **THE RESIDUAL ⟹ THE CLAUSE.**  The direction that says the restatement asks the producer for
nothing new: whatever `SpineHargsK` gives, the checker-side form is already there. -/
theorem SpineHargsC.of_spineHargsK (hB : D.Built R K env occ) (hS : D.SpineHargsK K e occ) :
    R.SpineHargsC D K env e := by
  intro j T hT hK ci hci
  cases Option.some.inj ((built_ty_const hB hT hK).symm.trans hci)
  rw [declTele_eq_of_built hB hT hK, hB.tyArgs j T hT hK]
  exact hS j T hT hK

/-- **…so the two forms are interchangeable**, which is the result: the clause may be stated over
checker-side data without changing what is being asked for. -/
theorem spineHargsC_iff_spineHargsK (hB : D.Built R K env occ) :
    R.SpineHargsC D K env e ↔ D.SpineHargsK K e occ :=
  ⟨fun h => h.toSpineHargsK hB, fun h => .of_spineHargsK hB h⟩

end VIndRestore

/-! ## §4 The consumers, wired

`ValAt` from the clause is `valAt_of_spineHargsK` (`ValAtPrice.lean` §3) composed with §3.  From
`ValAt`, `RestrictCompanion.lean` §11's `csubstTy_WF_of_val` and `ArgsTypedK.restrict_of_val` are the
rest of the transport; those are stated over `ValAt` and take it as a hypothesis, so nothing further
is needed here — the clause reaches them. -/

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ e : VEnv}
  {occ : Nat → VNestedOcc}

/-- **`ValAt` FROM THE CHECKER-SIDE CLAUSE.**  `valAt_of_spineHargsK` with the clause in place of
the `occ`-form residual. -/
theorem valAt_of_spineHargsC (hB : D.Built R K env occ) (hS : R.SpineHargsC D K env e)
    (hle : env ≤ e) (hparams : OnCtx D.params.reverse (e.IsType D.uvars))
    (h₂ : env.addIndTypes D = some e₂)
    (hlvl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ l ∈ R.tyLvls j, l.WF D.uvars) : R.ValAt D K e₂ e :=
  valAt_of_spineHargsK hB (hS.toSpineHargsK hB) hle hparams h₂ hlvl

/-- **THE SUBSTITUTION'S WELL-FORMEDNESS FROM THE CHECKER-SIDE CLAUSE.**  `ValAt` was the fourth
and only remaining field of `(R.csubstTy D K).WF`; `csubstTy_WF_of_val` supplies the other three.
So this is the whole nested transport's hypothesis, restated over data the checker has.

**No `hparams`.**  The first version of this theorem took `valAt_of_spineHargsC`'s
`OnCtx D.params.reverse (e.IsType D.uvars)` as a hypothesis of its own.  It never had to:
`D.WF env`'s `params` field *is* that `OnCtx` at the pre-block environment, and `OnCtx.mono`
carries it along `hle` — both of which this theorem already takes.  (`RestrictStep.lean` §0's
`RestrictStepCfg.params₁` is the same argument at the bundled configuration, and
`Verify/Inductive/ValAtParam.lean` §1 states it as `VInductDecl'.WF.params_le`.) -/
theorem csubstTy_WF_of_spineHargsC (hB : D.Built R K env occ) (hS : R.SpineHargsC D K env e)
    (hle : env ≤ e)
    (henv : env.Ordered) (he : e.Ordered) (hD : D.WF env)
    (hf : (R.csubstTy D K).FreshIn env) (hcl : (R.csubstTy D K).Closed)
    (h₂ : env.addIndTypes D = some e₂) (h₁ : env.addIndTypesC D K = some e)
    (hlvl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ l ∈ R.tyLvls j, l.WF D.uvars) :
    (R.csubstTy D K).WF e₂ e D.uvars :=
  csubstTy_WF_of_val henv he hD hf hcl h₂ h₁ (valAt_of_spineHargsC hB hS hle
    (OnCtx.mono (fun h => h.mono hle) hD.params) h₂ hlvl)

end VIndRestore

/-! ## §5 The clause in `TrIndDeclN`'s own guard style

`TrIndDeclN` guards its companion-tail clauses by `types.length ≤ j`, not by `T.name ∈ K`; the two
are interchanged by its `companions` field.  `SpineHargsN` below is the clause exactly as the field
would read, staged over the `addIndTypesC` premise the way `trCtors` is, and `spineHargsC_of_N` is
the bridge.  `declTele` is a `Theory` abbreviation `InductR.lean` does not import, so the field
would spell it out; that is a transcription, not a difference. -/

/-- **THE CLAUSE AS A `TrIndDeclN` FIELD WOULD READ IT** — verbatim, modulo `declTele` being spelled
out.  Guarded by `types.length ≤ j` and staged over the `addIndTypesC` premise exactly as `trCtors`
is; the parameters are `TrIndDeclN`'s own `env`, `types`, `D`, `K`, `R` and **nothing else** — no
`occ`, no `npJ`. -/
def VIndRestore.SpineHargsN (R : VIndRestore) (D : VInductDecl') (K : List Name) (env : VEnv)
    (types : List Lean.InductiveType) : Prop :=
  ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → types.length ≤ j →
      ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
        env₁.HasArgs D.uvars D.params.reverse
          (R.declTele ci (R.tyArgs j).length j) (R.tyArgs j)

/-- **The bridge, in the form a consumer of `TrIndDeclN` would use it.**  `companions` turns the
index guard into the name guard and the staging premise is discharged where the consumer has it, so
the field *is* `SpineHargsC` at `(env, env₁)` — and hence, by §3/§4, `ValAt` and the transport. -/
theorem VIndRestore.spineHargsC_of_spineHargsN {R : VIndRestore} {D : VInductDecl'} {K : List Name}
    {env env₁ : VEnv} {types : List Lean.InductiveType}
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → (T.name ∈ K ↔ types.length ≤ j))
    (h₁ : env.addIndTypesC D K = some env₁) (h : R.SpineHargsN D K env types) :
    R.SpineHargsC D K env env₁ :=
  fun j T hT hK => h env₁ h₁ j T hT ((hcomp j T hT).1 hK)

/-- …and back, so the two guard styles are interchangeable and the field text above is not
secretly stronger than §2's clause. -/
theorem VIndRestore.spineHargsN_of_spineHargsC {R : VIndRestore} {D : VInductDecl'} {K : List Name}
    {env : VEnv} {types : List Lean.InductiveType}
    (hcomp : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → (T.name ∈ K ↔ types.length ≤ j))
    (h : ∀ env₁, env.addIndTypesC D K = some env₁ → R.SpineHargsC D K env env₁) :
    R.SpineHargsN D K env types :=
  fun env₁ h₁ j T hT hj => h env₁ h₁ j T hT ((hcomp j T hT).2 hj)

/-! ## §6 Collapse test, and then instantiation

At `K = []` the clause is vacuous, so all of §§3–4's content lives at `K ≠ []`; both of the tree's
nested witnesses are there. -/

theorem VIndRestore.spineHargsC_nil {R : VIndRestore} {D : VInductDecl'} {env e : VEnv} :
    R.SpineHargsC D [] env e := fun _ _ _ hK => nomatch hK

/-! ### §6a Inhabitation, stated separately from hole-freeness

`docs/vacuity-ledger.md` §0: the `#print axioms` lines in §7 are hole-freeness and nothing else.
This is the other question, and it is answered by instantiation.

Two ways the clause could be inert, and both are closed:

* **the `∀ ci` premise could have no witness.**  `SpineHargsC` reads *"for every `ci` the pre-block
  environment declares at the presented head"*, which is vacuously true when the head is undeclared.
  It never is, under `Built`: `built_ty_const` (§3) produces the lookup in general, and
  `nfnAux_spineHargsC_lookup` below exhibits it at the witness.
* **`K` could be empty**, which is §6's collapse test; `nfnK ≠ []` at the witness
  (`NestedWit.nfnK_companion`, read off `ArgsTypedSupply.lean` §4.1) and the presented spine is
  `[NFn]`, not `[]`, so the `HasArgs` at the companion member is a genuine `.cons`. -/

namespace NestedWit
open InductiveDeclExamples

/-- The clause's `∀ ci` premise fires at the witness: `env₂` really declares `PFn`. -/
theorem nfnAux_spineHargsC_lookup :
    ∃ env₂ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.constants (nfnRestore'.tyName 1) = some ⟨pfnOcc.decl.uvars, pfnOcc.src.type⟩ := by
  obtain ⟨env₂, F₁, h, -⟩ := nfnAux_stage₁_exists
  exact ⟨env₂, h, VIndRestore.built_ty_const (nfnAux_built'_of_blockK h)
    (show nfnAux.types[1]? = some _ from rfl) (by decide)⟩

/-- **THE CLAUSE, AND THE WHOLE RESIDUAL FROM IT, AT THE `NFn`/`PFn` BLOCK.**  Existentially
closed: no free variables, nothing hypothesised.  The clause is established in its
**checker-side** form (`SpineHargsC`, over `nfnRestore'` and `env₂`, no `occ` in the statement) and
`ValAt` — hence `csubstTy_WF_of_val`, hence the nested transport — comes out of it. -/
theorem nfnAux_valAt_of_spineHargsC :
    ∃ env₂ E₁ F₁ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addIndTypes nfnAux = some E₁ ∧ env₂.addIndTypesC nfnAux nfnK = some F₁ ∧
      nfnRestore'.SpineHargsC nfnAux nfnK env₂ F₁ ∧
      nfnRestore'.ValAt nfnAux nfnK E₁ F₁ := by
  obtain ⟨env₂, F₁, h, hF₁⟩ := nfnAux_stage₁_exists
  obtain ⟨E₁, h₃⟩ := nfnAux_staged_exists h
  have hB := nfnAux_built'_of_blockK h
  have hS : nfnRestore'.SpineHargsC nfnAux nfnK env₂ F₁ :=
    .of_spineHargsK hB (VInductDecl'.SpineHargsK.of_argsTypedK (nfnAux_argsTypedK hF₁))
  refine ⟨env₂, E₁, F₁, h, h₃, by rw [VEnv.addIndTypesC]; exact hF₁, hS, ?_⟩
  exact VIndRestore.valAt_of_spineHargsC hB hS (VEnv.addConstList_le hF₁) (by exact trivial) h₃
    nfnAux_tyLvls_wf

/-- **THE FIELD TEXT IS SATISFIABLE AT THE NESTED WITNESS**, in `TrIndDeclN`'s own guard style and
staged over the `addIndTypesC` premise the way `trCtors` is.  So §5's `SpineHargsN` is not merely a
transcription that typechecks: the producer side of the field has a closed instance.

(The environment argument is universally quantified inside `SpineHargsN`, and `addIndTypesC` is a
function, so the staging premise pins it to `nfnAux_stage₁_exists`' own `F₁`.) -/
theorem nfnAux_spineHargsN :
    ∃ env₂ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      nfnRestore'.SpineHargsN nfnAux nfnK env₂ [nfnIndType] := by
  obtain ⟨env₂, F₁, h, hF₁⟩ := nfnAux_stage₁_exists
  refine ⟨env₂, h, VIndRestore.spineHargsN_of_spineHargsC ?_ ?_⟩
  · rintro (_ | _ | j) T hT <;> simp only [nfnAux] at hT <;> [skip; skip; simp at hT] <;>
      cases hT <;> simp [nfnK]
  · intro env₁ h₁
    rw [VEnv.addIndTypesC] at h₁
    cases Option.some.inj (h₁.symm.trans hF₁)
    exact .of_spineHargsK (nfnAux_built'_of_blockK h)
      (VInductDecl'.SpineHargsK.of_argsTypedK (nfnAux_argsTypedK hF₁))

/-- **The round trip at the witness.**  §3's equivalence is not one-way at a real block: the
checker-side clause and the `occ`-form residual imply each other there. -/
theorem nfnAux_spineHargsC_iff :
    ∃ env₂ F₁ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addIndTypesC nfnAux nfnK = some F₁ ∧
      (nfnRestore'.SpineHargsC nfnAux nfnK env₂ F₁ ↔ nfnAux.SpineHargsK nfnK F₁ (fun _ => pfnOcc)) := by
  obtain ⟨env₂, F₁, h, hF₁⟩ := nfnAux_stage₁_exists
  exact ⟨env₂, F₁, h, by rw [VEnv.addIndTypesC]; exact hF₁,
    VIndRestore.spineHargsC_iff_spineHargsK (nfnAux_built'_of_blockK h)⟩

end NestedWit

/-! ### §6b …and at the **parameterised** block, where the degeneracy is gone

`docs/handoff-valat.md` §4 discloses that `nfnAux` has `uvars = 0` and `params = []`, so the
context-shaped hypotheses are `trivial` there, and reports that §3 was *not* instantiated at
`ntreeAux` (`NTree α` with a `List (NTree α)` field, `np = 1`, `uvars = 1` — the block Lean's own
kernel runs the nested elimination on).  This closes that gap for the clause itself: the spine is
`[NTree.{u} #0]`, a *parameter-dependent* one, and the parameter telescope is non-empty.

The clause is produced from `RestrictCompanion.lean` §8's `ntreeAux_datum_at_stage₁`, which is the
datum at exactly `addIndTypesC`-env.

**Correction (2026-09-03).**  This paragraph used to end: *"`ValAt` from it additionally needs
`OnCtx ntreeAux.params.reverse (env₃.IsType 1)`, which is not `trivial` at this block and is **not
supplied here** — that is the one hypothesis of §4 still open at the parameterised witness."*  That
was **wrong on both counts**, and `Verify/Inductive/ValAtParam.lean` is the correction:

* the premise was already proved, hole-free, at exactly this block —
  `InductiveDeclExamples.ntreeAux_params_WF` (`Theory/Inductive/NestedHead.lean`), which is that
  `OnCtx` verbatim at `env := env₃` since `ntreeAux.uvars = 1` literally;
* and it was never a hypothesis of §4 at all: `VInductDecl'.WF.params` **is** that `OnCtx` at the
  pre-block environment, so `OnCtx.mono` along `env ≤ e` derives it for **any** block from data
  `csubstTy_WF_of_spineHargsC` already takes.  §4's statement is weakened accordingly above —
  `hparams` is gone from it — and `ValAtParam.lean` §1 states the general lemma
  (`VInductDecl'.WF.params_le`) and §2 delivers `ValAt` at this block unconditionally
  (`ntreeAux_valAt`), with §3 running the whole transport there from the clause. -/

namespace InductiveDeclExamples

/-- **THE CHECKER-SIDE CLAUSE AT THE PARAMETERISED NESTED BLOCK.**  Existentially closed. -/
theorem ntreeAux_spineHargsC :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      ntreeRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ := by
  obtain ⟨env₁, env₂, env₃, h, h₂, h₃, -, hS⟩ := ntreeAux_datum_at_stage₁
  exact ⟨env₁, env₂, env₃, h, h₂, h₃,
    .of_spineHargsK (ntreeAux_built h) (VInductDecl'.SpineHargsK.of_argsTypedK hS)⟩

end InductiveDeclExamples

end Lean4Lean

/-! ## §7 Grading: hole-freeness, per declaration

Every line is hole-freeness and nothing else (`docs/vacuity-ledger.md` §0); inhabitation is §6a.
Names read off this file's own `namespace` lines. -/

#print axioms Lean4Lean.VExpr.splitPis_length_self
#print axioms Lean4Lean.VExpr.splitPis_eq_of_length
#print axioms Lean4Lean.VInductDecl'.exists_spineHargsK
#print axioms Lean4Lean.VIndRestore.built_ty_const
#print axioms Lean4Lean.VIndRestore.built_tyArgs_length
#print axioms Lean4Lean.VIndRestore.declTele_eq_of_built
#print axioms Lean4Lean.VIndRestore.SpineHargsC.toSpineHargsK
#print axioms Lean4Lean.VIndRestore.SpineHargsC.of_spineHargsK
#print axioms Lean4Lean.VIndRestore.spineHargsC_iff_spineHargsK
#print axioms Lean4Lean.VIndRestore.valAt_of_spineHargsC
#print axioms Lean4Lean.VIndRestore.csubstTy_WF_of_spineHargsC
#print axioms Lean4Lean.VIndRestore.spineHargsC_of_spineHargsN
#print axioms Lean4Lean.VIndRestore.spineHargsN_of_spineHargsC
#print axioms Lean4Lean.VIndRestore.spineHargsC_nil
#print axioms Lean4Lean.NestedWit.nfnAux_spineHargsC_lookup
#print axioms Lean4Lean.NestedWit.nfnAux_valAt_of_spineHargsC
#print axioms Lean4Lean.NestedWit.nfnAux_spineHargsN
#print axioms Lean4Lean.NestedWit.nfnAux_spineHargsC_iff
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_spineHargsC
#print axioms Lean4Lean.VIndRestore.SpineHargsC
#print axioms Lean4Lean.VIndRestore.SpineHargsN
