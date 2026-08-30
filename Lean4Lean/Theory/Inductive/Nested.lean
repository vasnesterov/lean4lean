import Lean4Lean.Theory.Inductive.Lemmas
import Lean4Lean.Theory.Typing.DeltaUnique
import Lean4Lean.Theory.Inductive.DeclExamples

/-!
# What `VInductDecl'` can and cannot declare

`docs/design-inductive.md` §9.3 and `bugs-found.md` item 11 both assert, in prose, that
`VInductDecl'` expresses only the *post-reduction mutual* form of an inductive block, and
therefore cannot model what `Environment.addInductive` does for a **nested** declaration.
This file turns that assertion into theorems, so that the claim cannot rot and so that a
later attempt to model nested blocks without changing `VInductDecl'` fails loudly.

The three facts, all corollaries of `VEnv.addInduct'_eq_some_iff`:

* `addInduct'_type_fresh` — every type of a block is a **newly declared** constant.  So a
  `VIndType` can never name an already-declared inductive `J`: the "companion type" of §9.3
  is not merely unrepresented, it is *ruled out* by `addInduct'` returning `none`.
* `addInduct'_no_companion` — the same fact in refutation form.
* `addInduct'_new_name` — the only names a block introduces are its type names, its
  constructor names, and `mkRecName` of its type names.  In particular a block cannot
  introduce a recursor under any other name, which is what the nested path's
  `mkAuxRecNameMap` does (`Inductive/Add.lean`: the auxiliary recursors are re-added as
  `(mkRecName mainName).appendIndexAfter i`).

Read together: for a nested declaration the final environment contains

* a recursor named `Foo.rec_1`, which no `VInductDecl'` can introduce
  (`addInduct'_new_name`), and
* no `_nested.List_1` constants at all, although the block that was actually checked
  declared them,

so it is `addInduct' env D` for no `D` whatsoever.  This is the gap the `TrEnv'.induct` rule
inherits (`Verify/Environment/Induct.lean`, "Non-nested only").

**Non-vacuity.**  The shared hypothesis `env.addInduct' D = some env'` is satisfiable by
`rfl`: `Theory/Inductive/DeclExamples.lean` has `fooEnv_eq : ∃ e, VEnv.empty.addInduct'
fooDecl = some e`, and `isSome` examples for `natDecl`, `mutDecl`, `accDecl`, `eqDecl`,
`iffDecl`, `nonemptyDecl` and `lvlDecl`.  `addInduct'_no_companion` is a *refutation*, so
its own hypotheses are jointly unsatisfiable by design — that is its content — but each is
individually realisable and the proof uses both.
-/

namespace Lean4Lean

namespace VEnv
variable {env env' : VEnv} {D : VInductDecl'}

/-- **A block's inductive types are always fresh constants.**  `addInduct'` goes through
`addConst`, which fails on a name already in `env`, so a `VIndType` cannot name an
inductive that already exists.  This is the structural reason `VInductDecl'` cannot express
a nested declaration: the "companion type" of `docs/design-inductive.md` §9.3 — a member of
the block whose head is an *already-declared* `J` — makes `addInduct'` return `none`. -/
theorem addInduct'_type_fresh (h : env.addInduct' D = some env') {T : VIndType}
    (hT : T ∈ D.types) : env.constants T.name = none :=
  (addInduct'_eq_some_iff.1 ⟨_, h⟩).1 _ <| by
    rw [VInductDecl'.allConsts_names]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hT))

/-- The same fact as a refutation: no `VInductDecl'` whose block contains an
already-declared name is addable. -/
theorem addInduct'_no_companion {T : VIndType} {ci : VConstant}
    (h : env.addInduct' D = some env') (hT : T ∈ D.types)
    (hJ : env.constants T.name = some ci) : False := by
  rw [addInduct'_type_fresh h hT] at hJ; exact absurd hJ nofun

/-- **The only names a block introduces.**  A constant that is new in `env'` is one of the
block's type names, one of its constructor names, or `mkRecName` of one of its type names.

There is no fourth possibility, so `addInduct'` cannot account for the auxiliary recursors
that `Environment.addInductive` re-adds on the nested path under
`(mkRecName mainName).appendIndexAfter i`. -/
theorem addInduct'_new_name {n : Lean.Name} (h : env.addInduct' D = some env')
    (hnew : env'.constants n ≠ env.constants n) : n ∈ D.allNames :=
  Classical.byContradiction fun hc => hnew (addInduct'_constants_of_not_mem h hc)

end VEnv

/-- …and `allNames` has exactly three kinds of member.  Together with `addInduct'_new_name`
this is the statement that a block introduces no constant under any other name. -/
theorem VInductDecl'.mem_allNames {D : VInductDecl'} {n : Lean.Name} (h : n ∈ D.allNames) :
    n ∈ D.blockNames ∨ n ∈ D.ctorConsts.map (·.1) ∨ ∃ T ∈ D.types, n = Lean.mkRecName T.name := by
  rw [VInductDecl'.allConsts_names] at h
  simp only [List.mem_append] at h
  rcases h with (h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ?_)
    simp only [VInductDecl'.recConsts, List.mem_map] at h
    obtain ⟨_, ⟨⟨T', k⟩, hk, heq⟩, rfl⟩ := h
    cases heq
    exact ⟨T', List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hk), rfl⟩

/-! ## The offset algebra a companion head would need

`tyApp`/`tyApp'`/`ctorApp'` all put the parameter block at a de Bruijn offset as
`bvars k D.np` — a contiguous run of variables — and every offset lemma about them
(`tyApp'_instAll`, `tyApp'_instAll'`, `shift_atRec_tyApp`, `liftN_atRec_tyApp`) is proved by
`map_liftN_bvars_lo/hi` and `map_instAll_bvars_ge/'`, which are lemmas *about `bvars`*.

A companion head is `J.{ls} A(params) ι`, where the parameter block is `A.map (·.liftN k 0)`
for a stored `A : List VExpr` over the parameters, rather than a run of variables.  The
question that decides the estimate is whether that block obeys the same two moves — lifting
past an outer cut, and instantiating a saturated spine away.

It does, and **both are instances of lemmas that already exist**:

* lifting is `VExpr.liftN'_liftN'` (`Theory/VExpr.lean:51`), whose hypotheses at `k₁ = 0` are
  `0 ≤ cut` and `cut ≤ k`;
* instantiation is the lemma below, two rewrites over `VExpr.liftN_liftN` and
  `VExpr.instAll_liftN` (`Theory/Inductive/Telescope.lean:792`).

The side condition in both cases is `cut ≤ k` — *the parameter block sits above the cut* —
and that is already a hypothesis of every existing offset lemma: `hni : ni ≤ K₀` in
`tyApp'_instAll'`, `hij : i + j ≤ k` in `shift_atRec_tyApp`, and the analogue in
`liftN_atRec_tyApp`.  So generalising the head does not invalidate the offset algebra; it
replaces each `bvars` rewrite by its `liftN`-of-a-stored-telescope counterpart under a
hypothesis the caller already supplies. -/
theorem VExpr.instAll_liftN_of_le {A : VExpr} {ιs : List VExpr} {k ni : Nat}
    (hlen : ιs.length = ni) (h : ni ≤ k) :
    VExpr.instAll (A.liftN k) ιs 0 = A.liftN (k - ni) := by
  have hk : k - ni + ni = k := Nat.sub_add_cancel h
  rw [← hk, ← VExpr.liftN_liftN, ← hlen, VExpr.instAll_liftN, Nat.add_sub_cancel]

/-! ## Exit 4: which uniqueness the companion needs, and where it comes from

`Theory/Typing/PatternRules.lean` recovers, from any ι-rule in `env.defeqs`, the block that
declared it — `VEnv.RuleShape`'s `iota` constructor carries `D`, `D.WF env₀` and the full
staging chain as *data*, and `VEnv.WF.ruleShape` (proved) supplies it from
`env.defeqs df`.  So `J`'s constructor list is recoverable without extending `VEnv`.

The risk was that two ι-rules of the same recursor get attributed to *different* blocks.
**Full block uniqueness is not what the companion needs** — it needs the recovered blocks to
agree about `J`'s constructor list, which is strictly weaker.  And the weaker fact does not
need the injectivity/`DeltaUnique` family at all: it follows from `addConst` failing on a
duplicate name.  That is what the theorem below records.

Note the direction of the argument.  A rule headed by `J.rec` comes from a block containing a
type named `J` (`iotaLhs`'s head is `mkRecName (D.types.getD j default).name`, and `mkRecName`
is injective on names).  By the theorem below, at most one block of a well-formed history
contains a type named `J`.  So the attribution is unique, and *a fortiori* the constructor
lists agree.

**One step of that sentence was missing, and it is the only thing this section's estimate got
wrong.**  "The block that declared it" is carried by `RuleShape.iota` as *data*, staged over
environments `env₀ … env₃` with `env₃ ≤ env` — and **nothing relates `env₀` to the history
`ds`**.  So `RuleShape` on its own cannot say that two recovered blocks are two `.induct`
steps of one `VEnv.WF'`, which is precisely what the disjointness theorem quantifies over:
the recovered block could, for all `RuleShape` says, have been declared over an environment
unrelated to `env`'s own history.  Nor is the constants map a way round it — two blocks
sharing a type name agree on `⟨uvars, type⟩` and on nothing else, in particular not on
`ctors`.

`VEnv.WF'.iotaRule_provenance` below supplies the missing step, in the one direction that
needs no edit to `PatternRules.lean`: a rule already known to be an ι-rule is one of the
ι-rules of an `.induct` step *of `ds`*.  With it, `WF'.iota_type_uniq` is the assembled
handle.

**This is deliberately stated here and not as a clause of `VIndType.WF`.**  `RuleShape` lives
downstream of `Theory/Inductive/Decl.lean` (`PatternRules.lean` imports `Inductive/Lemmas.lean`),
so a clause mentioning it would re-create exactly the import cycle that kills the
"thread `VEnv.WF'` into `VIndType.WF`" exit.  The companion's completeness belongs downstream,
where the handle already is. -/

namespace VEnv
variable {env env₁ env₂ env₃ : VEnv} {D D' : VInductDecl'}

/-- **At most one block declares a given type name.**  If `D` is added, and `D'` is added later
over any intervening growth, the two cannot share a type name.

The proof is two steps — the earlier block's type constant is present and monotone, and the
later block's `addInduct'` demands that name be *absent* — so the fact rests on
`addInduct'_type_fresh` above, i.e. on `addConst` failing on a duplicate. **Not** on
injectivity, which is the family the companion story was at risk of depending on. -/
theorem addInduct'_types_disjoint
    (h : env.addInduct' D = some env₁) (hle : env₁ ≤ env₂)
    (h' : env₂.addInduct' D' = some env₃)
    {T T' : VIndType} (hT : T ∈ D.types) (hT' : T' ∈ D'.types) : T.name ≠ T'.name := by
  intro hname
  have h1 : env₂.constants T.name = some ⟨D.uvars, T.type⟩ :=
    hle.constants (addInduct'_types h hT)
  rw [hname, addInduct'_type_fresh h' hT'] at h1
  exact absurd h1 nofun

end VEnv

/-- **The zero-constructor case has no certificate, and it is reachable.**  A block all of
whose types have no constructors contributes *no* ι-rules, so `VEnv.WF.ruleShape` — exit 4's
whole handle — yields nothing about it.

This is not a degenerate corner that cannot arise.  `Empty` and `False` cannot be nested
through (they take no parameters, so `Empty T` is ill-typed), but a *parameterised*
constructor-free inductive can be, and both kernels accept it:

```
inductive Void1 (α : Type) : Type          -- no constructors, one parameter
inductive T1 : Type | mk : Void1 T1 → T1   -- accepted; numNested = 1
```

`Lean4Lean.ElimNestedInductive` reduces `T1` to the block `[T1, _nested.Void1_1]` with
`_nested.Void1_1.ctors = []`, so the companion for `Void1` is a **zero-constructor companion**
and exit 4 is non-uniform exactly there.  A companion with no minor premises is an eliminator
asserting that `J A` is empty, so it needs a certificate rather than a shrug — that obligation
is real and is recorded in `docs/soundness-ledger.md`. -/
theorem VInductDecl'.iotaRules_eq_nil (D : VInductDecl') (h : ∀ T ∈ D.types, T.ctors = []) :
    D.iotaRules = [] := by
  have : D.ctorsAll = [] := by
    simp only [VInductDecl'.ctorsAll, List.flatMap_eq_nil_iff, List.map_eq_nil_iff]
    rintro ⟨T, j⟩ hmem
    exact h T (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hmem))
  simp [VInductDecl'.iotaRules, this]

/-! ## Step 1: the disjointness, wrapped in the induction over `VEnv.WF'`

`addInduct'_types_disjoint` above compares *two* blocks over an explicit intervening `≤`.
What exit 4 needs is the same fact about a whole *history*: any two `.induct` steps of one
`VEnv.WF'` list that share a type name are the same step.  Threading it is the induction
below, and the only new ingredient is the step-level monotonicity `VDecl.WF.le` — the
per-operation `≤` lemmas (`addConst_le`, `addConsts_le`, `addDefEq_le`, `addDefEqs_le`,
`addInduct'_le`) all existed, but nothing put them together at the level of a `VDecl.WF`
step. -/

/-- **Every declaration step grows the environment.**  Seven arms, each an existing `≤`
lemma; `quot` is the only one that has to be staged (`addQuot_stages`). -/
theorem VDecl.WF.le {env env' : VEnv} {d : VDecl} (h : VDecl.WF env d env') : env ≤ env' := by
  cases h with
  | «axiom» _ h | «opaque» _ h => exact VEnv.addConst_le h
  | «def» _ h => exact (VEnv.addConst_le h).trans VEnv.addDefEq_le
  | «example» _ => exact .rfl
  | unsafeDef _ h _ => exact (VEnv.addConsts_le h).trans VEnv.addDefEqs_le
  | quot _ h =>
    obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩ := VEnv.addQuot_stages h
    exact (((VEnv.addConst_le h1).trans (VEnv.addConst_le h2)).trans
      ((VEnv.addConst_le h3).trans (VEnv.addConst_le h4))).trans VEnv.addDefEq_le
  | induct _ h => exact VEnv.addInduct'_le h

namespace VEnv

/-- **Every `.induct` step of a history really ran `addInduct'`**, over some earlier
environment, and its result is below the final one.  One induction, from which both the
freshness facts (`addInduct'_eq_some_iff`) and the presence facts (`addInduct'_types`)
follow for a block named anywhere in the history. -/
theorem WF'.exists_addInduct' {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    ∀ D : VInductDecl', VDecl.induct D ∈ ds →
      ∃ env₀ env₁ : VEnv, env₀.addInduct' D = some env₁ ∧ env₁ ≤ env := by
  induction H with
  | empty => intro _ h; cases h
  | decl hd hds ih =>
    intro D hD
    rcases List.mem_cons.1 hD with rfl | hD
    · cases hd with
      | induct _ h => exact ⟨_, _, h, .rfl⟩
    · obtain ⟨env₀, env₁, h, hle⟩ := ih D hD
      exact ⟨env₀, env₁, h, hle.trans hd.le⟩

/-- **The history discharges `VInductDecl'.Declared`.**  This is `exists_addInduct'` with the
step's own `D.WF` carried along, packaged as the history-free predicate
(`Theory/Inductive/Decl.lean`).  It is the *only* place a declaration history is needed on the
nested path: `VIndRestore.Faithful`, `VNestedOcc.Occurs`, `VInductDecl'.Built` and
`VEnv.AddNested{,B}` all speak of `Declared` instead, so none of them mentions `ds`, and a
`VDecl.WF` rule for a nested step therefore needs no history parameter. -/
theorem WF'.declared {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    ∀ D : VInductDecl', VDecl.induct D ∈ ds → D.Declared env := by
  induction H with
  | empty => intro _ h; cases h
  | decl hd hds ih =>
    intro D hD
    rcases List.mem_cons.1 hD with rfl | hD
    · cases hd with
      | induct _ h => exact ⟨_, _, h, .rfl⟩
    · exact (ih D hD).mono hd.le

/-- The type names of every block of the history are declared, at the types the block
stored for them. -/
theorem WF'.constants_induct_type {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    (D : VInductDecl') (hD : VDecl.induct D ∈ ds) {T : VIndType} (hT : T ∈ D.types) :
    env.constants T.name = some ⟨D.uvars, T.type⟩ := by
  obtain ⟨_, _, h, hle⟩ := H.exists_addInduct' D hD
  exact hle.constants (VEnv.addInduct'_types h hT)

/-- Every block of the history introduces pairwise distinct names: `addInduct'` succeeded,
and `addConstList` rejects a repeat. -/
theorem WF'.induct_allNames_nodup {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    (D : VInductDecl') (hD : VDecl.induct D ∈ ds) : D.allNames.Nodup := by
  obtain ⟨_, _, h, -⟩ := H.exists_addInduct' D hD
  exact (VEnv.addInduct'_eq_some_iff.1 ⟨_, h⟩).2

/-- **`addInduct'_types_disjoint`, over a whole history.**  Two `.induct` steps of one
well-formed declaration list that share a type name are *the same step*.

This is the form exit 4 needs: it says that "the block that declared `J`" is well defined,
so anything read off that block — in particular `J`'s constructor list — is a function of
`J` alone.  The content is still `addInduct'_type_fresh`, i.e. `addConst` failing on a
duplicate; the induction only has to carry the earlier block's constant forward, which is
`VDecl.WF.le`. -/
theorem WF'.induct_eq_of_type_name {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    ∀ D D' : VInductDecl', VDecl.induct D ∈ ds → VDecl.induct D' ∈ ds →
      ∀ T ∈ D.types, ∀ T' ∈ D'.types, T.name = T'.name → D = D' := by
  induction H with
  | empty => intro _ _ h; cases h
  | decl hd hds ih =>
    intro D D' hD hD' T hT T' hT' hname
    rcases List.mem_cons.1 hD with rfl | hDtl
    · rcases List.mem_cons.1 hD' with h' | hD'tl
      · injection h' with h''; exact h''.symm
      · cases hd with
        | induct _ h =>
          have hfresh := VEnv.addInduct'_type_fresh h hT
          have hold := hds.constants_induct_type D' hD'tl hT'
          rw [hname] at hfresh
          rw [hfresh] at hold
          exact absurd hold nofun
    · rcases List.mem_cons.1 hD' with rfl | hD'tl
      · cases hd with
        | induct _ h =>
          have hfresh := VEnv.addInduct'_type_fresh h hT'
          have hold := hds.constants_induct_type D hDtl hT
          rw [← hname] at hfresh
          rw [hfresh] at hold
          exact absurd hold nofun
      · exact ih D D' hDtl hD'tl T hT T' hT' hname

end VEnv

/-! ## Step 2: the left-hand side's head determines `T.name`

Purely syntactic, no environment: `iotaLhs` is a spine with a `.const` head, so
`mkApp_inj_of_arity` reads the head off, and `mkRecName_inj` strips the `.rec`.  At the
level of a whole `iotaRule` the left-hand side is wrapped in `mkLams (D.iotaCtx C)`, and
`mkLams_inj_of_arity` peels that — the body's `lamArity` is `0` because `iotaLhs` always
carries at least the major premise, which is the same observation
`not_isDeltaRule_iotaRule` already makes about `peelLams`. -/

namespace VInductDecl'

/-- `iotaLhs` is an application, never a `lam`. -/
theorem iotaLhs_lamArity (D : VInductDecl') (j : Nat) (C : VIndCtor) :
    (D.iotaLhs j C).lamArity = 0 := by
  rw [VInductDecl'.iotaLhs, VExpr.mkApp_concat]; rfl

/-- **The head of an ι-rule's left-hand side.**  Two `iotaLhs` are equal only if they name
the same recursor at the same universe arity. -/
theorem iotaLhs_head_inj {D D' : VInductDecl'} {j j' : Nat} {C C' : VIndCtor}
    (h : D.iotaLhs j C = D'.iotaLhs j' C') :
    (D.types.getD j default).name = (D'.types.getD j' default).name ∧
      D.recUvars = D'.recUvars := by
  simp only [VInductDecl'.iotaLhs] at h
  have hh := (VExpr.mkApp_inj_of_arity (f := .const _ _) (g := .const _ _) rfl rfl h).1
  injection hh with h1 h2
  refine ⟨mkRecName_inj h1, ?_⟩
  have hlen := congrArg List.length h2
  simpa [VLevel.params] using hlen

/-- The same fact with the block's type read off by index rather than by `getD`. -/
theorem iotaLhs_name_eq {D D' : VInductDecl'} {j j' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T')
    (h : D.iotaLhs j C = D'.iotaLhs j' C') : T.name = T'.name := by
  have h1 := (iotaLhs_head_inj h).1
  rwa [D.getD_types hTj, D'.getD_types hTj'] at h1

/-- **The head of an ι-*rule*.**  `mkLams_inj_of_arity` peels `iotaCtx`, then
`iotaLhs_head_inj`. -/
theorem iotaRule_head_inj {D D' : VInductDecl'} {j q j' q' : Nat} {C C' : VIndCtor}
    (h : D.iotaRule j q C = D'.iotaRule j' q' C') :
    (D.types.getD j default).name = (D'.types.getD j' default).name ∧
      D.recUvars = D'.recUvars := by
  have hl : VExpr.mkLams (D.iotaCtx C) (D.iotaLhs j C)
      = VExpr.mkLams (D'.iotaCtx C') (D'.iotaLhs j' C') := congrArg VDefEq.lhs h
  exact iotaLhs_head_inj
    (VExpr.mkLams_inj_of_arity (D.iotaLhs_lamArity j C) (D'.iotaLhs_lamArity j' C') hl).2

theorem iotaRule_name_eq {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType}
    {C C' : VIndCtor} (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T')
    (h : D.iotaRule j q C = D'.iotaRule j' q' C') : T.name = T'.name := by
  have h1 := (iotaRule_head_inj h).1
  rwa [D.getD_types hTj, D'.getD_types hTj'] at h1

end VInductDecl'

/-! ## The two steps composed: where an ι-rule comes from, and that it is one block

`VEnv.WF.ruleShape` recovers a block from a rule, but the block it hands back is carried as
*data on the `RuleShape.iota` constructor*, staged over environments (`env₀ … env₃`) that
have no stated relation to the history `ds`.  So `RuleShape` alone cannot say that two
recovered blocks are steps of one history, which is what step 1 quantifies over.

`iotaRule_provenance` supplies the missing link, in the one direction available without
touching `PatternRules.lean`: a rule *already known to be an ι-rule* is one of the ι-rules
of an `.induct` step of `ds`.  Composing it with step 1 and step 2 gives
`iotaRule_block_uniq`, exit 4's handle in the form the companion clause needs. -/

namespace VEnv

/-- An ι-rule is never the quotient rule: their keys differ in the first entry, and a
recursor name ends in the segment `"rec"`. -/
theorem iotaRule_ne_quotDefEq (D : VInductDecl') (j q : Nat) (C : VIndCtor) :
    D.iotaRule j q C ≠ quotDefEq := by
  intro hq
  have hk := congrArg VDefEq.key hq
  rw [VEnv.key_quotDefEq, VInductDecl'.key_iotaRule] at hk
  injection hk with h1 _
  simp [Lean.mkRecName] at h1

/-- An ι-rule is never a `def`'s δ-rule: its left-hand side is an application. -/
theorem iotaRule_ne_toDefEq (D : VInductDecl') (j q : Nat) (C : VIndCtor) (ci : VDefVal) :
    D.iotaRule j q C ≠ ci.toDefEq := fun h =>
  VEnv.not_isDeltaRule_iotaRule D j q C ci.name ⟨_, congrArg VDefEq.lhs h⟩

/-- **Where an ι-rule of a well-formed environment comes from.**  It is one of the ι-rules
of an `.induct` step of the declaration history.

Unlike `VEnv.WF.ruleShape` this does *not* recover the block the rule was written with — it
recovers a block of the *history*, which `WF'.induct_eq_of_type_name` can then compare.
The two are related by `mem_iotaRules`: the history's block emits this very rule. -/
theorem WF'.iotaRule_provenance {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env) :
    ∀ (D : VInductDecl') (j q : Nat) (C : VIndCtor), env.defeqs (D.iotaRule j q C) →
      ∃ D₀, VDecl.induct D₀ ∈ ds ∧ D.iotaRule j q C ∈ D₀.iotaRules := by
  induction H with
  | empty => exact fun _ _ _ _ h => h.elim
  | decl hd hds ih =>
    intro D j q C hdf
    cases hd with
    | «axiom» _ h | «opaque» _ h =>
      rw [VEnv.addConst_defeqs h] at hdf
      obtain ⟨D₀, h1, h2⟩ := ih D j q C hdf
      exact ⟨D₀, List.mem_cons_of_mem _ h1, h2⟩
    | «example» _ =>
      obtain ⟨D₀, h1, h2⟩ := ih D j q C hdf
      exact ⟨D₀, List.mem_cons_of_mem _ h1, h2⟩
    | «def» _ h =>
      rcases (hdf : _ ∨ _) with heq | hdf
      · exact absurd heq (VEnv.iotaRule_ne_toDefEq _ _ _ _ _)
      · rw [VEnv.addConst_defeqs h] at hdf
        obtain ⟨D₀, h1, h2⟩ := ih D j q C hdf
        exact ⟨D₀, List.mem_cons_of_mem _ h1, h2⟩
    | unsafeDef _ h _ =>
      rcases VEnv.addDefEqs_defeqs hdf with ⟨ci, -, heq⟩ | hdf
      · exact absurd heq (VEnv.iotaRule_ne_toDefEq _ _ _ _ ci)
      · rw [VEnv.addConsts_defeqs h] at hdf
        obtain ⟨D₀, h1, h2⟩ := ih D j q C hdf
        exact ⟨D₀, List.mem_cons_of_mem _ h1, h2⟩
    | quot _ h =>
      obtain ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩ := VEnv.addQuot_stages h
      rcases (hdf : _ ∨ _) with heq | hdf
      · exact absurd heq (VEnv.iotaRule_ne_quotDefEq _ _ _ _)
      · rw [VEnv.addConst_defeqs h4, VEnv.addConst_defeqs h3, VEnv.addConst_defeqs h2,
          VEnv.addConst_defeqs h1] at hdf
        obtain ⟨D₀, hm1, hm2⟩ := ih D j q C hdf
        exact ⟨D₀, List.mem_cons_of_mem _ hm1, hm2⟩
    | induct _ h =>
      obtain ⟨e1, e2, e3, h1, h2, h3, rfl⟩ := VEnv.addInduct'_stages h
      rcases VEnv.addDefEqList_mem _ hdf with hdf | hdf
      · exact ⟨_, List.Mem.head _, hdf⟩
      · rw [VEnv.addConstList_defeqs h3, VEnv.addConstList_defeqs h2,
          VEnv.addConstList_defeqs h1] at hdf
        obtain ⟨D₀, hm1, hm2⟩ := ih D j q C hdf
        exact ⟨D₀, List.mem_cons_of_mem _ hm1, hm2⟩

/-- **Within one block, a type name determines the type — and its index.**  `addInduct'`
succeeded, so the block's names are `Nodup`; `blockNames` is `types.map (·.name)`. -/
theorem _root_.Lean4Lean.VInductDecl'.types_eq_of_name_eq {D : VInductDecl'} {j j' : Nat}
    {T T' : VIndType} (hnd : D.allNames.Nodup) (h0 : D.types[j]? = some T)
    (h1 : D.types[j']? = some T') (hn : T.name = T'.name) : j = j' ∧ T = T' := by
  rw [VInductDecl'.allConsts_names] at hnd
  have hb : D.blockNames.Nodup := (List.nodup_append.1 (List.nodup_append.1 hnd).1).1
  rw [VInductDecl'.blockNames] at hb
  have hlt : j < (D.types.map (·.name)).length := by
    simp only [List.length_map]; exact (List.getElem?_eq_some_iff.1 h0).1
  have e0 : (D.types.map (·.name))[j]? = (D.types.map (·.name))[j']? := by
    simp only [List.getElem?_map, h0, h1, Option.map_some, hn]
  have hjj : j = j' := (List.getElem?_inj hlt hb).1 e0
  subst hjj
  rw [h0] at h1
  exact ⟨rfl, Option.some.inj h1⟩

/-- **Exit 4's handle, assembled.**  Two ι-rules of a well-formed environment whose
recursors carry the same name are ι-rules of *one and the same type of one and the same
block* of the history — and each is the rule of a constructor drawn from that type's own
`ctors`, which is complete by construction.

That is exactly the completeness a companion clause may quote: `T₀.ctors` is a function of
the recursor's name alone.  Note what the proof uses and what it does not: `addConst`
failing on a duplicate (step 1, twice — once across the history, once inside the block) and
the syntactic head of `iotaLhs` (step 2).  No injectivity family, and no `recType`
inversion.

**Where it yields nothing.**  If `T₀.ctors = []` there are no ι-rules at all
(`iotaRules_eq_nil` below), so no instance of this theorem exists — the zero-constructor
companion is outside its reach by construction, not by omission. -/
theorem WF'.iota_type_uniq {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    (hdf : env.defeqs (D.iotaRule j q C)) (hdf' : env.defeqs (D'.iotaRule j' q' C'))
    (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T') (hname : T.name = T'.name) :
    ∃ (D₀ : VInductDecl') (j₀ : Nat) (T₀ : VIndType),
      VDecl.induct D₀ ∈ ds ∧ D₀.types[j₀]? = some T₀ ∧ T₀.name = T.name ∧
        D.iotaRule j q C ∈ D₀.iotaRules ∧ D'.iotaRule j' q' C' ∈ D₀.iotaRules ∧
        (∃ q₀ C₀, C₀ ∈ T₀.ctors ∧ D.iotaRule j q C = D₀.iotaRule j₀ q₀ C₀) ∧
        (∃ q₁ C₁, C₁ ∈ T₀.ctors ∧ D'.iotaRule j' q' C' = D₀.iotaRule j₀ q₁ C₁) := by
  obtain ⟨D₀, hD₀, hm₀⟩ := H.iotaRule_provenance D j q C hdf
  obtain ⟨D₁, hD₁, hm₁⟩ := H.iotaRule_provenance D' j' q' C' hdf'
  obtain ⟨j₀, q₀, C₀, hq₀, he₀⟩ := VInductDecl'.mem_iotaRules hm₀
  obtain ⟨j₁, q₁, C₁, hq₁, he₁⟩ := VInductDecl'.mem_iotaRules hm₁
  obtain ⟨T₀, hT₀, hC₀⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hq₀)
  obtain ⟨T₁, hT₁, hC₁⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hq₁)
  have hn₀ : T₀.name = T.name := VInductDecl'.iotaRule_name_eq hT₀ hTj he₀.symm
  have hn₁ : T₁.name = T'.name := VInductDecl'.iotaRule_name_eq hT₁ hTj' he₁.symm
  have hDD : D₀ = D₁ := H.induct_eq_of_type_name D₀ D₁ hD₀ hD₁
    T₀ (List.mem_of_getElem? hT₀) T₁ (List.mem_of_getElem? hT₁) (by rw [hn₀, hn₁, hname])
  subst hDD
  obtain ⟨rfl, rfl⟩ := VInductDecl'.types_eq_of_name_eq (H.induct_allNames_nodup D₀ hD₀)
    hT₀ hT₁ (by rw [hn₀, hn₁, hname])
  exact ⟨D₀, j₀, T₀, hD₀, hT₀, hn₀, hm₀, hm₁, ⟨q₀, C₀, hC₀, he₀⟩, ⟨q₁, C₁, hC₁, he₁⟩⟩

/-- The block-level reading of `iota_type_uniq`. -/
theorem WF'.iotaRule_block_uniq {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    (hdf : env.defeqs (D.iotaRule j q C)) (hdf' : env.defeqs (D'.iotaRule j' q' C'))
    (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T') (hname : T.name = T'.name) :
    ∃ D₀, VDecl.induct D₀ ∈ ds ∧
      D.iotaRule j q C ∈ D₀.iotaRules ∧ D'.iotaRule j' q' C' ∈ D₀.iotaRules := by
  obtain ⟨D₀, -, -, hD₀, -, -, hm₀, hm₁, -⟩ := H.iota_type_uniq hdf hdf' hTj hTj' hname
  exact ⟨D₀, hD₀, hm₀, hm₁⟩

/-- The `VEnv.WF` reading, matching `VEnv.WF.ruleShape`'s signature: consumers hold
`env.WF`, not a named history.  Dropping `.induct D₀ ∈ ds` loses nothing — the membership
was only ever the vehicle for the uniqueness, which has already been used. -/
theorem WF.iota_type_uniq {env : VEnv} (H : env.WF)
    {D D' : VInductDecl'} {j q j' q' : Nat} {T T' : VIndType} {C C' : VIndCtor}
    (hdf : env.defeqs (D.iotaRule j q C)) (hdf' : env.defeqs (D'.iotaRule j' q' C'))
    (hTj : D.types[j]? = some T) (hTj' : D'.types[j']? = some T') (hname : T.name = T'.name) :
    ∃ (D₀ : VInductDecl') (j₀ : Nat) (T₀ : VIndType),
      D₀.types[j₀]? = some T₀ ∧ T₀.name = T.name ∧
        D.iotaRule j q C ∈ D₀.iotaRules ∧ D'.iotaRule j' q' C' ∈ D₀.iotaRules ∧
        (∃ q₀ C₀, C₀ ∈ T₀.ctors ∧ D.iotaRule j q C = D₀.iotaRule j₀ q₀ C₀) ∧
        (∃ q₁ C₁, C₁ ∈ T₀.ctors ∧ D'.iotaRule j' q' C' = D₀.iotaRule j₀ q₁ C₁) := by
  obtain ⟨D₀, j₀, T₀, -, h⟩ :=
    WF'.iota_type_uniq H.choose_spec hdf hdf' hTj hTj' hname
  exact ⟨D₀, j₀, T₀, h⟩

end VEnv

/-! ## What remains before a companion clause can be stated

Three things, in the order they bite.

**1. `addInduct'` still refuses a companion member, and that is a theorem of this file.**
`addInduct'_type_fresh` says every `T ∈ D.types` is a *newly declared* constant, so a block
carrying a member whose head is an already-declared `J` returns `none`
(`addInduct'_no_companion`).  Exit 4 does not change that by itself: before any companion
clause is written, `addInduct'` — or the staging around it — has to admit a member that is
*not* re-declared.  That is a `Theory/Inductive/Decl.lean` change, and the two theorems above
are exactly the guard that will fire when it is attempted; they are the reason the change
cannot be made by accident.

**2. The certificate is available for every `J` that has a constructor, and for no other.**
`VEnv.WF.iota_type_uniq` recovers `(D₀, j₀, T₀)` from the *rules*, so its domain is
`env.defeqs (D.iotaRule …)`.  A `J` with `T.ctors = []` contributes no rule at all
(`iotaRules_eq_nil`), and a parameterised constructor-free inductive *can* be nested through
— see `iotaRules_eq_nil`'s docstring for the `Void1`/`T1` witness, which both kernels accept.
So the companion clause is non-uniform exactly there, and the certificate for that case has
to come from the recursor's *stored type* carrying no minor premises, i.e. from the `recType`
telescope inversion exit 3 needs.  That is shared work, not additional work; nothing here
substitutes for it.

**3. `binders_indep` must be preserved under the companion's substitution.**  A companion's
constructors are the declared block's constructors with the companion's parameters
substituted in, and that turns several fields recursive at once — for the motivating example
*both* fields of the companion constructor become recursive.  Nothing in this file touches
`VIndRecArg.BindersIndep`; what exists is the satisfiability check, `wDecl_WF`
(`Theory/Inductive/DeclExamples.lean`), a `VInductDecl'.WF` witness built at exactly that
configuration, plus `wRecBad` there showing the clause is not vacuous.  `Decl.lean`'s one
open `sorry`, `VIndRecArg.exists_indep`, is blocked on `forallE_inv` and is untouched by this
section.

**Where the clause goes.**  Not in `Decl.lean`: `VEnv.RuleShape` and `WF.iota_type_uniq` both
live downstream of it (`PatternRules.lean` imports `Inductive/Lemmas.lean`, and this file
imports `Typing/DeltaUnique.lean`), so a `VIndType.WF` clause quoting either would recreate
the import cycle that killed the "thread `VEnv.WF'` into `VIndType.WF`" exit.  The
completeness obligation belongs in a file that already imports both. -/

/-! ## Non-vacuity of everything above

Every theorem of this section is quantified over a `VEnv.WF' ds env` whose `ds` contains a
`VDecl.induct`, and `iotaRule_block_uniq` additionally over an ι-rule in `env.defeqs`.  A
statement of that shape is worthless if no such history exists, so here is one, built from
`fooDecl_WF` (`Theory/Inductive/DeclExamples.lean`) — a real `VInductDecl'.WF` witness, not a
hypothesis — and `fooEnv_eq`, which is `rfl`.

`induct_eq_of_type_name`'s *cross-step* branches are refutations, exactly like
`addInduct'_no_companion` above: their hypotheses are jointly unsatisfiable by design and
that is their content.  What has to be realisable is the ambient `VEnv.WF'` history, and the
`.head` branch, where the conclusion `D = D'` is actually produced; both are witnessed
below. -/

namespace InductiveDeclExamples

/-- A one-step declaration history containing an `.induct`. -/
theorem fooHistory : VEnv.WF' [VDecl.induct fooDecl] fooEnv :=
  .decl (.induct fooDecl_WF fooEnv_eq.choose_spec) .empty

theorem fooIota_mem :
    fooDecl.iotaRule 0 0 ((fooDecl.types[0]!).ctors[0]!) ∈ fooDecl.iotaRules :=
  List.Mem.head _

/-- …and the block really contributes an ι-rule to the environment, so `iotaRule_provenance`
and `iotaRule_block_uniq` have a non-empty domain. -/
theorem fooIota_defeq :
    fooEnv.defeqs (fooDecl.iotaRule 0 0 ((fooDecl.types[0]!).ctors[0]!)) :=
  VEnv.addInduct'_defeqs fooEnv_eq.choose_spec _ fooIota_mem

example : fooDecl.allNames.Nodup :=
  fooHistory.induct_allNames_nodup fooDecl (List.Mem.head _)

example {T : VIndType} (hT : T ∈ fooDecl.types) :
    fooEnv.constants T.name = some ⟨fooDecl.uvars, T.type⟩ :=
  fooHistory.constants_induct_type fooDecl (List.Mem.head _) hT

/-- `iotaRule_block_uniq` at a real history and a real rule. -/
example : ∃ D₀, VDecl.induct D₀ ∈ [VDecl.induct fooDecl] ∧
    fooDecl.iotaRule 0 0 ((fooDecl.types[0]!).ctors[0]!) ∈ D₀.iotaRules ∧
    fooDecl.iotaRule 0 0 ((fooDecl.types[0]!).ctors[0]!) ∈ D₀.iotaRules :=
  fooHistory.iotaRule_block_uniq fooIota_defeq fooIota_defeq (T := fooDecl.types[0]!)
    (T' := fooDecl.types[0]!) rfl rfl rfl

/-- …and the `VEnv.WF` reading, which is the form consumers hold. -/
example : ∃ (D₀ : VInductDecl') (j₀ : Nat) (T₀ : VIndType),
    D₀.types[j₀]? = some T₀ ∧ T₀.name = (fooDecl.types[0]!).name ∧
      fooDecl.iotaRule 0 0 ((fooDecl.types[0]!).ctors[0]!) ∈ D₀.iotaRules ∧
      fooDecl.iotaRule 0 0 ((fooDecl.types[0]!).ctors[0]!) ∈ D₀.iotaRules ∧
      (∃ q₀ C₀, C₀ ∈ T₀.ctors ∧
        fooDecl.iotaRule 0 0 ((fooDecl.types[0]!).ctors[0]!) = D₀.iotaRule j₀ q₀ C₀) ∧
      (∃ q₁ C₁, C₁ ∈ T₀.ctors ∧
        fooDecl.iotaRule 0 0 ((fooDecl.types[0]!).ctors[0]!) = D₀.iotaRule j₀ q₁ C₁) :=
  VEnv.WF.iota_type_uniq ⟨_, fooHistory⟩ fooIota_defeq fooIota_defeq
    (T := fooDecl.types[0]!) (T' := fooDecl.types[0]!) rfl rfl rfl

/-- The `.head` branch of `induct_eq_of_type_name` is reached, and its conclusion is the
non-trivial one: the *same* block on both sides. -/
example {T T' : VIndType} (hT : T ∈ fooDecl.types) (hT' : T' ∈ fooDecl.types)
    (hn : T.name = T'.name) : fooDecl = fooDecl :=
  fooHistory.induct_eq_of_type_name fooDecl fooDecl
    (List.Mem.head _) (List.Mem.head _) T hT T' hT' hn

end InductiveDeclExamples

end Lean4Lean
