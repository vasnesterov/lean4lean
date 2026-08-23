import Lean4Lean.Theory.Inductive.Lemmas

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

end Lean4Lean
