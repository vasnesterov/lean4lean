import Lean4Lean.Verify.Inductive.NestedOccData

/-!
# `TrIndDeclN.ctorName_own`: the producer side, the consumer audit, and `RestoreData.ctor`

`Verify/Environment/InductR.lean`'s `TrIndDeclN` gained one clause,

```
ctorName_own : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
  ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C → c.name = C.name
```

— *the checker's and `D`'s constructor names agree pointwise on the user's members*.  It is the
fact `docs/vacuity-ledger.md` rows 80a/91c name as the only thing between `RestoreData.ctor`'s
prefix half and a proof, and §3 below is that proof.

This file is the **audit** that must accompany such a change, because adding a conjunct to a
relation that appears as a *hypothesis* in already-proved theorems weakens those theorems and
**no instrument in this repo would notice**: the census reads proof terms, the cone walker
follows `deps`, `#print axioms` reports what a proof uses, and none of them asks whether a
hypothesis is still inhabited (`docs/vacuity-ledger.md` §0, blindness 4).  So:

* **§1 — the producer side, for every path.**  `TrIndDecl.toN` (the `numNested = 0` bridge) and
  the two nested witnesses.  `trIndDeclN_eq` is the new closed instance at `numNested = 0`.
* **§2 — the consumer audit.**  Every consumer of `TrIndDeclN`, with a named instance that
  satisfies its `TrIndDeclN` hypothesis, and — separately — the status of the *rest* of its
  hypothesis set.
* **§3 — `RestoreData.ctor`'s prefix half**, and why the new clause *breaks* rows 80a/91c's
  circle rather than relocating it.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. The producer side

Three paths produce a `TrIndDeclN` in this tree, and the clause is discharged on all three.

| path | where | how `ctorName_own` is met |
| --- | --- | --- |
| `numNested = 0` | `TrIndDecl.toN` (`Verify/Environment/InductR.lean`) | from `TrIndDecl.trCtors`, whose `TrIndCtor` carries `c.name = C.name` — **at the cost of one new premise**, see below |
| nested, hand restoration | `NestedWit.trIndDeclN_wit` (same file) | `rfl` at the block's single user constructor |
| nested, `mkRestore` restoration | `NestedWit.trIndDeclN_wit'` (`Verify/Inductive/NestedRestoreWit.lean`) | `rfl`, likewise |

**The one qualification, stated rather than hidden.**  `TrIndDecl` states its constructor
clause *staged*, over `env.addIndTypes D = some env₁`, because `TrExprS` of a constructor type
needs the block's type constants declared.  A name equation needs no environment, so
`ctorName_own` is **unstaged** — the alternative would push the staging premise onto every
consumer, including `RestoreData.ctor`'s.  The price is that `TrIndDecl.toN` cannot reach the
clause from `TrIndDecl` alone and now takes `∃ et, env.addIndTypes D = some et` as an explicit
premise.  That premise is **available at `toN`'s only call site**:
`Verify/Inductive/AddInductiveStep.lean`'s `addInductiveStepWF_of_run` already passes the same
term (`hadd.addIndTypes`) as `InductStepNested`'s second conjunct.  So no obligation is created;
one is shared.

### The closed `numNested = 0` instance

`TrIndDecl` has exactly one satisfiability witness, `trIndDecl_eq` at `Eq` — the first block of
`stdPrelude`, against the `eqIndDecl` that `VEnv.LeanWF` is stated over.  Pushing it through the
bridge needs `Canonical` and the `addIndTypes` success; both are proved here, so the
`numNested = 0` branch of `TrIndDeclN` has a **closed** instance carrying the new clause. -/

/-- `Eq`'s block is canonical: `Eq.refl` has no fields at all (both of its binders are
parameters), so `VIndCtor.Canonical`'s quantifier is empty. -/
theorem eqIndDecl_Canonical : eqIndDecl.Canonical := by
  intro j C hC
  simp only [show eqIndDecl.ctorsAll
      = [(0, (eqIndDecl.types.getD 0 default).ctors.getD 0 default)] from rfl,
    List.mem_cons, List.not_mem_nil, or_false] at hC
  cases hC
  intro i F r hF hr
  rcases i with _ | i
  · simp only [eqIndDecl] at hF; cases hF
  · simp [eqIndDecl] at hF

/-- …and its single type constant is fresh at `VEnv.empty`, so the staging premise `TrIndDecl.toN`
now takes is met. -/
theorem eqIndDecl_addIndTypes : ∃ et, VEnv.empty.addIndTypes eqIndDecl = some et := by
  refine VEnv.addConstList_eq_some_iff.2 ⟨?_, ?_⟩
  · intro n hn; simp [VInductDecl'.typeConsts, eqIndDecl] at hn; subst hn; rfl
  · decide

/-- **`TrIndDeclN` with the new clause is satisfiable at `numNested = 0`, at a closed
environment.**  This is the witness the audit of §2 instantiates every non-nested consumer at. -/
theorem trIndDeclN_eq :
    TrIndDeclN VEnv.empty [`u_1] 2 [eqIndTypeE] false 0 eqIndDecl [] eqIndDecl.idRestore :=
  trIndDecl_eq.toN eqIndDecl_addIndTypes

/-- The clause is *not* vacuous at that instance: it has a member with a constructor, so both
antecedents fire.  (Row 65a's discipline: instantiate at the degenerate instance and check the
hypotheses are satisfiable.  Here the *quantifier body* is what is checked non-empty.) -/
theorem trIndDeclN_eq_ctorName_own_fires :
    ∃ (j : Nat) (q : Nat) (t : InductiveType) (T : VIndType) (c : Constructor) (C : VIndCtor),
      ([eqIndTypeE] : List InductiveType)[j]? = some t ∧
      eqIndDecl.types[j]? = some T ∧ t.ctors[q]? = some c ∧ T.ctors[q]? = some C ∧
      c.name = C.name :=
  ⟨0, 0, eqIndTypeE, _, _, _, rfl, rfl, rfl, rfl,
    trIndDeclN_eq.ctorName_own 0 _ _ rfl rfl 0 _ _ rfl rfl⟩

/-! ## 2. The consumer audit

Six consumers take a `TrIndDeclN` as a hypothesis, directly or through `InductStepNested`.  For
each: **which instance satisfies the `TrIndDeclN` hypothesis after the addition** (that is the
question the brief asks, and a witness rather than a count is what answers it), and separately
the status of the remaining hypotheses.

| # | consumer | `TrIndDeclN` witness | rest of the hypothesis set |
| --- | --- | --- | --- |
| C1 | `TrIndDeclN.mem_indDeclNamesN` | `trIndDeclN_eq`; `NestedWit.trIndDeclN_wit` | jointly satisfied — `memIndDeclNamesN_sat` below |
| C2 | `TrIndDeclN.not_addInductStagesR` | same | jointly satisfied — `notAddInductStagesR_sat` below |
| C3 | `NestedWit.tBlock_not_refuted_at_trec1` | **none, before or after** — see below | n/a |
| C4 | `Result.name_prefix_of_run` | `trIndDeclN_eq`, `trIndDeclN_wit` | the `run`-success equation is `#eval`-witnessed only — see below |
| C5 | `InductStepNested` and its eight lemmas | `inductStepNested_wit` / `_wit_closed` re-elaborate | jointly satisfied by those two |
| C6 | `Result.ctor_prefix_of_run` (§3, new) | as C4 | as C4 |

**C3 is the one honest gap, and it predates this change.**
`NestedWit.tBlock_not_refuted_at_trec1` takes `TrIndDeclN env Us np [tIndType] false 1 D K R`
for the `T`-nesting-`Box` block, and **no `VInductDecl'` for that block exists in the tree** —
`NestedBuild.lean` builds one for `NFn`/`PFn` only.  So its `TrIndDeclN` hypothesis was
uninhabited-as-far-as-the-tree-knows *before* this change as well, and the addition is not what
put it there.  Two things make that acceptable rather than a defect: the theorem's conclusion is
`¬ ((`T.rec_1 : Name) ∉ indDeclNamesN [tIndType] 1)`, whose proof term is
`fun hn => hn trec1_mem_indDeclNamesN` — it uses **none** of its hypotheses, so no strength can
be lost by strengthening one; and `trIndDeclN_ne_load_bearing_tBlock` below states that
independence as a theorem rather than as a reading of the proof.

**C4/C6 carry a pre-existing hypothesis with no in-tree proof**, and it is *not* the
`TrIndDeclN` one: `ElimNestedInductive.run fuel np types cenv s = .ok (r, s')`.  The tree's only
evidence that a concrete `run` succeeds is the fidelity `#eval` of
`Verify/Inductive/NestedRestoreWit.lean` §1.1, which checks that `run`'s output matches
`nfnResult` at build time; there is no theorem `run … = .ok (nfnResult, _)`.  That is a real gap
in the *joint* satisfiability of C4's hypotheses — inherited unchanged by C6 — and it is
reported here rather than papered over.  It is orthogonal to `ctorName_own`. -/

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

section
variable {env : VEnv}
  (hPFn : env.constants ``PFn = some ⟨0, pfnType.type⟩)
  (hPFnMk : env.constants ``PFn.mk = some ⟨0, pfnMk.type pfnDecl 0⟩)
  (hfresh : ∀ n ∈ [``NFn, ``NFn.node, ``NFn.rec, ``NFn.rec_1], env.constants n = none)

/-- The first stage of `AddInductStagesR` at the nested witness, on its own: only `NFn`'s type
constant is declared, `_nested.PFn_1`'s having been filtered out by `typeConstsC`. -/
theorem nfnAux_addIndTypesC (hfresh : ∀ n ∈ [``NFn, ``NFn.node, ``NFn.rec, ``NFn.rec_1],
    env.constants n = none) : ∃ e₁, env.addIndTypesC nfnAux nfnK = some e₁ := by
  refine VEnv.addConstList_eq_some_iff.2 ⟨?_, ?_⟩
  · intro n hn
    simp only [show (nfnAux.typeConstsC nfnK).map (·.1) = [``NFn] from rfl,
      List.mem_singleton] at hn
    subst hn; exact hfresh _ (by simp)
  · decide

include hPFn hPFnMk hfresh in
/-- **C1's hypothesis set is jointly satisfiable**: the translation, the staging premise, and a
name actually in `allNamesCR`.  So `mem_indDeclNamesN` still has content at the nested block. -/
theorem memIndDeclNamesN_sat : ∃ env₁,
    TrIndDeclN env [] 0 [nfnIndType] false 1 nfnAux nfnK nfnRestore ∧
    env.addIndTypesC nfnAux nfnK = some env₁ ∧
    (``NFn : Name) ∈ nfnAux.allNamesCR nfnRestore nfnK ∧
    (``NFn : Name) ∈ indDeclNamesN [nfnIndType] 1 := by
  obtain ⟨e₁, he₁⟩ := nfnAux_addIndTypesC hfresh
  exact ⟨e₁, trIndDeclN_wit hPFn hPFnMk, he₁, by decide,
    trIndDeclN_wit (env := env) hPFn hPFnMk |>.mem_indDeclNamesN he₁ (by decide)⟩

include hPFn hPFnMk in
/-- **C2's hypothesis set is jointly satisfiable**, so `not_addInductStagesR` still refutes
something: a name outside `indDeclNamesN [nfnIndType] 1` that the output map holds and the input
map does not. -/
theorem notAddInductStagesR_sat {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ (m₂ : ConstMap) (env₂ : VEnv),
      TrIndDeclN env [] 0 [nfnIndType] false 1 nfnAux nfnK nfnRestore ∧ m.WF ∧
      m.find? `Foo = none ∧ m₂.find? `Foo ≠ none ∧
      (`Foo : Name) ∉ indDeclNamesN [nfnIndType] 1 ∧
      ¬ AddInductStagesR m env nfnAux nfnK nfnRestore m₂ env₂ := by
  have ci : ConstantInfo :=
    .axiomInfo { toConstantVal := { name := `Foo, levelParams := [], type := .sort .zero },
                 isUnsafe := false }
  refine ⟨m.insert `Foo ci, env, trIndDeclN_wit hPFn hPFnMk, hwf, hfr _, ?_, by decide, ?_⟩
  · rw [hwf.find?_insert]; simp
  · refine (trIndDeclN_wit hPFn hPFnMk).not_addInductStagesR hwf (n := `Foo) (hfr _) ?_
      (by decide)
    rw [hwf.find?_insert]; simp

end

/-- **C3's hypotheses are not load-bearing.**  `tBlock_not_refuted_at_trec1`'s conclusion holds
outright, with no `TrIndDeclN`, no `ConstMap.WF` and no `find?` premises.  So strengthening
`TrIndDeclN` cannot weaken it, whatever the inhabitation status of its hypothesis. -/
theorem trIndDeclN_ne_load_bearing_tBlock :
    ¬ ((`T.rec_1 : Name) ∉ indDeclNamesN [tIndType] 1) :=
  fun hn => hn trec1_mem_indDeclNamesN

end NestedWit

/-! ## 3. `RestoreData.ctor`, prefix half — and how the circle breaks

`RestoreData.ctor` (`Verify/Inductive/NestedRestore.lean`) is

```
ctor : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ t, r.types[j]? = some t →
  ∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name
```

and rows 80a/91c record why its prefix half was out of reach:

1. it needs `∃ c ∈ t.ctors, c.name = C.name` for `t` a member of the checker's output;
2. `TrIndDeclN.trCtors` supplies only `c.name = R.ctorName C.name`;
3. so one needs `R.ctorName C.name = C.name`, i.e. `VIndRestore.OwnId.ctorName`;
4. and `Result.mkRestore_ownId`'s `ctorName` clause is proved **from `RestoreData.ctor`**.

**How `ctorName_own` breaks it rather than relocating it.**  The derivation below never mentions
`R`.  It goes

* `run_prefix` (`Verify/Inductive/NestedRunInvariant.lean`): on the prefix, the output member's
  constructor *names*, in order, are the input member's — a fact about `State.newTypes`' name
  skeleton, with no `VEnv`, no `VIndRestore` and no translation in it;
* `TrIndDeclN.trCtorsLen`: the input member and `D`'s member have the same number of
  constructors, so the index `q` that locates `C` also locates an input constructor;
* `TrIndDeclN.ctorName_own`: that input constructor's name **is** `C.name`.

Since `R` does not occur, nothing here can be an input to `mkRestore_ownId`'s proof, so link 4
of the circle is not re-entered — as opposed to a derivation via `OwnId.ctorName`, which would
merely move the cycle one edge along.  The escape route rows 80a/91c examined and rejected
(`¬ IsNestedName C.name` ⇒ the `ctorRenames` lookup misses) is *also* not used, so the new clause
does not smuggle in a name-discipline fact: it is a statement about the relation between the two
descriptions of the same block, which is what a translation relation is for.

**What is still open, measured against `ctor`'s actual consumers.**  The **tail half** —
`j ≥ types.length`, i.e. `D`'s companion members — does not follow and cannot:
`TrIndDeclN.trType`/`trCtors`/`ctorName_own` are all quantified over `types[j]? = some t`, which
is `none` past the cut, and `RunSkelExtends` pins only the prefix by design.  That is
`RestoreData.auxName`/`auxCtorName` territory and needs `mkUniqueName`'s output.

`RestoreData.ctor` has **three** consumers in `Verify/Inductive/NestedRestore.lean`, and the
prefix half covers exactly one of them:

| consumer | index range it uses | covered? |
| --- | --- | --- |
| `mkRestore_ownId`'s `ctorName` | via `RestoreData.off`, so `j < types.length` | **yes** |
| `mkRestore_nameBarrier`'s `auxCtor` | via `RestoreData.on`, so `types.length ≤ j` | no |
| `mkRestore_nameBarrier`'s `resCtor` | via `RestoreData.get`, arbitrary `j`; the branch that uses it lands at `types.length ≤ j` | no |

So `RestoreData.ctor` as a whole is **not** closed, and the honest statement of what this buys is
narrower than "`ctor` is unblocked": it is *the one link the circle of rows 80a/91c ran through*
that is now cut, on the same footing as `Result.name_prefix_of_run`.  The other two consumers need
the tail, which is a different obligation with a different supplier. -/

namespace ElimNestedInductive.Result

variable {fuel np : Nat} {types : List Lean.InductiveType} {s : ElimNestedInductive.State}
  {r : Result} {s' : ElimNestedInductive.State} {cenv : Environment}

/-- **`RestoreData.ctor` at `run`'s monadic output, on the prefix.**  The half rows 80a/91c
declined for a circle, now closed by `TrIndDeclN.ctorName_own` — with no `VIndRestore` anywhere
in the statement or the proof. -/
theorem ctor_prefix_of_run {venv : VEnv} {Us : List Lean.Name} {npar nn : Nat} {iu : Bool}
    {D : VInductDecl'} {K : List Lean.Name} {R : VIndRestore}
    (htr : TrIndDeclN venv Us npar types iu nn D K R)
    (hs : s.newTypes.toList = types)
    (h : ElimNestedInductive.run fuel np types cenv s = .ok (r, s')) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ t, r.types[j]? = some t →
      j < types.length → ∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name := by
  intro j T hT t hjt hj C hC
  obtain ⟨u, hu, -, hcs⟩ := ElimNestedInductive.run_prefix hs h j t hjt hj
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hC
  have hqlt : q < u.ctors.length := by
    rw [htr.trCtorsLen j u T hu hT]; exact List.getElem?_eq_some_iff.1 hq |>.1
  obtain ⟨c₀, hc₀⟩ := exists_getElem?_of_lt hqlt
  have hname : c₀.name = C.name := htr.ctorName_own j u T hu hT q c₀ C hc₀ hq
  have hmem : c₀.name ∈ t.ctors.map (·.name) := by
    rw [hcs]; exact List.mem_map.2 ⟨c₀, List.mem_iff_getElem?.2 ⟨q, hc₀⟩, rfl⟩
  obtain ⟨c, hc, he⟩ := List.mem_map.1 hmem
  exact ⟨c, hc, he.trans hname⟩

/-- The two prefix halves together, in the shape `RestoreData`'s two fields want them.  Note
what is *not* here: the tail halves, and `ctor`'s tail half in particular is unreachable from
this hypothesis set for the structural reason §3 records. -/
theorem name_and_ctor_prefix_of_run {venv : VEnv} {Us : List Lean.Name} {npar nn : Nat}
    {iu : Bool} {D : VInductDecl'} {K : List Lean.Name} {R : VIndRestore}
    (htr : TrIndDeclN venv Us npar types iu nn D K R)
    (hs : s.newTypes.toList = types)
    (h : ElimNestedInductive.run fuel np types cenv s = .ok (r, s')) :
    (∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ t, r.types[j]? = some t →
      j < types.length → t.name = T.name) ∧
    (∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ t, r.types[j]? = some t →
      j < types.length → ∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name) :=
  ⟨name_prefix_of_run htr hs h, ctor_prefix_of_run htr hs h⟩

end ElimNestedInductive.Result

end Lean4Lean
