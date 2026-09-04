import Lean4Lean.Verify.Inductive.ProjNoNested
import Lean4Lean.Verify.Inductive.NestedRestore
import Lean4Lean.Verify.Inductive.RunIdentity
import Lean4Lean.Verify.Inductive.NestedOccData
import Lean4Lean.Verify.Inductive.OccArgsTyping

/-!
# The zero-`_nested`-constants measurement, as machine-checked statements

**The measurement.**  After elaborating a genuinely nested inductive in this toolchain —
`inductive Tree where | node : List Tree → Tree` — an environment scan finds **zero**
`_nested`-prefixed constants.  The auxiliary block a nested declaration is compiled through
lives only inside `Environment.addInductive`; the restoration renames the auxiliary family
away before anything is stored.  That is what `VIndRestore`, `csubst`/`csubstTy` and the
`Restrict*` files model, so the restoration layer is an account of the kernel rather than a
spec artefact.

**What a measurement is not.**  It is a fact about *this* elaborator's output at *one*
declaration; the spec quantifies over environments.  So this file does the conditional
version:

* §1 the condition on the incoming block — `NoNestedDeclNames`, which is exactly
  `checkNoNestedAuxName`'s success (`Lean4Lean/Inductive/Add.lean`:1086, called at :1104 and
  :1109) — with the equivalence proved, in both directions.
* §2 the condition on the environment — `VEnv.NoNestedN`
  (`Verify/Inductive/ProjNoNested.lean`:367, reused, not restated) — and the names a
  *restored* step declares, shown clean from §1.
* §3 the discharges: what becomes a theorem once §1/§2 hold, and at which existing hypothesis.
* §4 the instantiation at `ntreeAux` — the parameterised nested block, `uvars = 1`,
  `params = [.sort (.succ (.param 0))]` — including a **succeeding** step from the empty
  environment, so that nothing here is conditional on an unsatisfiable hypothesis.
* §5 the verdict: assumable, or must be established, and exactly where.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## §1 The condition on the incoming block, and the check that establishes it -/

/-- **The gate condition.**  No member of the block being declared, and no constructor of one,
carries the kernel's reserved `_nested` prefix.

This is deliberately a condition on the *Lean-level* declaration, because that is what
`Environment.addInductive` sees and what `checkNoNestedAuxName` tests.  The abstract side's
condition is `VEnv.NoNestedN` (§2), and §2 is how the two meet. -/
def NoNestedDeclNames (types : List InductiveType) : Prop :=
  ∀ t ∈ types, ¬ IsNestedName t.name ∧ ∀ c ∈ t.ctors, ¬ IsNestedName c.name

/-- **`checkNoNestedAuxName` decides exactly `¬ IsNestedName`.**  Both directions: the check's
success is neither weaker nor stronger than the condition, so §1's hypothesis is *precisely*
what the landed check buys and not an idealisation of it. -/
theorem checkNoNestedAuxName_ok_iff {n : Name} :
    checkNoNestedAuxName n = .ok () ↔ ¬ IsNestedName n := by
  rw [checkNoNestedAuxName, IsNestedName]
  split
  · simp_all
  · simp_all
    rfl

/-! ### §1.1 The check fires on every member: the guard loop, extracted

`checkNoNestedAuxName_ok_iff` says the check *decides* the condition; it does not say the gate
runs it on every name.  This does, by the pattern of `guardLoop_blockClosed`
(`Verify/Inductive/RunIdentity.lean` §6.1): the loop is transcribed verbatim from
`Environment.addInductive` and every other check is given the trivial postcondition, so what
comes out is exactly `checkNoNestedAuxName`'s contribution and nothing else. -/

/-- `checkNoNestedAuxName` as an `Except.WF` fact, for the loop. -/
theorem checkNoNestedAuxName.WF (n : Name) :
    (checkNoNestedAuxName n).WF fun _ => ¬ IsNestedName n := by
  rintro ⟨⟩ h; exact checkNoNestedAuxName_ok_iff.1 h

theorem guardLoop_ctors_noNested (env : Environment) (names lps : List Name) (np : Nat) :
    ∀ (cs : List Constructor),
    (forIn cs PUnit.unit (fun ctor _ => do
        env.checkNoMVarNoFVar ctor.name ctor.type
        checkNoNestedAux ctor.name ctor.type
        checkNoNestedAuxName ctor.name
        checkNoLooseBVars ctor.name ctor.type
        checkUniformIndOccs names lps np ctor.name ctor.type
        pure (ForInStep.yield PUnit.unit)) : Except Exception PUnit).WF
      (fun _ => ∀ c ∈ cs, ¬ IsNestedName c.name)
  | [] => Except.WF.pure (fun _ h => absurd h nofun)
  | c :: cs => by
    rw [List.forIn_cons]
    refine Except.WF.bind (Q := fun r =>
      r = ForInStep.yield PUnit.unit ∧ ¬ IsNestedName c.name) ?_ ?_
    · refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (checkNoNestedAuxName.WF c.name) fun _ hn => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      exact Except.WF.pure ⟨rfl, hn⟩
    · rintro r ⟨rfl, hn⟩
      refine (guardLoop_ctors_noNested env names lps np cs).mono fun _ h x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hn
      · exact h x hx

theorem guardLoop_noNested (env : Environment) (names lps : List Name) (np : Nat) :
    ∀ (types : List InductiveType),
    (forIn types PUnit.unit (fun indType _ => do
        env.checkNoMVarNoFVar indType.name indType.type
        checkNoNestedAux indType.name indType.type
        checkNoNestedAuxName indType.name
        checkNoLooseBVars indType.name indType.type
        for ctor in indType.ctors do
          env.checkNoMVarNoFVar ctor.name ctor.type
          checkNoNestedAux ctor.name ctor.type
          checkNoNestedAuxName ctor.name
          checkNoLooseBVars ctor.name ctor.type
          checkUniformIndOccs names lps np ctor.name ctor.type
        pure (ForInStep.yield PUnit.unit)) : Except Exception PUnit).WF
      (fun _ => NoNestedDeclNames types)
  | [] => Except.WF.pure (fun _ h => absurd h nofun)
  | t :: l => by
    rw [List.forIn_cons]
    refine Except.WF.bind (Q := fun r =>
      r = ForInStep.yield PUnit.unit ∧ ¬ IsNestedName t.name ∧
        ∀ c ∈ t.ctors, ¬ IsNestedName c.name) ?_ ?_
    · refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (checkNoNestedAuxName.WF t.name) fun _ hn => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (guardLoop_ctors_noNested env names lps np t.ctors) fun _ hc => ?_
      exact Except.WF.pure ⟨rfl, hn, hc⟩
    · rintro r ⟨rfl, hn, hc⟩
      refine (guardLoop_noNested env names lps np l).mono fun _ h x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hn, hc⟩
      · exact h x hx

/-- **The condition is what acceptance buys.**  `Environment.addInductive` accepting a block
implies `NoNestedDeclNames` of it — so §1's hypothesis is *established* for every block that
gets past the gate, by the two lines at `Lean4Lean/Inductive/Add.lean`:1104 and :1109 and
nothing else. -/
theorem addInductive_WF_noNestedDeclNames {env : Environment} {lparams : List Name} {np : Nat}
    {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig} :
    (Environment.addInductive env lparams np types iu ap fuel).WF
      fun _ => NoNestedDeclNames types := by
  unfold Environment.addInductive
  exact Except.WF.bind (guardLoop_noNested env _ lparams np types) fun _ hg _ _ => hg

/-! ## §2 The environment-level condition, and what a *restored* step declares

The abstract condition is `VEnv.NoNestedN` — "no declared name carries the prefix"
(`Verify/Inductive/ProjNoNested.lean`:367, reused verbatim; `noNestedC_of_noNestedN` there
already derives the `NoNestedC` half).  §2 connects it to §1: the names a restored inductive
step declares are `D.allNamesCR R K`, and `TrIndDeclN.mem_indDeclNamesN`
(`Verify/Environment/InductR.lean`:329) bounds those by `indDeclNamesN types numNested` — the
Lean-level block's own names plus the renamed auxiliary recursors `I.rec_k`.  So §1's condition
on the *input* is exactly what makes the *output* clean. -/

/-- The renamed auxiliary recursor name is outside the barrier.  `mkRecName n` never has macro
scopes (`hasMacroScopes` tests the last component against `"_hyg"`), so `modifyBase` is just the
function, and the appended component starts with `"rec"`. -/
theorem not_isNestedName_appendIndexAfter'_mkRecName {n : Name} (h : ¬ IsNestedName n) (i : Nat) :
    ¬ IsNestedName (appendIndexAfter' (Lean.mkRecName n) i) := by
  rw [appendIndexAfter', Lean.mkRecName, Name.modifyBase,
    show (Name.str n "rec").hasMacroScopes = false from rfl]
  refine fun hx => (IsNestedName.str_iff.1 hx).elim (fun hx => ?_) h
  rw [show (`_nested : Name) = .str .anonymous "_nested" from rfl, Name.str.injEq] at hx
  have h2 := congrArg String.toList hx.2
  simp [String.toList_append] at h2

/-- Every name the *renamed* auxiliary recursors use is clean, from §1's condition alone. -/
theorem NoNestedDeclNames.auxRecName {types : List InductiveType} (h : NoNestedDeclNames types)
    (k : Nat) : ¬ IsNestedName (Lean4Lean.auxRecName types k) := by
  rw [Lean4Lean.auxRecName]
  refine not_isNestedName_appendIndexAfter'_mkRecName ?_ _
  match types with
  | [] => exact IsNestedName.not_anonymous
  | t :: _ => exact (h t List.mem_cons_self).1

/-- **The Lean-level name budget is clean.**  `indDeclNames` is the block's own names and
`mkRecName` of each; `IsNestedName.mkRecName_iff` covers the third component. -/
theorem NoNestedDeclNames.indDeclNames {types : List InductiveType} (h : NoNestedDeclNames types) :
    ∀ n ∈ Lean4Lean.indDeclNames types, ¬ IsNestedName n := by
  intro n hn
  rw [Lean4Lean.indDeclNames, List.mem_append, List.mem_append] at hn
  rcases hn with (hn | hn) | hn
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
    exact (h t ht).1
  · obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hn
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 hc
    exact (h t ht).2 c hcm
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
    exact fun hx => (h t ht).1 (IsNestedName.mkRecName_iff.1 hx)

/-- …and so is the whole nested budget, auxiliary recursors included. -/
theorem NoNestedDeclNames.indDeclNamesN {types : List InductiveType} {numNested : Nat}
    (h : NoNestedDeclNames types) :
    ∀ n ∈ Lean4Lean.indDeclNamesN types numNested, ¬ IsNestedName n := by
  intro n hn
  rw [Lean4Lean.indDeclNamesN, List.mem_append] at hn
  rcases hn with hn | hn
  · exact h.indDeclNames n hn
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hn
    exact h.auxRecName k

namespace VEnv
variable {env env' : VEnv} {D : VInductDecl'} {R : VIndRestore} {K : List Name}

/-- **`NoNestedN` is preserved by a clean `addConstList`.**  The primitive step. -/
theorem NoNestedN.addConstList : ∀ {cs : List (Name × VConstant)} {env env' : VEnv},
    env.NoNestedN → (∀ p ∈ cs, ¬ IsNestedName p.1) →
    env.addConstList cs = some env' → env'.NoNestedN := by
  intro cs env env' hnn hcs h
  intro n hc hx
  by_cases hm : n ∈ cs.map (·.1)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    exact hcs p hp hx
  · obtain ⟨ci, hci⟩ := hc
    rw [VEnv.addConstList_constants_of_not_mem h hm] at hci
    exact hnn ⟨ci, hci⟩ hx

/-- **The invariant is preserved by the restored step.**  `addInductR` adds the constants
`D.allConstsCR R K` and then only ι-rules, which do not touch `constants`
(`VEnv.addInductR_constants_of_not_mem`, `Theory/Inductive/NestedHead.lean`:500).  So the whole
content is the *name* hypothesis, and §2's point is that §1 supplies it. -/
theorem NoNestedN.addInductR (hnn : env.NoNestedN)
    (hcl : ∀ n ∈ D.allNamesCR R K, ¬ IsNestedName n)
    (hadd : env.addInductR D K R = some env') : env'.NoNestedN := by
  intro n hc hx
  by_cases hm : n ∈ D.allNamesCR R K
  · exact hcl n hm hx
  · obtain ⟨ci, hci⟩ := hc
    rw [VEnv.addInductR_constants_of_not_mem hadd hm] at hci
    exact hnn ⟨ci, hci⟩ hx

/-- **The invariant is preserved, from the gate condition on the block the user wrote.**

This is the statement the measurement was about, made conditional in exactly the honest place:
the hypothesis is `NoNestedDeclNames types` — §1, i.e. what `checkNoNestedAuxName` establishes —
and *not* a fact about the abstract block, whose companion members are `_nested`-named on
purpose.  `TrIndDeclN` is the translation the nested branch already carries; `hst` is its
`addIndTypesC` premise, which `mem_indDeclNamesN` needs. -/
theorem NoNestedN.addInductR_of_tr {e₁ : VEnv} {Us : List Name} {np numNested : Nat}
    {types : List InductiveType} {iu : Bool}
    (hnn : env.NoNestedN) (htr : TrIndDeclN env Us np types iu numNested D K R)
    (hst : env.addIndTypesC D K = some e₁) (hgate : NoNestedDeclNames types)
    (hadd : env.addInductR D K R = some env') : env'.NoNestedN :=
  hnn.addInductR (fun n hn => hgate.indDeclNamesN n (htr.mem_indDeclNamesN hst hn)) hadd

end VEnv

/-! ## §3 The discharges: which assumed obligations become theorems, and from which condition

The obligations the restoration layer *assumes* are `RestoreData`'s prefix group
(`Verify/Inductive/NestedRestore.lean`:299-309) and the `FreshIn`/`NoConstIn` side conditions of
the `Restrict*` lemmas.  They do not all need the same condition, and separating them is the
point of this section.

| obligation | condition it needs | status |
| --- | --- | --- |
| `RestoreData.auxRec` (`:308`) | §1 (the gate) alone | **discharged outright**: `NoNestedDeclNames.auxRecName` |
| `RestoreData.ownName` (`:300`) | §1 + `run_prefix` | **discharged**: `ownName_of_gate` below |
| `RestoreData.ownCtor` (`:302`) | §1 + `run_prefix` | **discharged**: `ownCtor_of_gate` below |
| `RestoreData.head` (`:304`) | §2 (`NoNestedN`) + "the presented head is declared" | **reduced**: `presentedHead_clean_of_declared`; residual named |
| `RestoreData.headNe` (`:306`) | neither — a shape fact about `presentedHead`, not a prefix fact | untouched |
| `RestoreData.args` (`:309`) | §2 (`NoNestedN`) | already routed: `ProjNoNested.lean`'s `hnn` consumers |
| `(R.csubstTy D K).FreshIn env` (`RestrictStep.lean`:81, `RestrictCompanion.lean`:640/717, `SpineClause.lean`:201) | **neither** | already discharged, and *not* from either condition: `VIndRestore.csubstTy_freshIn` (`Theory/Inductive/TeleMove2.lean`:98) gets it from the type-staging success alone |

The last row is worth stating because it is a *negative* result about my own condition: the
`Restrict*` files' freshness hypothesis is not one of the things the measurement buys, and a
second route to it would be a duplicate. -/

namespace ElimNestedInductive.Result

variable {fuel np : Nat} {types : List InductiveType} {s : ElimNestedInductive.State}
  {r : Result} {s' : ElimNestedInductive.State} {cenv : Environment}

/-- **`RestoreData.ownName`, discharged from the gate.**  `ownName_of_run`
(`Verify/Inductive/NestedOccData.lean` §8) reduced the field to a hypothesis on the checker's
*input* block, and recorded it as "the unchecked name-discipline fact" — ledger row 58.  Since
`checkNoNestedAuxName` landed, that hypothesis **is** checked, and §1 is the proof: so the field
is a theorem for every block `Environment.addInductive` accepts. -/
theorem ownName_of_gate (hgate : NoNestedDeclNames types) (hs : s.newTypes.toList = types)
    (h : ElimNestedInductive.run fuel np types cenv s = .ok (r, s')) :
    ∀ (j : Nat) t, r.types[j]? = some t → j < types.length → ¬ IsNestedName t.name :=
  ownName_of_run hs h fun u hu => (hgate u hu).1

/-- …and `RestoreData.ownCtor`, the same way. -/
theorem ownCtor_of_gate (hgate : NoNestedDeclNames types) (hs : s.newTypes.toList = types)
    (h : ElimNestedInductive.run fuel np types cenv s = .ok (r, s')) :
    ∀ (j : Nat) t, r.types[j]? = some t → j < types.length →
      ∀ c ∈ t.ctors, ¬ IsNestedName c.name :=
  ownCtor_of_run hs h fun u hu c hc => (hgate u hu).2 c hc

/-- **`RestoreData.head`, reduced.**  The presented head of a companion member is the constant
the nested occurrence was headed by — `List` for `_nested.List_1` — and that constant is one the
*ambient environment already declares*, which is how `replaceIfNested` found it.  So the field is
§2's condition applied to a declared name, and the whole residual is the premise `hdecl`: that
`presentedHead` lands on a declared constant.  Nothing in this tree proves `hdecl` yet; it is a
statement about `aux2nested`'s values, not about names, so §1 cannot supply it. -/
theorem presentedHead_clean_of_declared {venv : VEnv} (hnn : venv.NoNestedN)
    (hdecl : ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j →
      venv.contains (r.presentedHead t.name)) :
    ∀ (j : Nat) t, r.types[j]? = some t → types.length ≤ j →
      ¬ IsNestedName (r.presentedHead t.name) :=
  fun j t ht hj => hnn (hdecl j t ht hj)

end ElimNestedInductive.Result

/-! ## §4 Instantiation at `ntreeAux` — the block the kernel really runs nested elimination on

`ntreeAux` (`Theory/Inductive/NestedHead.lean`:624) is the *parameterised* nested block:
`uvars = 1`, `params = [.sort (.succ (.param 0))]`, member 0 the user's `NTree`, member 1 the
companion `_nested.List_1`.  (`nfnAux` is the degenerate one — `uvars = 0`, `params = []` — and is
deliberately not used here.)

Everything below is closed: no environment variable, no unsatisfiable premise.  The pair of
statements in `ntree_restoration_keeps_the_environment_clean` is the measurement itself, at the
one block that exhibits the phenomenon. -/

namespace InductiveDeclExamples

/-- **The restored step's declared names carry no reserved prefix.**  Computed, not assumed:
`ntreeAux.allNamesCR ntreeRestore ntreeK` is
`[NTree, NTree.node, NTree.rec, NTree.rec_1]` — the auxiliary family is gone, exactly as the
shell measurement says. -/
theorem ntree_allNamesCR_eq :
    ntreeAux.allNamesCR ntreeRestore ntreeK
      = [`Lean4Lean.InductiveDeclExamples.NTree, `Lean4Lean.InductiveDeclExamples.NTree.node,
         `Lean4Lean.InductiveDeclExamples.NTree.rec,
         `Lean4Lean.InductiveDeclExamples.NTree.rec_1] := rfl

/-- …so the `∀`s below are not vacuous: the list has four entries, one of them the *renamed*
auxiliary recursor `NTree.rec_1`, which is the only trace the companion member leaves. -/
theorem ntree_allNamesCR_length : (ntreeAux.allNamesCR ntreeRestore ntreeK).length = 4 := rfl

theorem ntree_allNamesCR_clean :
    ∀ n ∈ ntreeAux.allNamesCR ntreeRestore ntreeK, ¬ IsNestedName n := by decide

/-- **…and the *unrestored* budget does carry it.**  `ntreeAux.allNames` — what `addInduct'`
declares — contains `_nested.List_1`.  So the two lists differ in exactly the way the
restoration is supposed to make them differ. -/
theorem ntree_allNames_not_clean : ¬ ∀ n ∈ ntreeAux.allNames, ¬ IsNestedName n := by decide

/-- The restored step **succeeds** from the empty environment: `addInductR` asks only for
freshness and no repeated name, and both are computations here.  (This is what keeps §4 from
being a family of vacuous implications.) -/
theorem ntree_addInductR_exists :
    ∃ env', VEnv.empty.addInductR ntreeAux ntreeK ntreeRestore = some env' :=
  VEnv.addInductR_eq_some_iff.2 ⟨fun _ _ => rfl, by decide⟩

/-- …and the environment it produces satisfies the invariant. -/
theorem ntree_addInductR_noNestedN {env' : VEnv}
    (h : VEnv.empty.addInductR ntreeAux ntreeK ntreeRestore = some env') : env'.NoNestedN :=
  NestedWit.empty_noNestedN.addInductR ntree_allNamesCR_clean h

/-- The *unrestored* step succeeds too — already at its first stage, which needs no restoration
data at all. -/
theorem ntree_addIndTypes_exists : ∃ e₁, VEnv.empty.addIndTypes ntreeAux = some e₁ :=
  VEnv.addConstList_eq_some_iff.2 ⟨fun _ _ => rfl, by decide⟩

/-- …and the environment **it** produces fails the invariant, because `_nested.List_1` is in it.
This is the half that makes the restoration load-bearing rather than cosmetic. -/
theorem ntree_addIndTypes_not_noNestedN {e₁ : VEnv}
    (h : VEnv.empty.addIndTypes ntreeAux = some e₁) : ¬ e₁.NoNestedN := by
  have hm : `_nested.List_1 ∈ ntreeAux.typeConsts.map (·.1) := by
    rw [VInductDecl'.typeConsts_names]; decide
  obtain ⟨p, hp, hn⟩ := List.mem_map.1 hm
  exact fun hnn => hnn (n := `_nested.List_1)
    ⟨p.2, hn ▸ VEnv.addConstList_constants h p hp⟩ (by decide)

/-- **The measurement, as one closed statement.**  From the *same* starting environment and the
*same* nested block: the restored step succeeds and leaves no `_nested` constant behind, while
the unrestored one succeeds and leaves one.  So "zero `_nested` constants in the environment" is
a property of the restoration, not of the block. -/
theorem ntree_restoration_keeps_the_environment_clean :
    (∃ env', VEnv.empty.addInductR ntreeAux ntreeK ntreeRestore = some env' ∧ env'.NoNestedN) ∧
      (∃ e₁, VEnv.empty.addIndTypes ntreeAux = some e₁ ∧ ¬ e₁.NoNestedN) :=
  ⟨let ⟨_, h⟩ := ntree_addInductR_exists; ⟨_, h, ntree_addInductR_noNestedN h⟩,
   let ⟨_, h⟩ := ntree_addIndTypes_exists; ⟨_, h, ntree_addIndTypes_not_noNestedN h⟩⟩

/-- The same contrast at the ι-rule-carrying step, from the general theorem already in the tree:
the *unrestored* `addInduct'` of `ntreeAux` breaks the invariant at its companion member.  Stated
at an arbitrary `env` because that is the form `noNestedN_false_of_companion` has. -/
theorem ntree_addInduct'_not_noNestedN {env env' : VEnv}
    (hadd : env.addInduct' ntreeAux = some env') : ¬ env'.NoNestedN :=
  noNestedN_false_of_companion hadd
    (T := { name := `_nested.List_1,
            type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
            indices := [], ctors := [nlistNil, nlistCons] })
    (by simp [ntreeAux]) (by decide)

end InductiveDeclExamples

/-! ## §5 Is the condition assumable, or must it be established?

**It must be established.  As of 2026-09-04 it CAN be, on every branch — this section's verdict has
flipped, and the paragraph that predicted the flip is its own last one.**

§5 closed by saying: *"One line beside `checkName` in `checkConstantVal` would supply it for all four
— another restrictive-direction divergence, of the same kind and cost as `checkNoNestedAuxName`'s."*
PR #46 (`7e39484`) added exactly that line.  So fact 3 below is **no longer true**, the `#eval` gate in
§5.1 fired on the merge to say so, and `VEnv.NoNestedN.addConst`'s `hn` hypothesis — the one this
section was written to make visible — is now suppliable in all four non-inductive cases.

**The induction has now been run — 2026-09-04.**  The paragraph that stood here said "Unlocked: the
*hypothesis*.  Still open: the *induction*", and that is no longer the status.
`Verify/Inductive/NoNestedAll.lean` runs it:

* §2 there — `VEnv.NoNestedN.of_trEnv' : TrEnv' safety C Q venv → NoNestedMap C → venv.NoNestedN` —
  is the induction, and it needed **no new case analysis at all**: `TrEnv'.aligned` had already run
  the nine-case induction and `Aligned.find?_iff` (`Verify/Environment/Lemmas.lean`:43) had already
  done the `SMap`-insert work, so the whole abstract side is four lines.  **No `TrEnv'` case
  resists.**
* §3 there *establishes* the hypothesis rather than assuming it: `NoNestedMap` holds of the empty
  kernel environment and is preserved by `addDecl` on the `axiomDecl`, `defnDecl` (both safety
  arms), `thmDecl`, `opaqueDecl` and `quotDecl` branches, **unconditionally**.  The load-bearing
  new lemma is `checkConstantVal_noNestedName` — the line PR #46 added, as a theorem about
  `checkConstantVal`'s success rather than about its operational behaviour.  It carries no
  `VEnvs.WF`, deliberately: `checkConstantVal.WF`'s does, and `VEnvs.WF` is unsatisfiable for a map
  holding an `.inductInfo`.
* **One** residual remains: `InductiveMapGate` (the map side of the inductive step — the seven-file
  flip), **unproved, not false**.  *Corrected 2026-09-04.*  This used to name two and grade both
  "unproved, not false".  `MutualNamesGate` is gone, and its grade was wrong in a way worth keeping:
  **as stated it was not provable**, because it omitted `env.constants.WF` — a hypothesis
  `NoNestedMap.add`, `checkConstantVal_find?_none` and `NoNestedEnv` itself all carry, and which its
  only consumer supplies.  The header loop was never the problem; the statement was.
  `Verify/Inductive/MutualNames.lean` proves the postcondition (`addMutual_header_post`) and
  discharges the branch outright (`addMutual_noNestedEnv'`).
* One inherited vacuity: `TrEnv'.aligned`'s `induct` arm is `Aligned.addInduct`, i.e. `nomatch`
  (`addInduct_isEmpty` there proves the emptiness).  So the `induct` case of §2 is discharged
  vacuously today.  This is `AddInduct`'s emptiness and nothing new; when the flip lands,
  `NoNestedAll.lean` does not change.

So the honest verdict is now: **proved, modulo `AddInduct`'s emptiness and two map-side gates** —
not "unlocked in principle".

The original verdict follows, kept verbatim because the reasoning is still the map of what has to be
proved — read fact 3 as history, not as current behaviour.

**~~It must be established, and today it cannot be — outside the inductive branch.~~**

Three facts settle it.

1. **Not assumable.**  `NoNestedN` is not a theorem about arbitrary environments and not a
   harmless normalisation: one `addConst` at a prefixed name refutes it
   (`NestedWit.noNestedN_not_preserved`, `Verify/Inductive/ProjNoNested.lean`:604).  So it is an
   invariant, and an invariant has to be *carried*.

2. **The inductive branch's step is proved** — §2 — and it rests on §1, i.e. on
   `checkNoNestedAuxName`.  `ntree_restoration_keeps_the_environment_clean` is the step firing at
   the real nested block: restored, the invariant survives; unrestored, it does not.

3. **The other branches break it.**  ***STALE since 2026-09-04 — this is the fact PR #46 changed.
   `checkConstantVal` now calls `checkNoNestedAuxName` too, so the two acceptances described below are
   now rejections.  Kept as the statement of what used to block the invariant.***
   `checkConstantVal` (`Lean4Lean/Environment.lean`:12) —
   the common gate of `addAxiom`, `addDefinition`, `addTheorem` and `addOpaque` — calls
   `checkName`, and `checkName` (`Lean4Lean/Environment/Basic.lean`:54) tests only "already
   declared" and `Environment.primitives`.  There is no prefix test, so
   `axiom _nested.zzz : Prop` and `def _nested.ddd := Prop` are **accepted**, and the invariant
   fails one step later.  `nested_name_gate_measurement` below is that measurement, self-checking.

~~So the honest status of every §3 discharge that needs §2 (`RestoreData.head`, and
`ProjNoNested.lean`'s `hnn` consumers) is: **conditional on an invariant the implementation
establishes for inductives only.**~~  **Superseded 2026-09-04.**  Those discharges are now
conditional on `VEnv.NoNestedN` of an environment the *kernel built*, and that is a theorem:
`VEnv.NoNestedN.of_addDecl` (`Verify/Inductive/NoNestedAll.lean`).  The remaining conditions are
`NoNestedMap` of the starting map — which the empty environment satisfies and `addDecl` preserves —
plus the two gates named above.  So §3's `RestoreData.head` row and `ProjNoNested.lean`'s `hnn`
consumers are **unconditional on the four `checkConstantVal` branches and on `quotDecl`**, and
conditional only on a named map-side residual for `mutualDefnDecl` and `inductDecl`.  The
discharges that need only §1 (`auxRec`, `ownName`, `ownCtor`) were, and remain, unconditional for
any block the gate accepted, because the gate is where the check lives.

Where it would have to be established, exactly: by induction on `TrEnv'`
(`Verify/Environment/Basic.lean`:634 and its constructors), whose `axiom`/`defn`/`opaque`/`quot`
cases would each need "the added name is not prefixed".  **This is where it was established, and
the prediction about the *route* was wrong**: the induction did not have to be written case by
case, because `TrEnv'.aligned` + `Aligned.find?_iff` already carry it, and the condition that
actually has to be threaded is the *kernel-level* `NoNestedMap`, not the abstract one.  The
single-constant step is `VEnv.NoNestedN.addConst` below; its `hn` hypothesis is precisely what no
implementation check supplied until PR #46, and `checkConstantVal_noNestedName`
(`Verify/Inductive/NoNestedAll.lean`) is now the proof that it does.  One line beside `checkName` in `checkConstantVal` would supply it for all four —
another restrictive-direction divergence, of the same kind and cost as
`checkNoNestedAuxName`'s. -/

namespace VEnv

/-- **The step the non-inductive branches would need.**  Stated so that the missing hypothesis
`hn` is visible in a statement rather than in prose: nothing in `checkConstantVal` establishes
it. -/
theorem NoNestedN.addConst {env env' : VEnv} {n : Name} {ci : VConstant}
    (hnn : env.NoNestedN) (hn : ¬ IsNestedName n) (h : env.addConst n ci = some env') :
    env'.NoNestedN :=
  hnn.addConstList (cs := [(n, ci)])
    (by intro p hp; rw [List.mem_singleton] at hp; subst hp; exact hn)
    (by rw [VEnv.addConstList_cons, h]; rfl)

end VEnv

/-! ### §5.1 The measurement, self-checking

If any of the three flips, the build fails here rather than in prose: `axiom _nested.zzz`
accepted, `inductive _nested.Zzz` rejected (that is `checkNoNestedAuxName` firing — before it
landed this case was accepted and stored, `docs/decision-nested-prefix.md`), `def _nested.ddd`
accepted.  Nothing is pretty-printed: `ppExpr` needs environment extensions that a
`Kernel.Environment` built here does not have. -/
#eval show Lean.CoreM Unit from do
  let kenv := Lean.Kernel.Environment.empty `main
  let ax := Lean4Lean.addDecl kenv (.axiomDecl
    { name := `_nested.zzz, levelParams := [], type := .sort .zero, isUnsafe := false })
  let ind := Lean4Lean.addDecl kenv (.inductDecl [] 0
    [{ name := `_nested.Zzz, type := .sort (.succ .zero), ctors := [] }] false)
  let df := Lean4Lean.addDecl kenv (.defnDecl
    { name := `_nested.ddd, levelParams := [], type := .sort (.succ .zero),
      value := .sort .zero, hints := .abbrev, safety := .safe })
  unless ind.toOption.isNone do
    throwError "RestoreFaithful/gate: Lean4Lean.addDecl ACCEPTS `inductive _nested.Zzz` --       checkNoNestedAuxName is not firing, and every discharge in §3 that reads the gate is void"
  -- Updated 2026-09-04, when PR #46 (`7e39484`) fired the tripwire this `unless` used to be.
  -- It asserted that `axiom`/`def` at a prefixed name were still ACCEPTED, and said that if they
  -- ever were not, §5's verdict had gone stale in the good direction.  They now are not.
  unless ax.toOption.isNone && df.toOption.isNone do
    throwError "RestoreFaithful/gate: `axiom _nested.zzz` or `def _nested.ddd` is ACCEPTED again --       checkNoNestedAuxName has been dropped from checkConstantVal, so §5's all-branches verdict       and every discharge resting on it are void; restore the check or revert §5.       This now also falsifies `checkConstantVal_noNestedName` and all of       `Verify/Inductive/NoNestedAll.lean` §3, which is where the induction was run"
  Lean.logInfo "RestoreFaithful/gate: all three of `inductive _nested.Zzz`, `axiom _nested.zzz`     and `def _nested.ddd` are REJECTED -- checkNoNestedAuxName fires in the inductive branch AND in     checkConstantVal, so NoNestedN's missing hypothesis is supplied on every addDecl branch, and     the induction that consumes it is RUN (`Verify/Inductive/NoNestedAll.lean`) ✓"

#print axioms Lean4Lean.checkNoNestedAuxName_ok_iff
#print axioms Lean4Lean.addInductive_WF_noNestedDeclNames
#print axioms Lean4Lean.NoNestedDeclNames.auxRecName
#print axioms Lean4Lean.NoNestedDeclNames.indDeclNamesN
#print axioms Lean4Lean.VEnv.NoNestedN.addInductR
#print axioms Lean4Lean.VEnv.NoNestedN.addInductR_of_tr
#print axioms Lean4Lean.ElimNestedInductive.Result.ownName_of_gate
#print axioms Lean4Lean.ElimNestedInductive.Result.ownCtor_of_gate
#print axioms Lean4Lean.InductiveDeclExamples.ntree_restoration_keeps_the_environment_clean

end Lean4Lean
