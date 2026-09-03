import Lean4Lean.Verify.Inductive.ProjNoNested
import Lean4Lean.Theory.Inductive.NestedFresh

/-!
# A spine clause for `VNestedOcc.Occurs`, and why it cannot be a *typing* clause

The brief for this round asked for **a typing clause for `args`** on
`Lean4Lean.VNestedOcc.Occurs` (`Theory/Inductive/NestedBuild.lean`:648), so that
`ElimNestedInductive.Result.RestoreData`'s `args` field
(`Verify/Inductive/NestedRestore.lean`:490)

    args : ∀ j, ∀ a ∈ tyArgs j, a.NoConstIn IsNestedName

is discharged with no `Expr`-side reasoning.  Both of those line references check out.

**A typing clause is the wrong shape, and this file proves it.**  §4 refutes it; §1–§3 give the
shape that works.  The refutation is short enough to state here:

* `Occurs` is stated at the environment **before** the new block is declared.  The nested spine
  `N.args` is `Ds`, the arguments of the nested occurrence, and those mention the block *being*
  declared — measured, not read off: `listOcc.args = [NTree α]` and
  `pfnOcc.args = [NFn]`, while `listOcc.Occurs env₁` has
  `env₁ = VEnv.empty.addInduct' listDecl` and `pfnOcc.Occurs env₂` has
  `env₂ = VEnv.empty.addInduct' pfnDecl`.  Neither environment declares `NTree` / `NFn`.
  So `∀ a ∈ N.args, VExpr.WF env U Γ a` is **refutable** at both witnesses (§4.1) — this is
  `docs/vacuity-ledger.md` rows 6 and 11 exactly: an occurrence hypothesis at the pre-step
  environment, unsatisfiable rather than merely weak.
* Restating it at the **post**-step environment does not rescue it either, and this is the
  second trap: `ElimNestedInductive.Result.args_of_wf`
  (`Verify/Inductive/ProjNoNested.lean`:581) is the existing typing-route producer for
  `RestoreData.args`, and its other premise is `VEnv.NoNestedN env` — no declared name carries
  the `_nested` prefix.  The post-step environment declares the **companions**, whose names are
  exactly the `_nested`-prefixed ones, so `NoNestedN` is false there (§4.2).  The two premises of
  `args_of_wf` are therefore satisfiable at *no* environment of the step: the pre-step one fails
  `hwf`, the post-step one fails `hnn`.

What does work is an **environment-free** clause: the spine mentions no reserved name.  §1 states
it, §2 shows it inhabited (at a named environment, with a witness), §3 is the negative control,
§5 is the exact edit and the two names that have to move for it to typecheck.

One bonus the brief did not ask for: the same single clause also discharges
`VNestedOcc.fields_noK_of_occurs`'s `hargs` premise (§1.3), which
`Theory/Inductive/NestedFresh.lean`'s `fields_noK_needs_spine` proved is *not* a consequence of
`Occurs`.  So the clause pays for `Built.fields_noK` and `RestoreData.args` at once.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §1 The clause, and the discharge

`OccursN` is `Occurs` plus one field.  Using `extends` rather than a transcribed copy makes the
collapse test (§1.1) an `Iff` with nothing hidden in it: `OccursN.toOccurs` is *the* existing
predicate, not a re-proof of it. -/

namespace VNestedOcc

/-- **The strengthened occurrence record.**  `Occurs` verbatim, plus: the nested spine mentions
no reserved name.

`IsNestedName` (`Verify/Inductive/NestedRestore.lean`:211) is
`(`_nested).isPrefixOf n = true` — a predicate on `Name` alone, no environment, no `VEnv`.  That
is the whole point: §4 shows every environment-indexed spelling of this clause is false at one
end of the step or the other. -/
structure OccursN (N : VNestedOcc) (env : VEnv) : Prop extends N.Occurs env where
  /-- **The new clause.**  `Ds` mentions no `_nested`-prefixed constant. -/
  args_noNested : ∀ a ∈ N.args, a.NoConstIn IsNestedName

variable {N : VNestedOcc} {env : VEnv}

/-! ### §1.1 Collapse: `OccursN` is exactly `Occurs` plus the clause -/

/-- Forgetting the clause gives back the existing predicate, unchanged. -/
theorem OccursN.collapse (h : N.OccursN env) : N.Occurs env := h.toOccurs

/-- …and the converse: nothing else was strengthened. -/
theorem occursN_of_occurs (ho : N.Occurs env)
    (ha : ∀ a ∈ N.args, a.NoConstIn IsNestedName) : N.OccursN env :=
  { ho with args_noNested := ha }

/-- **The collapse test, as an `Iff`.**  If this were not an `Iff` the clause would be smuggling
extra content past the reader. -/
theorem occursN_iff :
    N.OccursN env ↔ N.Occurs env ∧ ∀ a ∈ N.args, a.NoConstIn IsNestedName :=
  ⟨fun h => ⟨h.toOccurs, h.args_noNested⟩, fun ⟨h1, h2⟩ => occursN_of_occurs h1 h2⟩

end VNestedOcc

/-! ### §1.2 `RestoreData.args`, discharged

The one hypothesis that is *not* about occurrences is `hcases`: at an index with no occurrence
the abstract spine must be empty.  That is not slack — `RestoreData.args` quantifies over **all**
`j : Nat`, including `j` past `r.types.length`, where `as j` is unconstrained junk chosen by the
caller.  §5.2 records that `RestoreData.args`'s `j < types.length` instances are dead weight for
its only two consumers, and what the corresponding narrowing would be. -/

namespace VNestedOcc

/-- **The discharge, in the exact shape of `RestoreData`'s `args` field.**  No `Expr`, no
`TrExprS`, no gate, no `hproj`, no environment invariant: the conclusion is read straight off the
new clause.

`Comp` is the caller's notion of "index `j` carries a companion occurrence"; at the construction
it is `fun j => types.length ≤ j ∧ j < r.types.length`, and `hagree` is `Built.tyArgs`. -/
theorem args_of_occursN {as : Nat → List VExpr} {occ : Nat → VNestedOcc} {env : VEnv}
    {Comp : Nat → Prop}
    (hagree : ∀ j, Comp j → as j = (occ j).args)
    (hocc : ∀ j, Comp j → (occ j).OccursN env)
    (hcases : ∀ j, Comp j ∨ as j = []) :
    ∀ j, ∀ a ∈ as j, a.NoConstIn IsNestedName := by
  intro j a ha
  rcases hcases j with hj | hnil
  · exact (hocc j hj).args_noNested a (hagree j hj ▸ ha)
  · rw [hnil] at ha; exact absurd ha (by simp)

/-- The same with `Comp` eliminated: one hypothesis, no auxiliary predicate.  This is the
weakest form the conclusion can be got from. -/
theorem args_of_occursN' {as : Nat → List VExpr} {env : VEnv}
    (h : ∀ j, (∃ N : VNestedOcc, N.OccursN env ∧ as j = N.args) ∨ as j = []) :
    ∀ j, ∀ a ∈ as j, a.NoConstIn IsNestedName := by
  intro j a ha
  rcases h j with ⟨N, hN, he⟩ | hnil
  · exact hN.args_noNested a (he ▸ ha)
  · rw [hnil] at ha; exact absurd ha (by simp)

end VNestedOcc

/-! ### §1.3 The same clause pays for `fields_noK` too

`VNestedOcc.fields_noK_of_occurs` (`Theory/Inductive/NestedBuild.lean`:961) carries a premise
`hargs : ∀ a ∈ N.args, VExpr.NoConsts K a`, and `Theory/Inductive/NestedFresh.lean`'s
`fields_noK_needs_spine` proves that premise is **not** removable — `Occurs` cannot see the spine.
The new clause supplies it, given only that every companion name is reserved, which is
`RestoreData.isNestedName_of_mem` (`Verify/Inductive/SpineTransfer.lean`:113).  So one field on
`Occurs` closes `Built.fields_noK`'s residual *and* `RestoreData.args`. -/

namespace VNestedOcc

/-- `hargs`, from the new clause. -/
theorem OccursN.args_noConsts {N : VNestedOcc} {env : VEnv} {K : List Name}
    (h : N.OccursN env) (hK : ∀ n ∈ K, IsNestedName n) :
    ∀ a ∈ N.args, VExpr.NoConsts K a :=
  fun a ha => VExpr.noConsts_of_noConstIn hK (h.args_noNested a ha)

/-- …hence `fields_noK`'s body with **no** spine hypothesis left. -/
theorem OccursN.fields_noK {N : VNestedOcc} {env : VEnv} {K : List Name}
    (hcc : env.ConstsClosedC) (h : N.OccursN env) (hKf : ∀ n ∈ K, ¬ env.contains n)
    (hK : ∀ n ∈ K, IsNestedName n)
    {C₀ : VIndCtor} (hC₀ : C₀ ∈ N.src.ctors) {k : Nat} {F₀ : VIndField}
    (hF₀ : C₀.fields[k]? = some F₀) :
    VExpr.NoConsts K (VExpr.instAll (F₀.type.instL N.lvls) N.args k) :=
  fields_noK_of_occurs hcc h.toOccurs hKf (h.args_noConsts hK) hC₀ hF₀

end VNestedOcc

#print axioms Lean4Lean.VNestedOcc.OccursN.collapse
#print axioms Lean4Lean.VNestedOcc.occursN_iff
#print axioms Lean4Lean.VNestedOcc.args_of_occursN
#print axioms Lean4Lean.VNestedOcc.args_of_occursN'
#print axioms Lean4Lean.VNestedOcc.OccursN.args_noConsts
#print axioms Lean4Lean.VNestedOcc.OccursN.fields_noK

/-! ## §2 The clause is inhabited — **at a named environment**

The environment is stated, not left implicit, because the ledger's rows 6 and 11 are both cases
of a clause that is fine at one environment and unsatisfiable at another.

* `env₁` is fixed by `VEnv.empty.addInduct' listDecl = some env₁`: the environment in which
  `List` is declared and `NTree` is **not**.  It is the environment the `NTree` step runs *at*.
* `env₂` is fixed by `VEnv.empty.addInduct' pfnDecl = some env₂`: `PFn` declared, `NFn` not.

Both are the **pre**-step environment for the block being declared and the **post**-step
environment for the block being nested.  That is exactly where `Occurs` lives, and §4 is the
proof that the *typing* reading of the clause is refutable there. -/

namespace InductiveDeclExamples

open VNestedOcc

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- **`OccursN` at the `NTree`/`List` witness.**  The new clause is one `decide`: the spine is
`[NTree α]`, and `NTree` is not reserved. -/
theorem listOcc_occursN : listOcc.OccursN env₁ :=
  occursN_of_occurs (listOcc_occurs h) (by decide)

end

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
include h

/-- **`OccursN` at the `NFn`/`PFn` witness**, the one the `Verify`-side bundles use. -/
theorem pfnOcc_occursN : pfnOcc.OccursN env₂ :=
  occursN_of_occurs (pfnOcc_occurs h) (by decide)

/-- …and the inhabitation as an existential, so nothing reads as a statement about one fixed
occurrence. -/
theorem occursN_inhabited : ∃ N : VNestedOcc, N.OccursN env₂ ∧ N.args ≠ [] :=
  ⟨pfnOcc, pfnOcc_occursN h, by decide⟩

end

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.listOcc_occursN
#print axioms Lean4Lean.InductiveDeclExamples.pfnOcc_occursN
#print axioms Lean4Lean.InductiveDeclExamples.occursN_inhabited

/-! ## §3 Negative control: the clause is a real restriction

If the strengthening were satisfied by everything it would discharge nothing.  The separating
pair is already in the tree: `Theory/Inductive/NestedFresh.lean`'s `listOccBadSpine` is `listOcc`
with the spine `[NTree α]` replaced by the companion constant `[_nested.List_1 α]`.  `Occurs`
cannot tell them apart (`VNestedOcc.occurs_args_congr`: only `args_len` mentions `N.args`, and
only its length), so `listOccBadSpine.Occurs env₁` holds — and `OccursN` fails.

This is the sharpest form of the control: it shows not just that the clause bites, but that
`Occurs` is *exactly* silent about the spine's constants, so the clause adds content that no
amount of environment reasoning could recover. -/

namespace InductiveDeclExamples

open VNestedOcc

/-- `pfnOcc` with the spine replaced by the companion constant.  Same length, so same `Occurs`. -/
def pfnOccBadSpine : VNestedOcc := { pfnOcc with args := [.const `_nested.PFn_1 []] }

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- **The control at the `List` witness.**  Same `Occurs env₁`; `OccursN env₁` fails. -/
theorem listOccBadSpine_not_occursN :
    listOccBadSpine.Occurs env₁ ∧ ¬ listOccBadSpine.OccursN env₁ :=
  ⟨listOccBadSpine_occurs h, fun hN => by
    have := hN.args_noNested (.const `_nested.List_1 [.param 0]) (by decide)
    revert this; decide⟩

/-- **The separating pair, spelled out.**  Everything `Occurs` can see agrees; the new clause
separates.  So `Occurs → OccursN` is false, and the strengthening is proper. -/
theorem occursN_proper :
    listOccBadSpine.decl = listOcc.decl ∧ listOccBadSpine.idx = listOcc.idx ∧
      listOccBadSpine.lvls = listOcc.lvls ∧ listOccBadSpine.auxName = listOcc.auxName ∧
      listOccBadSpine.args.length = listOcc.args.length ∧
      listOcc.OccursN env₁ ∧ listOccBadSpine.Occurs env₁ ∧ ¬ listOccBadSpine.OccursN env₁ :=
  ⟨rfl, rfl, rfl, rfl, rfl, listOcc_occursN h, listOccBadSpine_occurs h,
   (listOccBadSpine_not_occursN h).2⟩

end

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
include h

/-- The same control at the `PFn` witness. -/
theorem pfnOccBadSpine_not_occursN :
    pfnOccBadSpine.Occurs env₂ ∧ ¬ pfnOccBadSpine.OccursN env₂ :=
  ⟨occurs_args_congr (pfnOcc_occurs h) rfl, fun hN => by
    have := hN.args_noNested (.const `_nested.PFn_1 []) (by decide)
    revert this; decide⟩

end

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_not_occursN
#print axioms Lean4Lean.InductiveDeclExamples.occursN_proper
#print axioms Lean4Lean.InductiveDeclExamples.pfnOccBadSpine_not_occursN

/-! ## §4 The brief's shape refuted: a *typing* clause is satisfiable at no environment of the step

The brief asked for a **typing** clause.  The existing typing-route producer for
`RestoreData.args` is `ElimNestedInductive.Result.args_of_wf`
(`Verify/Inductive/ProjNoNested.lean`:581):

    (henv : VEnv.WF env) (hnn : env.NoNestedN) (hΓ : OnCtx Γ (env.IsType U))
    (hwf : ∀ j, ∀ a ∈ as j, VExpr.WF env U Γ a) → ∀ j, ∀ a ∈ as j, a.NoConstIn IsNestedName

so a typing clause on `Occurs` would have to supply `hwf` at the environment `Occurs` is stated
at.  Two facts, each proved below, close that off:

* §4.1 at the **pre**-step environment `hwf` is **false**: the spine names the block being
  declared.  Not merely false for typing — false already for the far weaker
  `ConstsIn env.contains`, which typing implies.  Ledger rows 6 and 11.
* §4.2 at the **post**-step environment `hnn` is **false**: the companion names are declared
  there, and they are precisely the reserved ones.

So the two premises cannot be met at the same environment as long as the block has a companion —
and a nested occurrence exists exactly when it does.  §4.3 states the conjunction. -/

namespace InductiveDeclExamples

open VNestedOcc

/-! ### §4.1 The spine is not even *declared* at the pre-step environment -/

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
include h

/-- `NFn` — the block the `pfnOcc` occurrence sits inside — is not a constant of `env₂`. -/
theorem nfn_not_contains_env₂ : ¬ env₂.contains ``NFn := by
  rintro ⟨ci, hc⟩
  rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc
  exact absurd hc nofun

/-- **The weakest environment-side spine clause is already false.**  `ConstsIn env.contains` is
implied by well-typedness in an `Ordered` environment, so this refutes every typing spelling at
once, with no `Ordered`, no `OnCtx` and no `VEnv.WF` in sight. -/
theorem pfnOcc_args_not_constsIn :
    ¬ ∀ a ∈ pfnOcc.args, VExpr.ConstsIn a env₂.contains := by
  intro hcl
  exact nfn_not_contains_env₂ h (hcl (.const ``NFn []) (by decide))

/-- …hence the typing clause itself, for **every** `U` and every context the environment admits.
The `Ordered`/`OnCtx` hypotheses are the ones `VEnv.IsDefEq.constsIn` needs; they are not what
fails. -/
theorem pfnOcc_args_not_wf (henv : env₂.Ordered) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env₂.IsType U)) :
    ¬ ∀ a ∈ pfnOcc.args, VExpr.WF env₂ U Γ a := by
  intro hwf
  refine pfnOcc_args_not_constsIn h fun a ha => ?_
  obtain ⟨A, hA⟩ := hwf a ha
  exact (hA.constsIn henv.constsIn (VEnv.ctxConstsIn_of_onCtx henv hΓ)).1

/-- The empty context needs no side condition at all. -/
theorem pfnOcc_args_not_wf_nil (henv : env₂.Ordered) {U : Nat} :
    ¬ ∀ a ∈ pfnOcc.args, VExpr.WF env₂ U [] a :=
  pfnOcc_args_not_wf h henv trivial

end

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- The same at the `NTree`/`List` witness, where the spine is the *applied* head `NTree α`
rather than a bare constant — so the refutation is not an artefact of the second witness's
degenerate zero-parameter shape. -/
theorem listOcc_args_not_constsIn :
    ¬ ∀ a ∈ listOcc.args, VExpr.ConstsIn a env₁.contains := by
  intro hcl
  have h1 : VExpr.ConstsIn (.app (.const ``NTree [.param 0]) (.bvar 0)) env₁.contains :=
    hcl _ (by decide)
  obtain ⟨ci, hc⟩ := h1.1
  rw [VEnv.addInduct'_constants_of_not_mem h (by decide)] at hc
  exact absurd hc nofun

end

/-! ### §4.2 `NoNestedN` is false at the post-step environment -/

/-- **General**: an environment that has just had a block with a reserved member name declared
into it does not satisfy `VEnv.NoNestedN`. -/
theorem noNestedN_false_of_companion {env env' : VEnv} {D : VInductDecl'} {T : VIndType}
    (hadd : env.addInduct' D = some env') (hT : T ∈ D.types) (hn : IsNestedName T.name) :
    ¬ env'.NoNestedN :=
  fun hnn => hnn ⟨_, VEnv.addInduct'_types hadd hT⟩ hn

/-- …at the `NFn` step, whose second member is `_nested.PFn_1`. -/
theorem nfnAux_post_not_noNestedN {env₂ env₃ : VEnv}
    (hadd : env₂.addInduct' nfnAux = some env₃) : ¬ env₃.NoNestedN :=
  noNestedN_false_of_companion hadd
    (T := { name := `_nested.PFn_1, type := .sort (.succ .zero), indices := [],
            ctors := [pfnAuxMk] })
    (by simp [nfnAux]) (by decide)

/-! ### §4.3 The two premises, jointly unsatisfiable across the step

Stated at the concrete step so that nothing is hidden in a quantifier: there is no environment of
the `NFn` step at which `args_of_wf` fires. -/

theorem args_of_wf_unusable_at_step {env₂ env₃ : VEnv}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂) (henv : env₂.Ordered)
    (hadd : env₂.addInduct' nfnAux = some env₃) {U : Nat} :
    (¬ ∀ a ∈ pfnOcc.args, VExpr.WF env₂ U [] a) ∧ ¬ env₃.NoNestedN :=
  ⟨pfnOcc_args_not_wf_nil h henv, nfnAux_post_not_noNestedN hadd⟩

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.nfn_not_contains_env₂
#print axioms Lean4Lean.InductiveDeclExamples.pfnOcc_args_not_constsIn
#print axioms Lean4Lean.InductiveDeclExamples.pfnOcc_args_not_wf
#print axioms Lean4Lean.InductiveDeclExamples.listOcc_args_not_constsIn
#print axioms Lean4Lean.InductiveDeclExamples.noNestedN_false_of_companion
#print axioms Lean4Lean.InductiveDeclExamples.nfnAux_post_not_noNestedN
#print axioms Lean4Lean.InductiveDeclExamples.args_of_wf_unusable_at_step

/-! ## §5 `RestoreData.args` actually discharged, at the tree's own witness

`NestedRestoreWit.lean`:246 proves the `args` field by `decide` on `nfnAs`.  Below is the same
bundle with that field replaced by §1.2's producer, so the discharge is exercised end to end and
not merely stated.  Everything else is `nfnResult_restoreData` unchanged.

**What it costs.**  The `decide` proof mentions no environment; this one carries
`h : VEnv.empty.addInduct' pfnDecl = some env₂`, because the occurrence record does.  That is the
same trade `nfnAux_builtFresh` (`Theory/Inductive/NestedBuild.lean`:1854) took when `fields_noK`
moved from `decide` to the producer, and it is recorded here for the same reason: the *statement*
is weaker than it was.  Every downstream consumer of `RestoreData` at this witness already
carries `h`. -/

namespace NestedWit

open VNestedOcc InductiveDeclExamples

/-- The agreement `Built.tyArgs` supplies, at this witness: measured, `rfl`. -/
theorem nfnAs_eq_pfnOcc_args : ∀ j, j = 1 → nfnAs j = pfnOcc.args := by
  rintro _ rfl; rfl

/-- Off the companion index the abstract spine is empty — the `hcases` premise, at this
witness. -/
theorem nfnAs_cases : ∀ j, j = 1 ∨ nfnAs j = [] := by
  intro j
  by_cases hj : j = 1
  · exact .inl hj
  · exact .inr (by simp [nfnAs, hj])

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
include h

/-- **`RestoreData.args`, from the occurrence record.**  Zero `Expr`, zero `TrExprS`, zero gate,
zero `hproj`, zero `decide` over the spine. -/
theorem nfnAs_args_of_occursN : ∀ j, ∀ a ∈ nfnAs j, a.NoConstIn IsNestedName :=
  args_of_occursN (Comp := fun j => j = 1) nfnAs_eq_pfnOcc_args
    (fun _ _ => pfnOcc_occursN h) nfnAs_cases

/-- **The bundle, rebuilt.**  `nfnResult_restoreData` with its `args` field replaced by the
producer: `RestoreData` still holds, so the producer really is in the field's shape. -/
theorem nfnResult_restoreData_of_occursN :
    nfnResult.RestoreData [nfnIndType] nfnAux nfnK nfnAs :=
  { nfnResult_restoreData with args := nfnAs_args_of_occursN h }

/-- …and it still flows on: the spine premise `Built` needs, through the existing
`RestoreData.spine_noConsts`. -/
theorem nfnAs_noK_of_occursN :
    ∀ (j : Nat) (T : VIndType), nfnAux.types[j]? = some T → T.name ∈ nfnK →
      ∀ a ∈ nfnAs j, VExpr.NoConsts nfnK a :=
  (nfnResult_restoreData_of_occursN h).spine_noConsts nfnK_sub_blockNames

end

end NestedWit

#print axioms Lean4Lean.NestedWit.nfnAs_args_of_occursN
#print axioms Lean4Lean.NestedWit.nfnResult_restoreData_of_occursN
#print axioms Lean4Lean.NestedWit.nfnAs_noK_of_occursN

/-! ## §6 The exact edit, and the one thing it breaks

### §6.1 Do **not** put the field on `Occurs`

The brief asked for the clause *inside* `VNestedOcc.Occurs`.  That edit makes a theorem the tree
currently proves **false**, and the theorem in question is an anti-vacuity control:

`Theory/Inductive/NestedFresh.lean`:91 `VNestedOcc.occurs_args_congr` says `Occurs` cannot see the
spine, and :117 `listOccBadSpine_occurs` and :138 `fields_noK_needs_spine` use it to build the
separating pair that proves `fields_noK` is *not* a consequence of `Occurs`.  `listOccBadSpine`'s
spine is `[_nested.List_1 α]`, so the new clause fails of it.  §3's
`listOccBadSpine_not_occursN` is that fact, and §6.2 below is the induced refutation of the
strengthened `occurs_args_congr`.

So the clause belongs on an **extension** (`OccursN` here), with `Built` threading `OccursN` where
it currently threads `Occurs`, and `Occurs` left alone so the control survives.  The ripple is the
same size either way — the sites are listed in §6.3 — but this way nothing true becomes false.

### §6.2 The induced refutation, machine-checked -/

namespace InductiveDeclExamples

open VNestedOcc

/-- The witness environments exist outright — `addInduct'` at these blocks reduces. -/
theorem listDecl_env_exists : ∃ e, VEnv.empty.addInduct' listDecl = some e := ⟨_, rfl⟩

theorem pfnDecl_env_exists : ∃ e, VEnv.empty.addInduct' pfnDecl = some e := ⟨_, rfl⟩

/-- **`occurs_args_congr` does not survive the strengthening.**  Unconditional: no environment
hypothesis, because the witness environment is `rfl`.  This is the concrete cost of putting the
clause on `Occurs` itself. -/
theorem occursN_args_congr_false :
    ¬ ∀ (env : VEnv) (N : VNestedOcc) (as : List VExpr),
        N.OccursN env → as.length = N.decl.np →
        ({ N with args := as } : VNestedOcc).OccursN env := by
  obtain ⟨env₁, h⟩ := listDecl_env_exists
  intro H
  exact (listOccBadSpine_not_occursN h).2 (H env₁ listOcc _ (listOcc_occursN h) rfl)

/-- …and the typing refutation of §4.1, unconditional in the environment too (it still needs
`Ordered`, which is what `VEnv.IsDefEq.constsIn` consumes and which no one has proved at this
witness — see `Theory/Typing/ConstSubstNested.lean`:789). -/
theorem pfnOcc_args_not_constsIn' :
    ∃ env₂, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      ¬ ∀ a ∈ pfnOcc.args, VExpr.ConstsIn a env₂.contains := by
  obtain ⟨env₂, h⟩ := pfnDecl_env_exists
  exact ⟨env₂, h, pfnOcc_args_not_constsIn h⟩

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.listDecl_env_exists
#print axioms Lean4Lean.InductiveDeclExamples.occursN_args_congr_false
#print axioms Lean4Lean.InductiveDeclExamples.pfnOcc_args_not_constsIn'

/-! ### §6.3 The edit, spelled out

**Step 0 — module order.**  `IsNestedName` is defined at `Verify/Inductive/NestedRestore.lean`:211
and `VExpr.NoConstIn` at :65 (with `decNoConstIn` at :96 and `noConstIn_bvars` at :86), and
`Verify/Inductive/NestedRestore.lean` transitively imports
`Theory/Inductive/NestedBuild.lean` (measured: 138 modules in its import closure, `NestedBuild`
among them).  So the clause cannot be written in `NestedBuild.lean` as it stands — that is a
cycle.  Move these four declarations into a `Theory/` module that `NestedBuild.lean` imports
(nothing under `Theory/` uses `NoConstIn` today, measured, so the move is free), and leave
`export`s behind at the old site.

**Step 1 — the new structure**, in `Theory/Inductive/NestedBuild.lean` right after `Occurs`
(namespace `Lean4Lean.VNestedOcc`):

    structure OccursN (N : VNestedOcc) (env : VEnv) : Prop extends N.Occurs env where
      args_noNested : ∀ a ∈ N.args, a.NoConstIn IsNestedName

**Step 2 — `Built`**: change `VInductDecl'.Built.occurs`
(`Theory/Inductive/NestedBuild.lean`:690) from

    occurs : ∀ j T, D.types[j]? = some T → T.name ∈ K → (occ j).Occurs env

to `… → (occ j).OccursN env`.

`Built.fields_noK` (`NestedBuild.lean`:717, and its twin on `BuiltFresh` at :732) then becomes
**derivable but not free**: §1.3's `OccursN.fields_noK` needs, besides the new clause,
`env.ConstsClosedC`, `∀ n ∈ K, ¬ env.contains n` and `∀ n ∈ K, IsNestedName n` — and `Built`
carries none of the three.  So the honest accounting is *not* "delete `fields_noK`": it is
"`fields_noK` can be dropped from `Built` at the price of moving those three environment
premises to `Built`'s consumers", and whether that is a win depends on whether they already have
them.  Measured: the six `Built`-building sites all already have the `addInduct'` hypothesis the
first two come from (`pfnEnv_constsClosedC`, `nfnK_not_contains`), and the third is
`RestoreData.isNestedName_of_mem`.  Do **not** bundle this with Step 2; sequence it separately.

**Step 3 — the construction sites.**  Four build an `Occurs` directly; each needs one line:

| site | new field |
| --- | --- |
| `Theory/Inductive/NestedBuild.lean`:1304 `listOcc_occurs` | `args_noNested := by decide` |
| `Theory/Inductive/NestedBuild.lean`:1813 `pfnOcc_occurs` | `args_noNested := by decide` |
| `Theory/Inductive/MemberRedex.lean`:1034 `qnOcc_occurs` | `args_noNested := by decide` |
| `Theory/Inductive/NestedFresh.lean`:91 `occurs_args_congr` | **leave at `Occurs`** (§6.2) |

The six `Built`-building sites (`NestedBuild.lean`:1353, :1861, `MemberRedex.lean`:1082,
`RestoreBridge.lean`:941, `NestedOccData.lean`:567, `NestedRestoreWit.lean`:668) all read
`occurs := fun _ _ _ _ => …_occurs h`, so they need no change beyond the renamed producer; the two
that thread it (`NestedOccData.lean`:451, `NestedRestoreWit.lean`:572) forward `hres.occurs` and
need the residue bundle's field retyped to `OccursN`.

**Step 4 — the consumers of `Built.occurs` that only want `Occurs`** call `.toOccurs`.
`VInductDecl'.Built.toFaithful` (`NestedBuild.lean`:1000-ish) is the main one.

**Step 5 — `RestoreData`.**  `args` (`Verify/Inductive/NestedRestore.lean`:490) stays as it is;
§1.2's `args_of_occursN` is its producer and §5 exercises it.  Optional narrowing, and a separate
finding: `args` quantifies over **all** `j : Nat`, but its only two consumers
(`mkRestore_nestedBarrier.resArgs`, `NestedRestore.lean`:739-742, and `spine_noConsts`,
`SpineTransfer.lean`:122) read it only at `types.length ≤ j`.  At `j < types.length`
`mkRestore.tyArgs j` is `VExpr.bvars 0 np` and `as j` is never looked at, so those instances are
dead weight.  Narrowing `args` to `∀ j, types.length ≤ j → ∀ a ∈ tyArgs j, …` would drop `hcases`
from §1.2 down to `∀ j, types.length ≤ j → Comp j ∨ as j = []`. -/
