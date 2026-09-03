# Handoff — a spine clause for `VNestedOcc.Occurs`, and the refutation of the *typing* shape

File owned and delivered: `Lean4Lean/Theory/Inductive/OccArgsTyping.lean`.
Builds green (`lake build Lean4Lean.Theory.Inductive.OccArgsTyping`, 171 jobs), every declaration
sorry-free — measured, `#print axioms` on all 21 headline results is `[propext, Quot.sound]` or
that plus `Classical.choice` (from `simp [nfnAux]` and from `NestedRestoreWit`'s own bundle).
**No inherited `sorryAx`**: the file deliberately does not import `TrProj.wf`'s hole, and takes
`env₂.Ordered` as a hypothesis rather than deriving it.

Outcome delivered: **2 plus 3**. The clause is proved against a copy of the strengthened `Occurs`
(`VNestedOcc.OccursN`, defined by `extends`, so the collapse is an `Iff` with nothing hidden),
`RestoreData.args` is discharged from it with zero `Expr`-side reasoning, the whole
`RestoreData` bundle is rebuilt at the tree's witness with `args` coming from the clause, and the
brief's requested shape — a **typing** clause — is refuted.

## 1. Where the brief is wrong

Four corrections, in descending importance.

### 1.1 A typing clause is satisfiable at no environment of the step (§4)

`Occurs env` is stated at the environment *before* the block being declared goes in. The nested
spine `N.args` is `Ds`, the arguments of the nested occurrence, and those name **the block being
declared**. Measured at both witnesses in the tree, not read off:

* `listOcc.args = [.app (.const ``NTree [.param 0]) (.bvar 0)]`, and `listOcc.Occurs env₁` with
  `env₁ = VEnv.empty.addInduct' listDecl`. `NTree ∉ env₁`.
* `pfnOcc.args = [.const ``NFn []]`, and `pfnOcc.Occurs env₂` with
  `env₂ = VEnv.empty.addInduct' pfnDecl`. `NFn ∉ env₂`.

So `∀ a ∈ N.args, VExpr.WF env U Γ a` is **refutable** at both. `pfnOcc_args_not_constsIn` and
`listOcc_args_not_constsIn` refute the far weaker `ConstsIn env.contains` with **no** `Ordered`,
no `OnCtx`, no `VEnv.WF` — so every typing spelling dies at once; `pfnOcc_args_not_wf` spells out
the typing instance for every `U` and every admissible `Γ`. This is `docs/vacuity-ledger.md`
rows 6 and 11 in the shape the brief warned about, and the brief's own asked-for clause walks
into it.

Restating the clause at the **post**-step environment does not rescue it, and this is the second
trap. The existing typing-route producer is
`ElimNestedInductive.Result.args_of_wf` (`Verify/Inductive/ProjNoNested.lean`:581), whose other
premise is `VEnv.NoNestedN env` — no declared name carries the `_nested` prefix. The post-step
environment declares the **companions**, whose names are exactly the reserved ones, so
`NoNestedN` is false there: `noNestedN_false_of_companion` (general) and
`nfnAux_post_not_noNestedN` (at `nfnAux`, whose second member is `_nested.PFn_1`).
`args_of_wf_unusable_at_step` states the conjunction: pre-step fails `hwf`, post-step fails
`hnn`, and a nested occurrence exists exactly when there is a companion.

**Conclusion: the clause must be environment-free.** That is what §1 delivers.

### 1.2 The clause must NOT go on `Occurs` — it makes a proved anti-vacuity control false (§6.1–§6.2)

`Theory/Inductive/NestedFresh.lean`:91 `VNestedOcc.occurs_args_congr` proves "`Occurs` cannot see
the spine", and :117/:138 use it for the separating pair `fields_noK_needs_spine`, which is the
tree's proof that `fields_noK` is *not* a consequence of `Occurs`. `listOccBadSpine`'s spine is
`[_nested.List_1 α]`, so the new clause fails of it. Hence:

* `listOccBadSpine_not_occursN` — same `Occurs env₁`, `OccursN env₁` fails;
* `occursN_args_congr_false` — the strengthened `occurs_args_congr` is **false**, unconditionally
  (the witness environment is `rfl`, via `listDecl_env_exists`).

So putting the field inside `Occurs` would turn a currently-proved control into a false statement.
The clause belongs on an **extension**; `Built.occurs` threads `OccursN`, `Occurs` is left alone.
The ripple is the same size either way (§6.3), so this is free.

### 1.3 The relayed discharge site `Verify/Inductive/Add.lean:1121` is wrong

`RestoreData` is **never constructed anywhere in `Verify/Inductive/Add.lean`** — absence claim,
scoped: searched for the string `RestoreData` across the whole of `Lean4Lean/` (`grep -rn`), and
for `RestoreData`'s definition site `Verify/Inductive/NestedRestore.lean`:460. `Add.lean:1121`
is inside `M.WF.field_step`, an unrelated R6 lemma. The two real construction sites are
`Verify/Inductive/NestedRestoreWit.lean`:188 (`nfnResult_restoreData`) and :274
(`nfnResultBadHead`), plus `Verify/Inductive/NestedOccData.lean`:734.

The two relayed *line* facts do check out: `RestoreData.args` is at
`Verify/Inductive/NestedRestore.lean`:490, and `fields_noK_of_occurs` is at
`Theory/Inductive/NestedBuild.lean`:961. The brief's guess about `Occurs`'s home was half right:
`NestedBuild.lean`:648, not `Decl.lean`.

### 1.4 Two producers for `RestoreData.args` already existed

The brief presented this as open. Measured: `ElimNestedInductive.Result.args_of_gate` /
`args_of_source` (`Verify/Inductive/SpineTransfer.lean`:502-515, from the `checkNoNestedAux`
gate plus `htr` plus `hproj`) and `args_of_wf` (`ProjNoNested.lean`:581, the typing route §1.1
refutes). The contribution here is a **third**, which needs none of `Expr`, `TrExprS`, the gate,
`hproj`, or an environment invariant.

## 2. What is proved

Namespaces read off the file's own `namespace` lines, not from the path.

| result | statement |
| --- | --- |
| `Lean4Lean.VNestedOcc.OccursN` | `Occurs` + `args_noNested : ∀ a ∈ N.args, a.NoConstIn IsNestedName` |
| `…VNestedOcc.occursN_iff` | collapse test: `OccursN env ↔ Occurs env ∧ clause` — exact, nothing hidden |
| `…VNestedOcc.args_of_occursN` | **the discharge**, in the literal shape of `RestoreData.args` |
| `…VNestedOcc.args_of_occursN'` | the same from one hypothesis, no auxiliary predicate |
| `…VNestedOcc.OccursN.args_noConsts` | the clause also supplies `fields_noK_of_occurs`'s `hargs` |
| `…VNestedOcc.OccursN.fields_noK` | …hence `Built.fields_noK`'s body with no spine premise left |
| `…InductiveDeclExamples.listOcc_occursN`, `pfnOcc_occursN` | **inhabited**, at `env₁` / `env₂`, clause by `decide` |
| `…InductiveDeclExamples.occursN_inhabited` | `∃ N, N.OccursN env₂ ∧ N.args ≠ []` — non-degenerate |
| `…InductiveDeclExamples.occursN_proper` | **negative control**: separating pair, `Occurs` agrees, `OccursN` splits |
| `…InductiveDeclExamples.pfnOcc_args_not_constsIn`, `…_not_wf`, `listOcc_args_not_constsIn` | §1.1's refutation |
| `…InductiveDeclExamples.args_of_wf_unusable_at_step` | both `args_of_wf` premises, jointly unsatisfiable |
| `…InductiveDeclExamples.occursN_args_congr_false` | §1.2's induced refutation, unconditional |
| `…NestedWit.nfnAs_args_of_occursN` | `RestoreData.args` at the witness, from the clause |
| `…NestedWit.nfnResult_restoreData_of_occursN` | the **whole bundle** rebuilt with that field |
| `…NestedWit.nfnAs_noK_of_occursN` | …and it still flows into `Built` via `spine_noConsts` |

Anti-vacuity checklist, per the brief:

* **Environment stated**: the clause is at *no* environment — it is a predicate on `Name` only.
  That is the finding, not an evasion; §4 is the proof that every environment-indexed spelling
  fails at one end of the step.
* **Inhabited**: two witnesses at two named environments, plus an `∃`-form; both environments
  proved to exist outright (`listDecl_env_exists`, `pfnDecl_env_exists`, both `rfl`).
* **Hypotheses discharged or inhabited**: `args_of_occursN`'s `hcases` is discharged at the
  witness (`nfnAs_cases`); `hagree` is `rfl` (`nfnAs_eq_pfnOcc_args`); `env₂.Ordered` in §4.1 is
  carried, not proved, and is *not* what fails there — flagged in the docstring.
* **Negative control**: `occursN_proper` and `pfnOccBadSpine_not_occursN`. The control is sharp:
  it shows `Occurs` is *exactly* silent about the spine's constants, so no amount of environment
  reasoning recovers the clause.
* **Parameters quantified**: `env`, `N`, `K`, `as`, `occ`, `Comp`, `U`, `Γ` are all universally
  quantified in §1 and §4's general lemmas. Fixed only at the witnesses (`listDecl`/`pfnDecl`,
  `nfnAux`, `nfnAs`, `nfnResult`), and those are the tree's own.

## 3. The exact edit (§6.3 of the file has it in full)

**Step 0 is a module-order move and is not optional.** `IsNestedName`
(`Verify/Inductive/NestedRestore.lean`:211) and `VExpr.NoConstIn` (:65, with `decNoConstIn` at
:96 and `noConstIn_bvars` at :86) live in `Verify/`, and
`Verify/Inductive/NestedRestore.lean` transitively imports `Theory/Inductive/NestedBuild.lean`
(measured: 138 modules in the closure, `NestedBuild` among them). Writing the clause in
`NestedBuild.lean` as things stand is a **cycle**. Move those four declarations into a `Theory/`
module `NestedBuild.lean` imports — nothing under `Theory/` uses `NoConstIn` today (measured,
`grep -rn NoConstIn Lean4Lean/Theory/`), so the move is free — and leave `export`s behind.

Then: add `OccursN` next to `Occurs`; retype `Built.occurs` (`NestedBuild.lean`:690) to
`OccursN`; add `args_noNested := by decide` at the three direct `Occurs` builders
(`NestedBuild.lean`:1304 `listOcc_occurs`, :1813 `pfnOcc_occurs`,
`MemberRedex.lean`:1034 `qnOcc_occurs` — `qnOcc.args = [.const ``QN []]`, clean, measured);
leave `NestedFresh.lean`:91 `occurs_args_congr` at `Occurs`. Six `Built`-building sites and two
forwarding sites are listed with line numbers in §6.3. `Built.fields_noK`'s deletion is
*derivable but not free* (three environment premises `Built` does not carry) — sequence it
separately; the file's §6.3 Step 2 spells out why.

## 4. Where I did not get all the way

* **`RestoreData.args` in general, not at the witness.** §5 discharges it at `nfnResult`/`nfnAs`
  only. A general discharge needs `Built.tyArgs` (which is `hagree`) plus a general `hcases`, and
  `hcases` is not derivable from anything: `RestoreData.args` quantifies over **all** `j : Nat`,
  including `j` past `r.types.length`, where `as j` is unconstrained junk the caller picks.
  Separate finding, §6.3 Step 5: `args`'s only two consumers
  (`mkRestore_nestedBarrier.resArgs`, `NestedRestore.lean`:739-742, and `spine_noConsts`,
  `SpineTransfer.lean`:122) read it **only** at `types.length ≤ j`; at `j < types.length`
  `mkRestore.tyArgs j` is `VExpr.bvars 0 np` and `as j` is never looked at, so those instances
  are dead weight. Narrowing `args` to `∀ j, types.length ≤ j → …` is an edit to
  `Verify/Inductive/NestedRestore.lean`, which this round did not own.
* **The cost of §5 is real and recorded**: the old `args` proof was `decide` and mentioned no
  environment; the new one carries `VEnv.empty.addInduct' pfnDecl = some env₂`, because the
  occurrence record does. Same trade `nfnAux_builtFresh` (`NestedBuild.lean`:1854) took when
  `fields_noK` moved from `decide` to the producer. Every downstream consumer at this witness
  already carries `h`, measured.
* **`env₂.Ordered`** in §4.1's typing refutation is a hypothesis. `Theory/Inductive/Lemmas.lean`:1364
  gives `addInduct'` preserves `Ordered` modulo two obligations, and
  `Theory/Typing/ConstSubstNested.lean`:789 records that nobody has proved it at this witness. It
  is not what fails in the refutation — the `ConstsIn` form (`pfnOcc_args_not_constsIn`) needs
  none of it.

## 5. Pick up first

1. Decide `Occurs` + field vs. `OccursN` extension. The file argues for the extension and proves
   what the mutation breaks (`occursN_args_congr_false`). If you take the mutation anyway,
   `NestedFresh.lean`:117 and :138 have to be restated at a predicate that is not `Occurs`.
2. Step 0's move of `IsNestedName` / `VExpr.NoConstIn` into `Theory/`. Nothing else can land
   until it does, and it is a pure relocation of four declarations.
3. Then `Built.occurs : … → OccursN env`, and the three `by decide` lines.
4. Independently: narrow `RestoreData.args` to `types.length ≤ j`. That removes the only
   non-occurrence hypothesis from §1.2's discharge and makes it general rather than
   witness-bound.
