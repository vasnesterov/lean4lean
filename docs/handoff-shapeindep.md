# Handoff: `ShapeIndep` — the variable entries are a **rename**

Round 12 of the `PiDescend` line.  One question, taken from `docs/handoff-spinevar.md` §1.3 and §4.1,
which flagged it as the highest-value open item of round 11:

> Do `SpineVarPiDisj`, `SpineVarSortDisj` and `SpineVarAppDisj` follow from `RigidShapeUniq`?  If
> they did, the extension would be a **rename**, not a localisation.

## 0. Verdict

**They do.  Both variable entries — `ShapeVar.lean`'s bare variable and `SpineVar.lean`'s variable
spine — are a relabelling of facts the corner already had.**  Round 11 said out loud that this was
the question that would downgrade it, and the answer is the downgrade.

| row | what it is | status |
| --- | --- | --- |
| `SpineVarPiDisj` (var spine ≉ Π) | `RigidConstPiDisj`, conjunct 2 of `rigidShapeUniqNS_iff_family` | **theorem**, `rows12_theorem` |
| `SpineVarSortDisj` (var spine ≉ sort) | `RigidConstSortDisj`, conjunct 5 | **theorem**, `rows12_theorem` |
| `SpineVarAppDisj` (var spine ≉ const spine) | `VEnv.ConstNoConf` (`Verify/Typing/Rigidity.lean`) | **theorem in its `IsType`-guarded form**; the `¬ IsProof` form is the one new thing here |
| `ShapeVar.VarPiDisj`, `.VarSortDisj` | the empty-spine instances of the first two | **theorem**, `varRows_theorem` |

Consequences, both machine-checked:

* `piDescend_iff_neutralNVS_sortConv'` — `SpineVar.lean` §5's row deletion needs **no hypothesis**.
* `piDescend_iff_neutralNV_sortConv'` — nor does `ShapeVar.lean` §6's.

So the two rounds bought vocabulary and a consumer-side convenience, not strength, and the entry
`SpineVar.lean` §9 proposes putting into `RigidShape` itself (86 mentions, 9 eliminators) buys
nothing that the transport below does not already give.  **Do not sequence that edit on the strength
of these rows.**

## 1. Why there is no separating witness, and why the question had to be re-read

The brief's outcome 1 asked for a `VEnv.WF` environment satisfying `RigidShapeUniq` and violating a
row.  No such object can be exhibited, and the reason is not difficulty:

`ShapeIndep.rowsFromBridge_iff_rows` proves

    (∀ env U, WF env → RigidShapeUniq env U → rows)  ↔  (∀ env U, WF env → rows)

outright.  `Injectivity.WF.rigidShapeUniq` asserts the bridge at *every* `VEnv.WF` environment, so
over `VEnv.WF` "follows from `RigidShapeUniq`" and "is a theorem" are the **same predicate**: the
hypothesis is inert.  A `VEnv.WF` separating witness would therefore refute
`WF.rigidShapeUniqNS`, and a non-`WF` one would have to *prove* `RigidShapeUniq` at a concrete
environment — which nothing in this tree does at **any** environment, `VEnv.empty` included
(checked: the only route to `RigidShapeUniq` in the compiled tree is `WF.rigidShapeUniq`, i.e. via
`WF`).

That is a defect in the *framing* used to grade this corner's last two rounds, not just in the
brief: any statement true of well-formed environments "follows from `RigidShapeUniq`" in the
fixed-environment reading.  Grading a shape entry as *localisation* on that reading is therefore
never falsifiable.  The reading that has content is the derivability one, and §2 answers it.

## 2. Method: one variable becomes one axiom

`Theory/Typing/ConstVar.lean` transports a judgement over `env.addConst c ci` **down** to `env` in a
context extended by `ci.type` — constant to variable — and pays about 200 lines for a substitution
`cvar` and its commutation lemmas.  The direction needed here is the other one, and it is much
cheaper, because it needs no substitution function at all:

* the **outermost** entry of an `OnCtx` context is typed in the empty context, hence closed and
  level-well-formed, hence a legal axiom type;
* `env.addConst c ⟨U, T⟩` is then well formed, and `.const c (VLevel.params U)` inhabits `T` there
  (`LevelWF.instL_id` cancels the `instL`);
* so `IsDefEq.instN` — one existing lemma — replaces `.bvar Γ₀.length` by that constant and shortens
  the context by one.

That is `VEnv.axiomize_step` (`ShapeIndepStep.lean`).  Iterating it (induction on the context
*length*) either turns the spine head into the fresh constant — and then the **constant** row fires —
or reaches `Γ = []`, where every variable-headed row is already a theorem (`SpineVar.lean` §7.1).
Both branches are exercised at witnesses (§4 below).

Three facts make the step cheap and are worth remembering:

1. `VExpr.spineHead_inst : (e.inst e₀ k).spineHead = (e.spineHead.inst e₀ k).spineHead` — one
   `rfl`-induction.  The extra `spineHead` on the right is not slack: `instVar` can put an
   *application* where a variable was, so the naive equation is false.
2. `Ctx.InstN` at `Γ₀ = []` is exactly "substitute for the outermost variable"; no new context
   relation was needed.
3. An **undeclared** constant heads no rule (`ruleFreeHead_of_not_contains`, from
   `Ordered.constsInD`), so the fresh axiom satisfies `RuleFreeHead` for free — which is what lets
   the constant rows, all guarded by `RuleFreeHead`, be applied at all.

### 2.1 `VEnv.FreshNames` is a theorem, not a side condition

The first draft carried freshness as a hypothesis and asserted in a docstring that no "names added"
bound existed for `VDecl.WF`'s arms.  **That was wrong.**  `addInduct'`, the arm that looked worst,
already has one (`VEnv.addInduct'_constants_of_not_mem`, `Theory/Inductive/Lemmas.lean`), and the
rest are `addConst`, `addConsts`, `addQuot` and the identity.  `ShapeIndepFresh.lean` proves

* `Name.exists_not_mem` — `Name` is infinite, by a component-count measure (no pigeonhole);
* `WF.constantsBounded` — a `VEnv.WF` environment's constants are confined to a finite list, one
  clause per arm;
* `VEnv.freshNames : FreshNames` — hole-free.

So the verdict has **no** freshness side condition.

## 3. The one thing that is genuinely new: a guard, not a shape

Row 3 reduces to constant no-confusion for **distinct** rule-free heads.  Two things about that:

* `RigidShape.Compat`'s `app`/`app` entry is guarded by `c = c'`, so `RigidShapeUniq` says nothing
  there (`rigidShapeUniq_says_nothing_distinct`).  `RigidShapeVS.Compat` declines the same fact at
  the corresponding entry — its `varApp`/`varApp` diagonal is `True`
  (`rigidShapeVSUniq_says_nothing_distinct`).  The two vocabularies decline no-confusion in
  matching places, which is a coherence check on the translation.
* But the fact **is already in the tree**, named, with the *same guards* I arrived at
  independently: `VEnv.ConstNoConf` (`Verify/Typing/Rigidity.lean:151`), described there as "the
  fourth fact of `Theory/Typing/Injectivity.lean`'s taxonomy, which that file declines to state
  because no consumer has asked for it".  Machine-checked in a scratch probe (`/tmp`, importing both
  layers — **not** a tree file, since `Theory` may not import `Verify`):

      rigidConstNoConf_iff_constNoConf : env.RigidConstNoConf U ↔ env.ConstNoConf U   -- hole-free
      spineVarAppDisjT_via_constNoConf : ∀ env, env.WF → env.SpineVarAppDisjT U       -- via constNoConf_of_wf

  So row 3 is a theorem too, via `constNoConf_of_wf → patWF_of_wf → IsDefEq.church_rosser`.  That
  route is the one `RigidNodeCircle.lean` marks **circular** for discharging the bridge; it is not
  circular for *this* use, because nothing here feeds back into the bridge, but a reader should know
  the row's only supply runs through `church_rosser`, whose own statement is refuted at the
  K-canonical instance (`KCanonical.not_crStatement_of_kstep`).

**The guard gap, stated precisely.**  What is reduced is `SpineVarAppDisjT` — row 3 with `¬ IsProof`
replaced by `IsType` — not `SpineVarAppDisj` as `SpineVar.lean` states it.  The translation pushes
judgements *up*, so it moves `IsProof` forwards and `¬ IsProof` backwards; turning that round is
`ConstVar.axiomConservativityWF_iff_target`, i.e. the strengthening target, an open node.  And the
tree's own `ConstNoConf` uses `IsType` too, so **nothing in the tree has the `¬ IsProof` form of
constant no-confusion**.  That is the single residue of two rounds of variable entries, and it is a
statement about a guard, not about variables.

## 4. Anti-vacuity

Per `docs/vacuity-ledger.md` §0, in order.

* **Midpoint restriction? No, structurally.**  Nothing here opens a conversion derivation.  §2 and §3
  are substitutions, and substitution acts on the two **endpoints** of `IsDefEqU`; `IsDefEq.instN` is
  proved over the whole derivation and imposes no condition on any midpoint.  The recursion is on
  the **length of the context**.  So this is not the twelfth collapse, and not by a read-off.
* **Both branches of the transport fire.**  `axiomize_step_fires`: at `VEnv.empty` with context
  `[Prop]` — where every name is fresh by `rfl` — the step runs, produces a `WF` environment above
  `VEnv.empty` with a typed rule-free axiom, shrinks the context to `[]`, and turns `.bvar 0` into
  that **constant** (the branch where only the constant row closes the goal).
  `axiomize_step_recurses` exercises the other branch (`0 < 1`, spine head stays a variable).
* **The reduced row's guard set is inhabited**, at a **non-empty** spine:
  `spineVarAppDisjT_guards_inhabited` gives all five premises of `SpineVarAppDisjT` at once over
  `svEnv`, in `SpineVar.lean` §7.2's three-entry context, at the type `.app (.bvar 2) (.bvar 1)`.
  Uses `empty_le_svEnv` to move §7.2's witnesses across.
* **Refutation attempts on the two new definitions**, in `ShapeIndep.lean` §5.3.  `RigidConstNoConf`:
  δ blocked by `RuleFreeHead` on both heads, proof irrelevance blocked by the `IsType` guard (via
  `IsType.not_isProof`, which is in the tree but **tainted** — so that half is a blocked-mechanism
  claim resting on a tainted lemma, not a theorem here).  Not refuted.  `SpineVarAppDisjT`: implied
  by the row `SpineVar.lean` states, so it cannot be stronger; §5.2 shows it is not empty.
* **Inhabitation and hole-freeness, stated separately** (below).  Note that `svEnv` is
  **inconsistent** (`SpineVarVacuity.svEnv_every_prop_inhabited`); the guard-inhabitation statement
  is a conjunction of premises, not a refutation, so that neither helps nor hurts it — but it is
  disclosed here rather than left to the reader.

## 5. Where earlier work — mine included — was wrong

1. **Expressibility was the wrong signal.**  `spineVar_grade`'s conjuncts 3 and 4 (no `RigidShape`,
   no `RigidShapeV` denotes a non-empty variable spine) were offered in `docs/handoff-spinevar.md`
   §1.3 as making derivability "look unlikely".  They are irrelevant to it: the derivation changes
   the **environment**, not the vocabulary.  A statement can be inexpressible in a vocabulary at a
   fixed environment and still be a theorem, and here it is one.  Anyone grading a future shape entry
   should not count inexpressibility as evidence of strength.
2. **`docs/handoff-spinevar.md` §4.1** describes the settling witness as "a `VEnv.WF` environment
   satisfying `RigidShapeUniq` and violating one of the three rows".  Such an object refutes
   `WF.rigidShapeUniqNS`; the item was not cheap-to-state, it was unstatable-as-a-target.
3. **`SpineVar.lean` §4's docstring** — "a refutation would be a refutation of the injectivity
   corner's *shared* node, not of my entry" — is right, and is now the *whole* story rather than a
   caveat: §5.4 of `ShapeIndep.lean` says the same thing in the forward direction.
4. **My own draft of §4** claimed the `SortUniq`/`ProofTransport` tax on the constant rows was
   avoidable off the full `RigidShapeUniq`, because the middle term can be taken to be the constant
   spine and `not_isProof_of_defeqU_forallE` then discharges `¬ IsProof` from `VEnv.WF` alone.  The
   route compiles and is **tainted**: that lemma goes through `WF.sortUniq'` and `IsProof.defeqU`,
   both `sorryAx`, whereas `RigidNodeCircle`'s `not_isProof_of_forallE'` is hole-free *because* it
   takes the two nodes as hypotheses.  Measured, then corrected in the file.  The tax buys the
   hole-freeness; it is not overhead.
5. **My own `ShapeIndepStep.lean` docstring** claimed no "names added" bound existed — false, and it
   would have left the verdict conditional for no reason.  §2.1.
6. **Duplicate name caught**: my `nameDepth` collided with
   `Verify/Inductive/NestedOccData.nameDepth` (a different function).  Renamed to `nameParts`; the
   collision showed up as a census crash (`environment already contains …_unsafe_rec`), not as a
   build failure, which is worth knowing — `lake build` of my own modules was green throughout.

## 6. Measurements

* `lake build` of the three new modules: **110 jobs**, green.
* `lake env lean --run scripts/sorry-census-all.lean`: **13 holes**, unchanged — this round adds
  none.  `on disk: 423; population: 399; BUILT: 399; NOT BUILT: 0` (round 11's two `CtorBeta`
  stragglers are gone).  Pass A 396, pass B 3.  35 orphan modules; the three new files are leaves.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` → **empty**.
* Frozen files `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`: not read for edit,
  not edited, not `touch`ed.  `SpineVar*.lean`, `ShapeVar.lean`, `Injectivity.lean`,
  `InjOneFact.lean`, `RigidNodeCircle.lean`: **unmodified** (only imported).
* Cones (`scripts/hole-cone.lean` re-seeded, `allowOpaque := true`, `Theory.Typing.ShapeIndep` added
  to the import list):

| seed | cone | holes in cone |
| --- | --- | --- |
| `VExpr.spineHead_inst` | 391 | none |
| `spineVarAppDisjT_guards_inhabited` | 871 | none |
| `WF.constantsBounded` | 1068 | none |
| `freshNames` | 1090 | none |
| `axiomize_step` | 3288 | none |
| `axiomize_step_fires` | 3297 | none |
| `spineVarPiDisj_of_constPiDisj` | 3349 | none |
| `spineVarSortDisj_of_constSortDisj` | 3349 | none |
| `spineVarAppDisjT_of_constNoConf` | 3353 | none |
| `rows12_of_rigidShapeUniqNS_all` | 3510 | none |
| `rigidShapeVSUniq_of_bridge_all_and_row3` | 3543 | none |
| `rowsFromBridge_iff_rows` | 3482 | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |
| `rows12_theorem` | 3685 | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |
| `rigidShapeVSUniq_iff` (round 11's) | 3705 | `forallE_inv_stratified` |
| `piDescend_iff_neutralNVS_sortConv` (round 11's) | 3735 | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |
| `piDescend_iff_neutralNVS_sortConv'` (mine) | 3896 | `forallE_inv_stratified`, `WF.rigidShapeUniqNS` |

  Read the last two rows together: internalising the row costs 161 constants of cone and **no new
  hole**.  Read the top block: every *reduction* is hole-free, because in each the nodes are
  hypotheses.  **Hole-freeness is not discharge** — `rows12_theorem` is the discharged form and it
  carries both of the corner's holes, exactly as `WF.rigidShapeUniqNS` does.

## 7. What to pick up first

1. **The `¬ IsProof` form of constant no-confusion.**  It is the entire residue of rounds 10-12, it
   is a statement about a guard, and nothing in the tree has it — `Verify/Typing/Rigidity.ConstNoConf`
   and `RigidNodeCircle.RigidConstAppInv` sit on opposite sides of the guard (`IsType` vs
   `¬ IsProof`), so someone should check whether the `¬ IsProof` no-confusion row is even **true**;
   `Theory/Typing/ConstInvWitness.lean` is where dropping the guards is known to prove `False`, and
   is the right place to look for a refutation.
2. **`SpineVar.lean` §9's in-place `RigidShape` edit: do not sequence it** on these rows' account.
   If a variable entry is wanted for *ergonomics* that is a separate case, and it should be argued as
   ergonomics.
3. **`axiomize_step` is reusable and nobody else has it.**  Any row in this tree about a
   *variable*-headed term reduces to the same row about a constant-headed one, at a one-axiom
   extension, in about ten lines.  Candidates: the remaining slices of `PiCodLiftNeutralNVS`
   (`spineHead_cases_of_noSpineVar` names them), and anything in the `Strengthen*` family whose
   statement quantifies over a context variable.
4. **`ConstantsBounded` may be worth moving upstream.**  It is a general fact about `VEnv.WF` that
   several files could have used (`StrengthenAxiom.lean`'s freshness hypotheses, `ConstVar.lean`'s
   `addConst … = some env'` premises); it currently lives in a leaf file of this corner.
