# Handoff: the eleventh field through `instN`, `instL`, `defeqDFC` (and the `weak'_inv` verdict)

*Round of 2026-09-03, following `docs/handoff-trproj-wide.md`.  Two new modules only —
`Lean4Lean/Verify/Typing/TrProjWideTransport.lean` and
`Lean4Lean/Verify/Typing/TrProjWideTransportWitness.lean`.  **No existing file was edited.**
`Verify/Typing/Expr.lean` (`TrProj`'s definition) is untouched; the in-place edit of
`handoff-trproj-wide.md` §5 was **not** made.*

Every claim is tagged **[measured]** (an instrument was run this round, named at the claim) or
**[read off source]**.

---

## 0. Headline

**Outcome 1 for `instN` and `instL`; outcome 2 for `defeqDFC`, with the obstruction named and
priced; plus a measured verdict on `weak'_inv` that is an argument against option (d).**

| lemma | transports? | hypotheses it needs | cone | holes |
|---|---|---|---|---|
| `TrProjG.mono` (prior round) | yes, free | `env ≤ env'` | 1020 (narrow 1010) | **none** |
| `TrProjG.weak'` / `.weakN` (prior round) | yes | `VEnv.Ordered` + `Ctx.Lift'` / `Ctx.LiftN` | 3581 / 3582 (narrow 3263 / 3264) | **none** |
| **`TrProjG.instN`** | **yes, free** | `VEnv.Ordered env`, `Ctx.InstN`, `t₀ : HasType Γ₀ e₀ A₀` — **identical to `TrProj.instN`** | 2657 (narrow 2340) | **none** |
| **`TrProjG.instL`** | **yes, free, and cheapest of all** | `∀ l ∈ ls, l.WF U'` and **nothing else** — no `Ordered`, no `WF`, no `OnCtx`; identical to `TrProj.instL` | 1090 (narrow 1027) | **none** |
| **`TrProjG.defeqDFC`** | **yes, at the narrow signature, but NOT free** | `VEnv.WF env`, `IsDefEqCtx`, `IsDefEqU` — identical to `TrProj.defeqDFC` | 5289 (narrow 3497) | `{weakN_iff, forallE_inv_stratified}` (narrow: `{forallE_inv_stratified}`) |
| `TrProjG.defeqDFC_ten` (the same lemma minus the eleventh field) | — | same | 3490 | `{forallE_inv_stratified}` |

All figures **[measured]** this round, in a single `hole-cone`-style run over one import set
(`TrProjWideTransportWitness` + `Lemmas` + `ProjSpineCongr` + `ProjWeakInvSplit` +
`ProjWeakInv`); cone sizes depend on the import set, so figures from different runs are not
comparable and everything quoted here is from that one run.

**No new hole, nothing traded.**  Every hole anywhere in this round's output is one of
`VEnv.IsDefEqU.weakN_iff` / `VEnv.IsDefEqU.forallE_inv_stratified` — wall 2's own two, which are
also the *narrow* `projTerm_hasType`'s own two.  Nothing gained a hole the tree did not already
have.  **[measured]**

Full `lake build`: **1548 jobs, exit 0**.  Guards unchanged: guard 1 `24 frozen axioms ✓`,
guard 2 `within whitelist ✓ (proof INCOMPLETE: sorryAx present)`, guard 3 `2/2 ✓`.  **[measured]**

---

## 1. `instN` and `instL`: free, and the brief's guess was right

The brief guessed these "should go the same way as `weak'`".  They do, and the guess was
accurate to the line: both proofs are `TrProjG.weak'`'s proof with `lift'` replaced by `inst` /
`instL`, and the eleventh field's transport is the same three-step move —
`VExpr.inst_instAll` / `VExpr.instL_instAll` kills the operation on the *head* (the field type is
`ClosedN (D.np + i)` by `ProjClosedG.fields`), and `projTermG_instN` / `projTermG_instL` moves it
through every spine entry.  `instL` is the cheapest of the whole cluster: `projTermG_instL` is
unconditional and `VExpr.instL_instAll` needs no closedness, so the eleventh field costs a
`simpa`.  **[measured: both compile hole-free at the narrow lemmas' exact signatures.]**

**Neither needs `VEnv.WF`.**  This is the measurement the brief asked not to round up, so it is
stated flat: `TrProjG.instN` needs `VEnv.Ordered env`, and `TrProjG.instL` needs **no environment
hypothesis at all**.  `VEnv.WF` occurs in these two nowhere.

---

## 2. `defeqDFC`: transports at the narrow signature, and pays `weakN_iff` for it

**This is the one place option (d) costs something in the structural cluster, and the cost is
exactly identified.**

`weak'`, `instN`, `instL` all apply one syntactic operation uniformly to subject, spine and type,
so the transported `HasType` *is* the eleventh field wanted.  `defeqDFC` changes the **major
premise**, `e₁ → e₂`, and the eleventh field's *type* mentions the earlier projections of the
major premise — so `HasType.defeqDFC` delivers the field at `e₁` while the constructor demands it
at `e₂`.  It has to be re-derived, and the only producer is `TrProjG.mk'`, i.e. wall 2.

* **Signature: unchanged.**  `mk'` wants `VEnv.WF env` (which `TrProj.defeqDFC` already takes
  verbatim) and `OnCtx Γ₂ (env.IsType U)` (which is already a line of the narrow proof,
  `(hΓ.symm henv.ordered).isType`).  So no consumer pays a new hypothesis.  **[measured]**
* **Hole set: grows by `weakN_iff`.**  Localised, not asserted: `TrProjG.defeqDFC_ten` — the same
  lemma with the eleventh field removed from the conclusion — has cone **3490** and holes
  `{forallE_inv_stratified}`, i.e. the narrow lemma's own cost to 7 nodes (narrow: 3497, same
  hole, which comes from `IsDefEqU.of_l` moving the subject).  Adding the eleventh field takes it
  to **5289** and `{weakN_iff, forallE_inv_stratified}`.  **[measured]**

### 2.1 The alternative route exists, is unpriced, and I got its absence wrong twice

Route 2 would avoid `mk'`: prove `projTermG … e₁ ≡ projTermG … e₂` and move the type along.  I
twice wrote in a docstring that this was blocked by an absent lemma.  **Both claims were false**,
and I record it because that is the ledger's kind-4 overstatement (an unproved negative that
stops people looking), produced twice in one afternoon by me.

* `VInductDecl'.projTerm_congr_subject` (`Verify/Typing/ProjSpineInv.lean:184`) is exactly the
  subject congruence, narrowly.  Cone 3497, holes `{forallE_inv_stratified}`.  **[measured]**
* `VEnv.IsDefEqU.instAllCongr` (`Verify/Typing/ProjSpineCongr.lean:26`) is the general
  `instAll b as ≡ instAll b as'` from `HasArgsDF`.  Cone 3519, holes
  `{forallE_inv_stratified}`.  **[measured]**

The first grep missed the second lemma; it was found by a **structural query** over the compiled
environment (every declaration whose conclusion head is `IsDefEq`/`IsDefEqU` and whose conclusion
mentions `VExpr.instAll`: 112 scanned, 19 hits).  That is the ledger's guard for kind-2
overstatement and it should have been the first instrument, not the third.

**So route 2 is live and unpriced, and it is interesting**: neither ingredient carries
`weakN_iff`, so it could plausibly give `defeqDFC` its narrow hole set back.  What it cannot do is
save a hypothesis (both take `VEnv.WF`).  What is unmeasured is its real cost: `instAllCongr`
wants `OnCtx (As.reverse ++ Γ)` and `HasType (As.reverse ++ Γ) b B` for the **field telescope**,
plus a `HasArgsDF` between the two projection spines — assembling those without re-entering
`projTermG_hasType` is an unbuilt module, not a rewrite of the existing proof.  **I did not
attempt it and I do not claim it works.**

---

## 3. Firing tests

`Lean4Lean/Verify/Typing/TrProjWideTransportWitness.lean`, on `MutField.declEnv_trProjG` — the
two-type mutual block at member `j = 1` where `VEnv.IsStructure` is outright false.

| firing | what it shows | cone | holes |
|---|---|---|---|
| `declEnv_trProjG` (input, prior round) | — | 6760 | `{weakN_iff, forallE_inv_stratified}` |
| `declEnv_trProjG_weakN` | `weakN` under a fresh `Type` variable | 6810 | the same two |
| `declEnv_trProjG_instN` | `instN` substituting `Prop` for it | 6817 | the same two |
| `declEnv_trProjG_instL` | `instL` at `ls = []` | 6782 | the same two |
| `declEnv_trProjG_defeqDFC_refl` | `defeqDFC` at reflexive context and defeq | 6771 | the same two |
| `declEnv_trProjG_defeqDFC_eta` | **`defeqDFC` at a subject that actually moves**: `x ⟶ B.mk x.f` | 6776 | the same two |

**Every firing inherits exactly the input derivation's two holes and adds none** (+7 to +57
nodes).  **[measured]**

### 3.1 The limits of these firings, stated rather than glossed

* `MutField.decl` has `uvars = 0`, `params = []`, `indices = []`, so at this derivation
  `us = ps = ιs = []`.  Therefore **`instL` at the only available `ls` is a no-op**, and the
  weaken-then-instantiate `instN` composite is a **round trip**.  They exercise every side
  condition of the transport — which is what a firing test is for — but they do not exhibit a new
  term.  The non-degenerate halves are fired elsewhere, on the term-level commutation these
  transports run on: `Rich.projTermG_instN_fires` and `Poly.projTermG_instL_fires`
  (`Verify/Typing/ProjGenInstWitness.lean:152, 251`), at `us = [.param 0]`, `ls = [.succ .zero]`
  and a non-empty parameter spine.
* **Absence claim, to the required standard.**  I did not find a `TrProjG` (or `TrProj`)
  derivation over a concrete environment with `uvars > 0`.  Searched for: derivations of
  `TrProj`/`TrProjG` at a named environment, over every `*.lean` under `Lean4Lean/`; the two that
  exist are `barEnv_TrProj` (`Verify/Typing/ProjWfWitness.lean`) and `MutField.declEnv_trProjG`
  (`Verify/Typing/TrProjWideWitness.lean`), and both have `uvars = 0`.  **[measured]**
* `declEnv_trProjG_defeqDFC_eta` is the non-degenerate one, and it carries **two** open
  hypotheses, both named: `VEnv.WF declEnv` (the tree's keystone, open for everybody) and
  `declEnv.StructEtaG`.  The latter is **inhabited somewhere** — `VEnv.empty.StructEtaG` is proved
  (`Verify/TypeChecker/EtaStructG.lean:339`) — and is **not** proved at `declEnv`; it is the eta
  rule as an environment assumption, exactly as `declEnv_structEtaG` itself takes it.  So it is
  not vacuous, and it is not discharged.

---

## 4. `weak'_inv`: **not** better positioned.  Worse by one hole, and that is a result

The brief asked for an honest measurement and said a widened version is not expected to be
hole-free.  The answer is sharper than "not better":

* **Input side, no gain.**  The widened hypothesis is strictly stronger — it hands you the
  target's typing in `Γ'` free (`TrProjG.wf`, cone 737, hole-free) where a narrow proof wanting
  it must call `TrProj.wf` (cone 5095, both holes).  But the *live* narrow route does not want
  it: `TrProj.weak'_inv_of_typing_head` has cone **3716**, holes
  `{forallE_inv_stratified, rigidShapeUniqNS}` — **no `weakN_iff`**, so it never calls
  `TrProj.wf`.  The free field pays for nothing that route was buying.  **[measured]**
* **Output side, strict loss.**  The widened conclusion needs an eleventh field **in the smaller
  context `Γ`**, and its only producer is `mk'`.  `TrProjG.weak'_inv_of_narrow` (the widened
  inversion from the narrow one) has cone **5319** and holes
  `{weakN_iff, forallE_inv_stratified}` — it re-imports precisely the hole
  `weak'_inv_of_typing_head` was engineered to avoid.  It also needs `OnCtx Γ`, the *smaller*
  context, which the headline `TrProj.weak'_inv` does not have (it takes `OnCtx Γ'`; recovering
  `OnCtx Γ` is `OnCtx.weak'_inv`, the single step Update 7 of that docstring identifies as
  `weakN_iff`'s entry point).  **[measured]**
* **The cost is exactly the field, and nothing else.**
  `TrProjG.weak'_inv_of_narrow_and_field` — the ten fields *plus* the eleventh, in `Γ` — gives the
  widened conclusion with **no `VEnv.WF`, no `OnCtx`, cone 733, hole-free**.  So the whole of the
  5319-vs-3716 gap and the whole of the `weakN_iff` acquisition are attributable to producing
  that one `HasType`, and anything producing it another way would pay neither.  **[measured]**

**Read against §2, this is a pattern, not an incident**: option (d) leaves five of the structural
lemmas (`mono`, `weak'`, `weakN`, `instN`, `instL`) hole-free and costs `weakN_iff` at exactly the
two lemmas whose conclusion is an **existential over a *new* derivation** (`defeqDFC`,
`weak'_inv`) rather than a transport of the given one.  That is the correct generalisation, and
it predicts the remaining unpriced consumers: any `TrProj` lemma that *constructs* a derivation
pays wall 2; any that *moves* one does not.  I flag the prediction **as a prediction** — it is
proved for the four lemmas measured, and asserted for the rest.

---

## 5. `uniq` — still row 107c's casualty, in one paragraph

Unchanged, and for a reason that has nothing to do with the eleventh field.  `TrProj.uniq` works
by extracting the two derivations' data with `VEnv.IsStructure.projData_uniq`
(`Verify/Typing/ProjSpineInv.lean:74`), whose engine is `VEnv.WF.structureUniq`
(`Verify/Typing/RecTypePeel.lean:258`): two `IsStructure` certificates *for the same name* agree
on the records.  Under `IsStructureG` that step has no analogue — the widened uniqueness would
have to conclude `j₁ = j₂` as well, and a name is not pinned to a block by anything
`IsStructureG` records (its `decl` field existentially quantifies the block).  Definition site
searched: `StructureUniq` / `structureUniq`, over every `*.lean` under `Lean4Lean/` — the
predicate exists only over `IsStructure`, with no `G` variant, and the missing fact is ledger
**G4**, which still has no statement in the tree (it is also `TrProjG.toNarrow`'s `hsingle`).
The eleventh field would then be an *additional* obligation on top, of the same
existential-conclusion kind §4 prices.  So `uniq` is blocked upstream of option (d) and I did not
attempt it.

---

## 6. Where the brief was wrong, and where I was

* **The brief was right** that `projTermG_instN`/`projTermG_instL` already exist and that `instN`
  and `instL` "should go the same way as `weak'`".  Both confirmed, both free.
* **The brief's framing "the unpriced part of the ripple"** is right for `instN`/`instL` and
  slightly optimistic for `defeqDFC`: `defeqDFC` is not a transport at all, it is a
  re-construction, and no amount of `lift'_instAll`-shaped bookkeeping reaches it.
* **My own errors, both self-caught and both recorded in the source file's docstrings**: two
  false absence claims about congruence lemmas (§2.1); and a first draft that called
  `defeqDFC_ten` hole-free when it carries `{forallE_inv_stratified}` — "built green" is not
  "hole-free", and I wrote the sentence the ledger exists to prevent.  Both are corrected in
  `TrProjWideTransport.lean` at the point of claim, not only here.
* **Process slip, disclosed**: to force the build-time guard messages to reprint I ran `touch`
  on `Lean4Lean/Verify/Guard.lean`.  That changes mtime, not content — `git status` shows the
  file unmodified — but a frozen file should not have been touched at all, and I should have
  forced the rebuild another way.

---

## 7. What this changes about the in-place edit (`handoff-trproj-wide.md` §5)

**The edit itself is unchanged** — the four steps stated there are still exactly right, and I did
not make them.  What is now known about its consequences:

* Of the 16 pre-existing hand-written `TrProj.mk` users, **`wf`, `mono`, `weak'`, `instN`,
  `instL` are now proved to survive at their own signatures, hole-free** (`weak'`, `instN`,
  `instL` at `Ordered`/nothing, explicitly *not* `VEnv.WF`).
* `defeqDFC` survives at its own signature and gains `weakN_iff`.
* `weak'_inv` and `uniq` are the two that get worse, for the same structural reason (§4, §5).
* Still unpriced: `defeqDFC_target`, `isStructure` (trivial — `TrProjG.isStructureG` already
  exists), `noConstIn_of_spine`, `uniq_of_projTermCongr`, the two `weak'_inv_of_*` variants, the
  three `projDataCongr` bridges, and `barEnv_TrProj`.

## 8. What to pick up first

1. **Route 2 for `defeqDFC`** (§2.1).  It is the only identified way to keep option (d) *and*
   keep `defeqDFC`'s narrow hole set, both its ingredients exist, and it has never been costed.
2. **Decide whether §4's pattern is a reason to reconsider option (d).**  The cost is now
   concrete: `weakN_iff` at the two existential-conclusion lemmas, one of which
   (`weak'_inv_of_typing_head`) had been deliberately engineered away from that hole.  That is a
   real argument, and it did not exist before this round.
3. **Do not redo `TrProjG.instN`/`.instL`.**  They are twenty lines of `inst_instAll` /
   `instL_instAll` bookkeeping each and are easy to redo badly, exactly as
   `handoff-trproj-wide.md` warned about `weak'`.
4. **Instrument blindness, flagged rather than fixed** (same as both predecessors): the new
   modules are built by the `Lean4Lean.Verify.*` glob but **nothing imports them**, so a census
   working from a fixed import list is blind to them.  Neither contains a `sorry`.
