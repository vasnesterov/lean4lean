# Handoff: `ShapeVar` — the variable entry, added out-of-place, fired, and priced

New file, owned by this stream: `Lean4Lean/Theory/Typing/ShapeVar.lean` (756 lines, 96 jobs,
`Lean4Lean.Theory.*` glob so it builds automatically). Nothing else in the tree was edited —
`git status` shows only `?? Lean4Lean/Theory/Typing/ShapeVar.lean` as mine.

Marks: **[measured]** = a run reproduced here after a full rebuild; **[read]** = read off source;
**[analysis]** = neither.

---

## 0. Verdict, up front

* **The relayed claim is TRUE, and I re-verified it two ways.** `VEnv.RigidShape`
  (`Lean4Lean/Theory/Typing/Injectivity.lean:918`) has exactly three constructors — `sort u`,
  `pi A B`, `app c ls as`; `VEnv.SPShape` (`Lean4Lean/Theory/Typing/InjOneFact.lean:170`) has
  exactly two — `sort u`, `pi A B`; **neither has a `.bvar` entry** [read]. And, better than a
  read: `RigidShape.toExpr_ne_bvar` and `SPShape.toExpr_ne_bvar` prove that **no** shape in
  either vocabulary denotes a `.bvar` — so "cannot express a variable endpoint" is a theorem
  here, not a grep [measured].
* **Outcome 1, partially: the entry is added, the existing results still hold with identical
  axiom lists, and the residual's `.bvar` row is stated and discharged *modulo the extended
  bridge*.** It is not discharged outright, and nothing in this corner could be — see §3.
* **My entry does NOT constrain a `trans` midpoint. I am not the twelfth collapse** — but I am
  also **not claiming a strength gain**, and the honest grading is the one the brief warned
  about: §7 of the file proves `rigidShapeVUniq_iff`, so the extension **is** the old bridge
  conjoined with exactly three new disjointness rows. §5 is therefore a **localisation** of the
  `.bvar` row into the corner's existing shared node, not a reduction of it. Same reading
  `SortPiDisjPrice.lean` §2 forced. What is bought is **vocabulary**: the row stops being an
  unnamed gap outside the machinery and becomes a named row of the one statement all the `trans`
  residuals already share.
* **Two of my own first-draft entries were FALSE, both now refuted at `VEnv.WF` environments**
  (§5 below). This is the part I would read first.
* **Where the brief is wrong**: its outcome-3 hint ("already covered elsewhere under another
  name") is **half right in a way worth recording** — ledger row 86b already says the sort/Π and
  const-spine disjointness facts are three instances of *one* fact ("a κ-normal rigid head has no
  reduct of another shape") plus Church–Rosser, and the variable row is a fourth instance of the
  **same** fact. So the *content* was already accounted for; what was missing was any statement
  and any slot. Nothing in the compiled environment states it [measured, §6].
* **In-place edit: NOT made, and NOT needed to make progress.** The exact edit and its measured
  ripple are §7. I recommend sequencing it, but it is optional: everything below works
  out-of-place.

---

## 1. What is in the file

| § | result | hole cone |
| --- | --- | --- |
| 1 | `RigidShape.toExpr_ne_bvar`, `SPShape.toExpr_ne_bvar` — the old vocabularies cannot denote a variable | **empty** (405 / 65) |
| 2 | `RigidShapeV` = `RigidShape` + `var i`; `toExpr`, `RuleFree`, `Compat`, `BothSort`, `RigidShapeVUniq`, `RigidShapeVUniqNS` | — |
| 3 | `RigidShapeVUniq.rigidShapeUniq`, `RigidShapeVUniqNS.rigidShapeUniqNS` — the collapse | **empty** (646 / 653) |
| 4 | `WF.instL_lhs_ne_bvar` — no rule rewrites a variable | **empty** (1881) |
| 5 | `varPiDisj_of_rigidShapeVUniq` — **the firing test** | `forallE_inv_stratified` (3588) |
| 6 | `codLift_bvar_absurd`, `PiCodLiftNeutral.of_noVar`, `piDescend_iff_neutralNV_sortConv` | empty (157/410); `forallE_inv_stratified` + `rigidShapeUniqNS` (3733) |
| 7 | `rigidShapeVUniq_of_family`, `RigidShapeVUniq.varSortDisj` — the price tag | empty (646); `forallE_inv_stratified` (3588) |
| 8 | anti-vacuity: `varPiDisj_nil`, `bvar_row_reachable`, `varNoConf_false` + its two control halves | **all empty** (899 / 649 / 628 / 169) |
| 8.5 | `RigidShapeVUniq.varAppDisj`, `rigidShapeVUniq_iff` — §7's other half (placed after §8/§10's refutations, which force its guard) | `forallE_inv_stratified` (3573 / 3660) |
| 9 | regression: `RigidShapeVUniqNS.rigidShapeUniq'`, `.piUniq` | empty (3410); `forallE_inv_stratified` (3515) |
| 10 | `wf_svEnv`, `svEnv_conv`, `varAppDisjNaive_false`, `svEnv_isProof_bvar0` | **all empty** (782 / 798 / 814 / 771) |

All cone and hole-cone figures **[measured]** on a rebuilt tree with a local copy of
`scripts/hole-cone.lean`'s walker (run from `/tmp`, so no script in the repo was touched).
`IsDefEqU.weakN_iff` is in **no** cone of any of the 25 seeds, mine or reference **[measured]**.

## 2. The firing test, and why it is a firing test and not a rename

The brief's requirement was: *exhibit an instance the old vocabulary cannot express and the new
one can, with every premise discharged except ones you name.* Both halves are theorems.

* **Old vocabulary cannot**: `RigidShape.toExpr_ne_bvar (s) (i) : s.toExpr ≠ .bvar i`. So the
  appeal `RigidShapeUniq … (s₁ := ?) (s₂ := .pi A B)` with a variable left endpoint is not a
  proof that fails to typecheck — there is no term to write.
* **New vocabulary can, and it fires**: `varPiDisj_of_rigidShapeVUniq` proves
  `VarPiDisj : ∀ Γ i A B, OnCtx Γ … → ¬ env.IsDefEqU U Γ (.bvar i) (.forallE A B)` by the same
  thirteen-case `IsDefEqStrong` induction `IsDefEqU.const_forallE_inv` runs. **Twelve cases
  close outright**: `extra` by the new `WF.instL_lhs_ne_bvar` and the existing
  `WF.instL_lhs_ne_forallE`; `proofIrrel` by `forallE_not_proof` off `WF.sortUniq'` (so it costs
  the statement no hypothesis); the `bvar` constructor is vacuous because its *other* endpoint is
  the same variable; `beta`/`eta` vacuous on their left endpoint; the five congruence rules on
  endpoint heads; `symm`/`defeqDF` bookkeeping. **The thirteenth is `trans`**, discharged at
  `.var i` / `.pi A B`, whose `Compat` entry is `False`.
* **Named residual**: the extended bridge `RigidShapeVUniq`, carried as a hypothesis. Plus
  `forallE_inv_stratified`, which enters through `IsDefEqStrong` and is in every member of this
  family already.

Then it is **used**: `codLift_bvar_absurd` closes `PiCodLiftNeutral`'s variable row (a lift of a
variable is a variable, `liftN_bvar_eq`), and `piDescend_iff_neutralNV_sortConv` is
`PiDescendFstCod.piDescend_iff_neutral_sortConv` with **two** neutral heads instead of three.
Cone 3733 against the original's 3720 — 13 constants of difference **[measured]**.

## 3. Does the entry constrain a midpoint? No — and here is the argument in full

Mandatory question, per ledger rows 94 / 94a / 100–103 (all read before any Lean was written).
The recurring mechanism there is: **a predicate on a `trans` midpoint cannot localise anything,
because β manufactures a midpoint of any shape** (`InjOneFact.midShapeless_vacuous`, `:320`, is
the general theorem: for any `P` with `∀ X, P (betaMid X)`, the `P`-restricted midpoint statement
is *equivalent* to the unrestricted link statement).

`RigidShapeV` values occur in `RigidShapeVUniq` **only as the two endpoints `s₁`, `s₂`**. The
middle term `e` is bound by `∀` and carries only typing premises (`OnCtx`, `¬ IsProof`, and the
two conversions) — byte for byte what `RigidShapeUniq` carries. Nothing was added to `e`. And the
three new rows (`VarPiDisj`, `VarSortDisj`, `VarAppDisj`) mention no midpoint at all: they are
`¬ IsDefEqU` statements between two explicit endpoints, character for character the shape of
`IsDefEqU.const_forallE_inv`. So `midShapeless_vacuous` has nothing to bite on.

**Mark: [read off the definitions]**, not machine-checked. There is no formal statement of "is not
a midpoint restriction" and I did not invent one; the check is that the definition of
`RigidShapeVUniq` in §2 of the file differs from `RigidShapeUniq` in the *index type of `s₁`,
`s₂`* and in nothing else.

What the change **is** vulnerable to instead is the *other* failure mode, and I measured it
rather than argue it: `rigidShapeVUniq_iff` (§7) proves

    RigidShapeVUniq  ↔  RigidShapeUniq ∧ VarPiDisj ∧ VarSortDisj ∧ VarAppDisj

(given `VEnv.WF` and `ProofTransport`), so the extension smuggles in no strength and buys none.
**Grade it as a localisation, not a reduction.**

## 4. The regression: existing consumers are byte-identical in axioms

Nothing in the tree was edited, so existing results are unchanged by construction. The check
the brief asked for is the stronger one — re-derive consumers *through* the new vocabulary and
compare **[measured]**:

| consumer | through `RigidShapeUniqNS` | through `RigidShapeVUniqNS` |
| --- | --- | --- |
| `rigidShapeUniq_of_sortUniq` | `[propext, Classical.choice, Quot.sound]`, cone 3382 | `RigidShapeVUniqNS.rigidShapeUniq'`: `[propext, Classical.choice, Quot.sound]`, cone 3410 |
| `RigidShapeUniqNS.piUniq` | `[propext, sorryAx, Classical.choice, Quot.sound]`, holes `{forallE_inv_stratified}`, cone 3487 | `RigidShapeVUniqNS.piUniq`: same axioms, same holes, cone 3515 |

Identical axiom sets and identical hole cones; the cone grows by the 28 constants of the collapse
lemma, which is hole-free. That is the whole intended effect.

## 5. Two refutations — the part to read first

Both are of **my own** first-draft entries, both at environments that **are** `VEnv.WF`, and both
hole-free. This is where the round's real information is.

1. **The naive diagonal `i = j` is FALSE.** `varNoConf_false : ¬ VarNoConf (∅ : VEnv) 0`. In
   `varCtx3 = [.bvar 1, .bvar 0, Prop]` — every entry a type, over `VEnv.empty`, which is
   `VEnv.WF` by `⟨[], .empty⟩` — the variables `.bvar 0` and `.bvar 1` both inhabit the
   proposition `.bvar 2`, so `proofIrrel` identifies them (`varCtx3_conv`). So "variables are
   told apart by their index" is not available, and the `Compat` diagonal for `var` is `True` —
   which is also its correct value on its own terms, since a bare variable has no subterms to
   compare (the `app` diagonal's content is levels and arguments; a variable has neither).
   *Control, second half*: `varCtx3_compat` shows the row this file actually declares **holds** at
   the witness, and `varCtx3_isProof` shows `.bvar 0` **is** a proof there, so the bridge's
   `¬ IsProof` premise excludes the witness before `Compat` is consulted. Nothing here refutes
   the target.
2. **The naive var/app off-diagonal, unguarded, is FALSE.**
   `varAppDisjNaive_false : ¬ VarAppDisjNaive svEnv 0`, where `svEnv` = `VEnv.empty` plus one
   axiom `svC : ∀ X : Prop, X` and **no rules** (so every head is rule-free), `VEnv.WF` by one
   `.axiom` step (`wf_svEnv`) — the one-axiom construction `RigidConstPrice.wf_rcEnv0` uses,
   rebuilt locally rather than imported because that file is another stream's. In the context
   `[∀ X : Prop, X]` the variable `.bvar 0` and the spine `svC` are both proofs of the same
   proposition, and `proofIrrel` identifies them (`svEnv_conv`).
   **My first `rigidShapeVUniq_of_family` took the unguarded row as a hypothesis and was
   therefore vacuous, while printing a clean `[propext]` and an empty hole cone.** It is now
   guarded by `¬ IsProof (.bvar i)`, which is what the bridge's own premise supplies (via
   `ProofTransport`, taken as an explicit hypothesis so the price tag stays hole-free — the
   discipline `PiLevelPin.lean` uses for `SortUniq`).
   *Control, second half*: `svEnv_isProof_bvar0`. Note the asymmetry with `ForallInvPrice`'s
   `rogueSortPiEnv`: there a `not_wf_sortPiEnv` half is needed because the witness is
   `Ordered`-but-not-`WF`. Here the witness **is** `WF`, so no such half exists or is needed —
   which is exactly what makes this a hard constraint on the vocabulary rather than a control.

**Why the variable rows differ from the sort and Π rows, in one sentence**: a sort and a Π are
not proofs, so their `proofIrrel` cases close for free; a variable can be a proof, so the var/app
row needs a guard and the var/var row must claim nothing. The var/Π and var/sort rows are still
unguarded and still fine, because the *Π side* and the *sort side* close `proofIrrel` on their
own.

## 6. Anti-vacuity, in the order the ledger asks

* **Inhabitation and hole-freeness, stated separately, as the brief requires.**
  * *Hole-freeness*: **19 of my 25 measured seeds** have **empty hole cones** — §1, §3, §4, §6's mechanics, §7's
    price tag, and all of §8 and §10 **[measured]**. The three inductions (§5, §7's two
    converses) carry `sorryAx` through **`IsDefEqU.forallE_inv_stratified` only**;
    `piDescend_iff_neutralNV_sortConv` additionally through `WF.rigidShapeUniqNS`, the same pair
    as the theorem it refines. `weakN_iff` in no cone. **"`weakN_iff` absent" is not
    "hole-free"**, and there is a second caveat the cone cannot see at all: the extended bridge
    is a **hypothesis**, and a hypothesis is not a dependency (ledger §0, third instrument). The
    real obligation of §5 is invisible to `#print axioms` and to the cone.
  * *Inhabitation*: **`VarPiDisj` has no inhabitation witness here, and I did not build one.**
    This is not a gap peculiar to me: `InjPiRogue.lean:99` records that
    `StrengthenAudit.no_neutral_proofIrrel` is the **one** inhabited `¬ IsDefEqU` in the whole
    tree, and it is built from `IsDefEqU.sort_forallE_inv`, i.e. from the hole. What is exhibited
    instead is (a) the row's **type-side** premises fire (`bvar_row_reachable`), and (b) an
    absolute inhabitation witness for the residual's conversion premise would **refute the
    target**, by `PiDescendFstCod.piDescend_of_no_neutral_pi`. So the honest status is: not
    inhabited, and inhabiting it is as hard as settling `PiDescend`.
  * No witness environment used here declares anything like `univInhab`; both are `VEnv.empty` or
    `VEnv.empty` + one axiom, and neither is inconsistent as far as anything here shows. (I make
    no consistency *claim* — `Theory/Consistency.lean` states consistency without proof.)
* **Firing test**: §2 above. A widening with only a collapse test would be a rename; this one has
  both halves as theorems.
* **Degenerate instance (blindness 7), in its dual form.** `VarPiDisj` is a *negation*, so the
  degenerate risk is triviality, not emptiness — and at `Γ = []` it **is** a theorem, at every
  `Ordered` environment, by the scope invariant `IsDefEq.closedN` (`varPiDisj_nil`, hole-free).
  So all of its content is at non-empty contexts, and `bvar_row_reachable` is deliberately at a
  context of length two.
* **Row reachability.** `bvar_row_reachable`: over `VEnv.empty`, in `varCtx2 = [.bvar 0, Prop]`,
  the term `.bvar 0` is well-typed at the **variable** type `.bvar 1`, which is itself a type and
  is `PiDescendNeutral` — and `∀ s : RigidShape, s.toExpr ≠ .bvar 1` is bundled into the same
  statement. So §6 deletes a row with live instances on its type side.
* **Negative controls**: §5, both of them, with both halves each.

## 7. The in-place edit, stated and NOT made, with its measured ripple

I did **not** touch `Injectivity.lean`. If you want the entry in place, the edit is:

1. `inductive RigidShape` (`Injectivity.lean:918`) — add `| var (i : Nat)`.
2. `RigidShape.toExpr` (`:924`) — add `| .var i => .bvar i`.
3. `RigidShape.RuleFree` (`:932`) — add `| .var _ => True`. **No** side condition; `§4`'s
   `WF.instL_lhs_ne_bvar` is why, and it belongs next to `instL_lhs_ne_sort` /
   `instL_lhs_ne_forallE` in `DeclRules.lean:234,240` rather than in my file.
4. `RigidShape.Compat` (`:949`) — currently **nine explicit rows**; needs **seven more**:
   `var/var => True` (§5.1 forbids `i = j`), and `var/sort`, `sort/var`, `var/pi`, `pi/var`,
   `var/app`, `app/var` all `False`. Or restructure with a `| _, _ => False` catch-all, as my
   `RigidShapeV.Compat` does.
5. `RigidShape.BothSort` (`:998`) — already has a `| _, _ => False` catch-all; **no edit**.

**Measured ripple** [measured, over the compiled environment]: **86** declarations mention
`RigidShape` at all, but only **9 hand-written declarations eliminate it** and would need new
cases (the other 12 eliminators are auto-generated `casesOn`/`recOn`/`noConfusion`/`ctorIdx`/
`match_1` and my own `toV` lemmas, which the in-place version deletes):

* `Injectivity.lean`: `RigidShape.toExpr`, `RigidShape.RuleFree`, `RigidShape.Compat`,
  `RigidShape.BothSort`, `rigidShapeUniq_of_sortUniq`, `rigidShapeUniq_of_family`;
* `RigidNodeCircle.lean:169`: `rigidShapeUniqNS_of_family`;
* `InjSpineTransport.lean:175,221`: `rigidShapeUniqNS_of_familySpine`,
  `rigidShapeUniq_of_family_convStep2`.

Each of the five theorems is a `cases s₁ <;> cases s₂` and gains four rows; each needs the three
new disjointness facts as hypotheses (or `False.elim` on the `var` rows if the family form is
kept as a *lower* bound). `SPShape` is separate: **18** eliminators, **60** mentions; I did not
extend it, because none of its three consumers ranges over a variable (`InjOneFact.lean` §3 says
so explicitly) and extending it would be a widening with no consumer — a rename.

**My recommendation**: sequence the in-place edit, but not urgently. Out-of-place cost is one
hole-free collapse lemma and 28 constants of cone; the only real benefit of in-place is that
future consumers do not have to know two vocabularies exist.

## 8. Where the brief and its inputs are wrong

1. **"the `.bvar` row … has no machinery pointing at it" — right about machinery, incomplete
   about accounting.** Ledger row 86b already rules that the sort/Π and const-spine disjointness
   facts are three instances of one fact ("a κ-normal rigid head has no reduct of another shape")
   plus Church–Rosser. The variable row is a **fourth instance of the same fact**, so the corner's
   critical path does not lengthen by adding it — one prerequisite, now four consumers. That is a
   sharpening of `handoff-pidescendfst.md` §9's guess that "the entry may be nearly free"; it is
   nearly free, and §5 measures how nearly.
2. **`handoff-pidescendfst.md` §5's absence claim is confirmed but its scope statement is the
   right one and should not be widened.** I re-ran the absence question over the compiled
   environment of my own module: nothing states variable/Π disjointness. But note it is now
   *statable*, which the earlier claim said it was not "even in principle" — that phrasing was
   about `RigidShape`'s vocabulary, and it is exactly right about that.
3. **The brief's framing "add the entry … and use it to discharge the row" invites over-reading.**
   The row is discharged **modulo the same bridge everything else in the family sits on**, and §7
   proves that bridge is *equivalent* to the old one plus the three rows. There is no version of
   this change that discharges the row without confluence.
4. **A guess of mine that was wrong and is worth recording**: I first designed the entry as a
   *spine* `var i as`, on the grounds that it would also cover part of `PiCodLiftNeutral`'s
   `.app` row (whose live content is δ-active constant spines **and** variable-headed spines).
   That does not go through as cheaply: `IsDeclRule.lhs_shape` (`DeclRules.lean:203`) allows a
   rule's left-hand side to be an `.app`, so `extra` is not closed by head shape and needs the
   closedness of `df.lhs` (which `VDefEq.WF` does give, typing both sides in the **empty**
   context, but there is no `ClosedN.spineHead` lemma in the tree to cash it in with)
   **[analysis]**. Bare `var i` is what the `.bvar` row needs and it is what I built.

## 9. What to pick up first

1. **The variable-headed *spine* entry**, `var i as`. It covers the variable slice of
   `PiCodLiftNeutral`'s `.app` row, which after `codLift_const_ruleFree` and my
   `codLift_bvar_absurd` is one of the two things left in the whole residual. The one missing
   ingredient is measured in §8.4: a `ClosedN`-of-`spineHead` step so that `extra` closes from
   `VDefEq.WF`'s empty-context typing. That looks like a five-line lemma about `VExpr` and it is
   not in the tree.
2. **The in-place edit** (§7), when you want to stop maintaining two vocabularies. 9 hand-written
   declarations, 3 files, none of them frozen.
3. **Do not** look for an inhabitation witness for `VarPiDisj` before `PiDescend` moves: §6 says
   finding one refutes the target.
4. **Ledger rows to add** (I did not edit `docs/vacuity-ledger.md` — not my file): the two
   refutations of §5, both as "my own draft hypothesis, false at a `VEnv.WF` environment,
   witness reachable"; and the grading of §5-of-the-file as a **localisation** (collapse-adjacent
   but not a collapse: the statement was never claimed to be weaker).

## 10. Verification

* `lake build`: green, whole tree, at the moment the census below was run **[measured]**. A later
  re-run failed in **`Lean4Lean/Verify/TypeChecker/EtaUnitRefute.lean:29`** (a `rewrite` failure) —
  that file is untracked, belongs to the concurrent `Verify/TypeChecker/EtaUnit*` stream, and is
  not in my import closure; `lake build Lean4Lean.Theory.Typing.ShapeVar` is green throughout
  **[measured]**. Flagging it rather than touching it.
* Module: `Lean4Lean.Theory.Typing.ShapeVar`, **96 jobs** **[measured]**.
* `lake env lean --run scripts/sorry-census-all.lean`: **375** modules in the default-target
  population, **375 BUILT, 0 not built**, **13 holes** over the whole built population — the same
  13 as before this round **[measured]**. (An earlier run of the census, before a full rebuild,
  reported 2 unbuilt modules — `Lean4Lean.Verify.Primitive` and
  `Lean4Lean.Verify.TypeChecker.EtaUnitRefute`, both other streams' — and crashed on the missing
  `.olean`. A full `lake build` fixed it. Recording it because the brief warned about exactly
  this and it fired.)
* `scripts/dup-names.lean`: no duplicate `Lean4Lean` declarations **[measured]**.
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` is **empty** **[measured]**.
* Frozen files: `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` not read, not
  written, not touched.
* No `git` state-changing command run; nothing sent anywhere.
