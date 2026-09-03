# Handoff: wall 2 (`projTermG_hasType`) — **proved**, and it is two walls, not one

*Round of 2026-09-03.  New modules only: `Lean4Lean/Verify/Typing/ProjGenTerm.lean` (782
lines, 12 declarations) and `Lean4Lean/Verify/TypeChecker/ProjGenTermWitness.lean` (37 lines,
1 declaration).  **No existing file was edited**, so no existing declaration can have moved.*

Every claim below is tagged **[measured]** (an instrument was run this round, named at the
claim) or **[read off source]**.

---

## 0. Headline

**Wall 2 is closed at the generality that two of the three corners actually need, and it is
open at the generality the third needs — and those are two different statements.**  The brief
conflated them.

```
theorem VEnv.IsStructureG.projTermG_hasType (henv : VEnv.WF env)
    (Hs : env.IsStructureG S D j T C) (hrec : C.recFields = [])
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U) :
    ∀ i, i < C.fields.length →
      (∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) → (C.fields.getD k default).lvl.inst us
          ≈ D.elimLvl.inst (D.projLvls C us k)) →
      ProjHasTypeG env U S D T C us j i
```

* `VEnv.IsStructure` → `VEnv.IsStructureG`: the `types : D.types = [T]` field is **gone**, a
  block index `j` appears, and `projTerm` is `projTermG`.  This is the statement
  `docs/vacuity-ledger.md` rows 105a(2), 107b and 114–114c call wall 2.
* `C.recFields = []` is carried as an **explicit premise**.  `IsStructureG` dropped it, so it
  has to come from somewhere; `EtaStructSpineG` (`Verify/TypeChecker/EtaStructG.lean:601`)
  **already carries it as an explicit conjunct**, which is why this is the right cut.  §3 is
  the price of removing it.
* Axioms `[propext, sorryAx, Classical.choice, Quot.sound]`; forward cone **5271**; hole set
  **`{weakN_iff, forallE_inv_stratified}`** — *byte-identical to the narrow
  `projTerm_hasType`'s* (cone 5082, same two holes).  **[measured]**, own instrument,
  `getUsedConstantsAsSet` with `allowOpaque := true`.
* **No new `sorry`, none traded, no new frozen-axiom dependency.**  `#print axioms` on all 13
  new declarations shows no `Lean4Lean.*` axiom at all.  **[measured]**
* **Hole-free is not discharged, and this is not hole-free.**  The result inherits
  `weakN_iff`/`forallE_inv_stratified` through `VEnv.HasType.swapCtx`, exactly as the narrow
  lemma does (`ProjGenSwap.lean`'s docstring says so).  What is new is *not* that a hole
  closed — none did — but that a statement which did not exist now does, at the same hole
  cone as its narrow predecessor.

Collapse test, in the same file: **`projTerm_hasType_of_G`** re-derives the narrow
`projTerm_hasType`'s statement, hypothesis for hypothesis, from the general one at `j = 0`
through `projHasTypeG_eq`.  So this is a generalisation, not a differently-shaped statement.

Firing test, `Verify/TypeChecker/ProjGenTermWitness.lean`:
**`MutField.projTermG_hasType_at_mutual`** fires it at `MutField.declEnv` — the **two-type**
mutual block of `EtaStructG.lean`, projected member at index **1**, one field, where
`VEnv.IsStructure` is outright false (`MutField.decl_not_isStructure`).  Every premise is
discharged **except `VEnv.WF declEnv`**, which is taken as a hypothesis: nothing in this tree
proves `VEnv.WF` of an `addInduct'` environment (that is the keystone), and the *narrow*
lemma is in the same position at its own witnesses.  Hole set of the firing: the same two.
**[measured]**

---

## 1. Where the brief is wrong

I was asked to say this plainly.  Five items, in decreasing importance.

### 1.1 "Three corners gate on it" is right about the gating and wrong that one item clears all three

| corner | needs | status after this round |
|---|---|---|
| `TrProj.weak'_inv` (90 users), via the `TrProj` widening / option (d) | wall 2 **at whatever generality the widened `TrProj` carries** | **unblocked iff the widening keeps `noRec`.**  Ledger row 107d ruling (iii) says "take the `noRec` drop with it" — and that ruling exists *because* it is "what makes `inferProj.WF` provable at all", i.e. corners 1 and 2 were deliberately bundled.  **Unbundling them is the single highest-value decision available now.** |
| `inferProj.WF` (70 users) | wall 2 **`noRec`-free** — `inferProj` never reads `I_val.isRec` | **NOT unblocked.**  §3 names the extra obligation, and it has no statement anywhere in the tree. |
| the eta corner (`isDefEqUnitLike.WF`, `tryEtaStructCore.WF`) | the `StructEtaG` constructor's `IsDefEqStrong.hasType'` case | **the `VEnv.HasType` half is done**, at exactly the generality `EtaStructSpineG` states.  The remaining half is a *relation upgrade*, §2. |

### 1.2 The eta corner needs `HasTypeStrong`, not `HasType` — and the brief (and `docs/audit-isdefeq-constructor.md` item 10) do not distinguish them

Item 10 says the new constructor's case of `IsDefEqStrong.hasType'` must produce
`HasTypeStrong Γ (D.etaExpansionG …) ((const S us).mkApp ps)`.  What I proved is
`VEnv.HasType`.  **`HasTypeStrong.hasType` exists (`Theory/Typing/Strong.lean:885`); the
converse does not exist anywhere** — grep for `HasTypeStrong` across `Lean4Lean/`, and the
only bridges are strong → plain, plus `HasTypeStrong.stratify`.  **[measured]**

So item 10's *soundness* question is answered — the rule does **not** assert a defeq with an
ill-typed side, which was the thing that would have made the constructor "wrong, not merely
expensive" — but its *cost* question is not.  The residual is: restate the projection cluster
over `HasTypeStrong`, or find a `HasType → HasTypeStrong` refinement for these terms.  Neither
exists, and neither has been priced.  **Do not read this round as "the constructor is now
cheap".**

### 1.3 Ledger row 114c has the right shape and the wrong second conjunct

Row 114c: "one `Nat.strongRecOn` on the field index whose motive is the **conjunction**
«`ProjHasTypeG … j k`» ∧ «minor-block spine at `k`»".

The induction is exactly one `Nat.strongRecOn` and the motive is exactly a conjunction — that
part is right, and it is what `projTermG_hasType_aux` does.  But the second conjunct **cannot
be the spine**: the spine is needed in a *different context* (the constructor's own field
telescope over the ambient one) at a *different* parameter spine (`ps.map (·.liftN nf)`), so
only a `Γ`/`ps`/`ιs`/`e`-quantified predicate can be carried.  The conjunct that works is
`ProjRealMinorG` — the real minor's typing, quantified over the same data `ProjHasTypeG` is.

And the spine at the *current* field index is **not** an induction conjunct at all.  See §1.4.

### 1.4 The mechanism that opens the circle is recorded nowhere, and it is one sentence

The apparent circle is: block spine at `take q` ⟸ real minor at slot `q` ⟸ the ι/swap/β defeq
`hiota` ⟸ block spine.  **It opens because `hiota` does not mention `q`.**  So the induction on
the minor slot `q` that builds the spine can discharge its own projected entry on the way up,
from a `hiota` fixed once outside it.  That is `padMinors_hasArgs_take_of_hiota` — the same
induction as `padMinors_hasArgs_take` (`ProjGenBlock.lean`) with the `hreal` **premise replaced
by its ingredients**, cone 4018, **hole set empty**.  **[measured]**

Consequence for the ledger: row 114's "the circle is in exactly ONE premise" is correct, and
the bounded/`take`-restricted variant of `padMinors_hasArgs_take` that an earlier plan would
have needed is **not** needed.  `padMinors_hasArgs_take` itself was left untouched.

### 1.5 Four small pieces were missing that no document listed

`docs/handoff-inferproj.md` §7.2 says wall 2's "two named prerequisites (`iota_law_gen`,
`realMinor_app`) are now closed, and what is left is one `Nat.strongRecOn`".  What was also
missing, and is now landed in `ProjGenTerm.lean`:

* **`VEnv.IsStructureG.iotaCtx`** and **`VEnv.IsStructureG.iotaDefeq`** — `iota_law_gen` needs
  `D.IotaCtx env` and `env.defeqs (D.iotaRule j q C)`, and only the *narrow*
  `IsStructure.iotaCtx`/`.iotaDefeq` existed.  Row 107c lists both among "six structural
  lemmas that widen and were **compiled**" — they were compiled **in scratch** and never
  landed, so the tree did not have them.  Both are one-liners off `H.decl` plus
  `VInductDecl'.iotaRule_mem`; the narrow `iotaCtx` never reads `types`/`ctors`/`noRec` at all.
* **`args_closedN_gen`** — the narrow `args_closedN` takes `env.IsStructure`.
* **`VInductDecl'.mem_ctorsAll_gen`** — `(j, C) ∈ D.ctorsAll` from `types[j]?` + `C ∈ T.ctors`.
  Only the *forward* `mem_ctorsAll` existed in the import closure.

And **`realMinor_app` was not needed**.  With `noRec` carried, `projMinor_app` (already landed,
and already general in `ps`/`fs`) does the job.  `realMinor_app` is a prerequisite of the
`noRec`-**free** half only.

---

## 2. What the proof is, so it can be checked without re-reading it

`Lean4Lean/Verify/Typing/ProjGenTerm.lean`, in dependency order:

| declaration | what it is | cone / holes |
|---|---|---|
| `VEnv.IsStructureG.iotaCtx`, `.iotaDefeq` | the two environment facts `iota_law_gen` needs, at an arbitrary block member and constructor | `[propext, Quot.sound]` |
| `args_closedN_gen`, `VInductDecl'.mem_ctorsAll_gen` | bookkeeping the narrow forms had only at index 0 | `[propext, Quot.sound]` |
| `projGen_hiota` | **the tail of `projMinor_hasType`, generalised** — `hFL`/`hFR`, `swapDataG`, `hr`/`hDFearlier`, `hcong`, `hbetaQ`, assembly.  Takes the two facts about *earlier* fields (`hIH`, `hiotaK`) as premises, because that is where the recursion sits | 5005 / the two |
| `ProjRealMinorG` (def) | `projCoreG_hasType_of_hreal`'s `hreal`, `Γ`/`ps`/`ιs`/`e`-quantified.  **The second conjunct of the induction motive** | — |
| `projTermG_hasType_of_hreal` | the type side: one β-reduction (`projMotiveBodyG_instAll`) joining `projCoreG_hasType_of_hreal`'s conclusion to `ProjHasTypeG`'s | 4999 / the two |
| `projGen_iota_step` | **the ι law at field `k`**: `padMotives_hasArgs` + `padMinors_hasArgs` (whose `hreal` is the strong IH) → `iotaCtx_hasArgs` → `iota_law_gen_norec` → `projMinor_app` → `trans` | 4933 / the two |
| `padMinors_hasArgs_take_of_hiota` | §1.4: the block spine with the projected entry discharged internally | 4018 / **none** |
| `projTermG_hasType_aux` | the `Nat.strongRecOn`, motive `ProjHasTypeG ∧ ProjRealMinorG` | 5192 / the two |
| `VEnv.IsStructureG.projTermG_hasType` | the packaging at `IsStructureG` | 5271 / the two |
| `projTerm_hasType_of_G` | the collapse test | 5304 / the two |

One detail worth keeping, because it cost a false start: inside the induction, the **field
telescope's `OnCtx`** (`hOnΔF`, which every later step needs) is obtained from
`minor_declType_isType_gen` at **slot `0` with an empty accumulator** — that instance needs
only the *motive* block (`padMotives_hasArgs`), no minors at all — then `minorType_eq_mkPi` +
`IsType.mkPi_inv` + `minorTele_norec`.  The narrow proof gets it from the minor's declared type
at the block it already has; at a general block that would have been circular.

Cost, deterministically: `lake env lean` on the module is **2.4 s** end to end (elaboration +
kernel), on the witness **1.9 s**, at the **default `maxHeartbeats`** — the narrow
`projTerm_hasType` needs `set_option maxHeartbeats 1000000`, this does not.  Per-module `lake
build`: **73 jobs** (`ProjGenTerm`), **153 jobs** (`ProjGenTermWitness`).  **[measured]**

---

## 3. The other wall: wall 2 without `noRec`, priced

This is the half `inferProj.WF` needs, and the price is **nameable and not yet stated
anywhere**.

With `C.recFields = []` dropped, `iota_law_gen`'s reduct is `minor.mkApp (fs ++ ihs)` where
`ihs` is `(D.ihValues C).map (VExpr.instAll · (ps ++ mots ++ mins ++ fs))`, and the minor is
`D.realMinor`, not `C.projMinor`.  Two changes follow:

1. `projMinor_app` becomes `realMinor_app` (**already landed**, `ProjGenMinor.lean`), and
2. `realMinor_app`'s `hA` premise requires **`HasArgs Γ (minorBinders telescope) (fs ++ ihs)`**
   — i.e. **every induction-hypothesis value must be well typed at its `ihType`**.

`D.ihValues C` (`Theory/Inductive/Decl.lean:722`) is, per recursive field, a *recursor
application* under that field's own `r.binders` (ξ) telescope, at the **padded** motive and
minor blocks.  Typing it needs `recApp_hasType''` in a doubly-extended context (field
telescope, then ξ), with the padded block weakened into it, and the motive slot read at the
recursive field's *own* block index `r.idx` — which is generally a **padding** motive, not the
real one.

**Nothing in the tree types `ihValues`.**  The identifier occurs in exactly three places:
its definition (`Decl.lean`), `ihValuesR` (`Restore.lean`), and inside `iota_law_gen`'s own
statement (`Theory/Inductive/IotaGen.lean`).  Predicate: the token `ihValues`; tree covered:
all of `Lean4Lean/` (`grep -rn --include=*.lean`).  A synonym could hide from that grep, so
treat it as a floor — but `ihTypes`, the corresponding *types*, is likewise only ever
manipulated syntactically (`minorTele_gen`, `length_minorBinders_map`, and the `= []` collapse
lemmas), never inhabited.  **[measured]**

So the `noRec`-free half is **one new lemma cluster with no precedent**, not a substitution.
Against it, `docs/handoff-inferproj.md` §7.3's other exit — **decide `bugs-found.md` item 10 by
making `addDecl` reject `.proj` at a recursive constructor** — is now clearly the cheaper of
the two, and nobody had priced them against each other.  That is a `divergences.md` entry plus
an arena run, versus a cluster that has to type recursor applications under nested ξ-binders.

---

## 4. What I tried that failed, and the step it failed at

1. **Carrying "the minor-block spine at `k`" as the induction's second conjunct** (row 114c as
   written).  Failed at *stating* it: the spine the ι step at `k` needs lives in
   `(instAllTele (C.fields.map …) ps).reverse ++ Γ` at parameter spine `ps.map (·.liftN nf)`,
   not in `Γ` at `ps`, so a conjunct fixed at the induction's own context is the wrong object.
   Replaced by `ProjRealMinorG`, which quantifies the context.
2. **Getting `hOnΔF` from `minor_declType_isType_gen` at the actual slot `q`.**  Failed at
   `hspine`: that instance needs the block spine at `take q`, which is what `hOnΔF` is being
   used to build.  Fixed by taking slot `0` with an empty accumulator instead (§2).
3. **A `take`-bounded variant of `padMinors_hasArgs_take`** (`hreal` restricted to `q' < q`),
   to break the slot circularity.  **Abandoned as unnecessary**, not as failed: §1.4's
   observation that `hiota` is `q`-independent makes the plain induction work, and
   `padMinors_hasArgs_take` did not have to be touched.  Had I not noticed, the bounded variant
   would additionally have needed "`ctorsAll` has exactly one entry at index `j` when
   `T.ctors` is a singleton", which has no statement in the tree.
4. **Firing the result unconditionally at the mutual witness.**  Failed at `VEnv.WF declEnv`:
   no lemma in the tree gives `VEnv.WF` of an environment built by `addInduct'` (grep for
   `VEnv.WF` applied to any witness environment; the closest are `decl_WF : decl.WF
   VEnv.empty`, which is the *declaration's* well-formedness, not the environment's).  So the
   firing is stated as an implication.  **[measured]**

---

## 5. Anti-vacuity, applied to this round's own output

* **No hypothesis of any existing declaration was strengthened and no conclusion weakened**;
  no existing file was edited at all (`git status`: my only entries are the two new files).
* The new statement is **not** vacuous by construction: `projTerm_hasType_of_G` shows it
  implies the narrow lemma, and `MutField.projTermG_hasType_at_mutual` shows every premise but
  `VEnv.WF` is jointly satisfiable at a block where the narrow *predicate* is false.
* `hrec : C.recFields = []` is a **real** premise, not a smuggled narrowing: `IsStructureG`
  dropped it deliberately, `EtaStructSpineG` already re-adds it, and §3 is the honest price of
  removing it again.  It is *not* the `types = [T]` field — that one is genuinely gone.
* **`TrProj` was not widened.**  `Verify/Typing/Lemmas.lean`, `ProjWeakInvSplit.lean`,
  `Experimental/ConeJoin.lean` and all three frozen files were not touched.
* **Instrument blindness, flagged rather than fixed:** `ProjGenTerm.lean` is picked up by
  `lake build` (the `Lean4Lean.Verify.*` glob in `lakefile.toml`), but **nothing in the tree
  imports it except my own witness module, which nothing imports.**  Any census instrument that
  works from a fixed import list — `scripts/cone-measure.lean`, `Experimental/ConeJoin.lean` —
  is therefore blind to both new leaves.  I did not add an import to a file in those closures,
  because that would move other declarations' cones and `ConeJoin.lean` is off limits to me.
  **Orchestrator action:** if the census should see these, one file already in the closure has
  to import `Lean4Lean.Verify.Typing.ProjGenTerm`.  Nothing is at risk in the meantime — the
  module contains no `sorry`, so no census count moves either way.

---

## 6. What to pick up first

1. **The unbundling decision, and it is yours.**  Ledger row 107d ruling (iii) ties the
   `TrProj` widening to the `noRec` drop.  Split it: widen `TrProj` **keeping** `noRec`, via
   option (d)'s eleventh field, and `VEnv.IsStructureG.projTermG_hasType` discharges that field
   today.  That is `TrProj.weak'_inv`'s 90 users and `TrProj.wf`'s 158, on a lemma that now
   exists.  `inferProj.WF` stays where it is — it was last in its own ordering anyway
   (`docs/handoff-inferproj.md` §4).
2. **Price the relation upgrade for the eta corner** (§1.2) before adding the `StructEtaG`
   constructor.  The soundness objection in `docs/audit-isdefeq-constructor.md` item 10 is
   answered; the cost objection has moved, not vanished.  Concretely: does
   `IsDefEqStrong.hasType'`'s new case actually need `HasTypeStrong` of the whole η-expansion,
   or can it be assembled from `HasTypeStrong` of the *major premise* plus plain typing of the
   projections?  Nobody has looked.
3. **Then, and only then, `inferProj.WF`** — and price §3's ih-value cluster against
   `bugs-found.md` item 10's second exit first.  My reading is that item 10's exit is cheaper
   by a wide margin, and that is a change from the standing assumption that the generalisation
   is the cheaper way out.
4. **Do not re-derive `projGen_hiota`.**  It is a 180-line transcription of
   `projMinor_hasType`'s tail with `projTerm ↦ projTermG … j` and `IsStructure ↦ hTj/hctors/
   hname + ProjClosedG`.  A future round that "generalises the swap chain" will be redoing it.
