# Handoff: the `TrProj` widening (ledger row 107d option (d)), with `noRec` kept

*Round of 2026-09-03.  New modules only — `Lean4Lean/Verify/Typing/TrProjWide.lean` (238 lines,
12 declarations) and `Lean4Lean/Verify/Typing/TrProjWideWitness.lean` (139 lines, 9
declarations).  **No existing file was edited**, so no existing declaration can have moved, and
`TrProj`'s own definition site (`Verify/Typing/Expr.lean:82-146`) is untouched.*

Every claim is tagged **[measured]** (an instrument was run this round, named at the claim) or
**[read off source]**.

---

## 0. Headline

**Outcome 2 of the brief's list, plus the firing test and one measurement the brief did not ask
for.**  The widening is landed as a *new* predicate `TrProjG` beside `TrProj`, and **the eleventh
field is discharged** — at every environment where the caller can supply `VEnv.WF`.

| result | what it is | axioms | cone / holes **[measured]** |
|---|---|---|---|
| `TrProjG` | the widened relation: `IsStructureG S D j T C`, `C.recFields = []` **kept**, target `projTermG … i j`, **eleventh field** = the target's typing | — | 6 / none |
| `TrProjG.wf` | option (d)'s payoff: `cases`-and-project.  **No `VEnv.WF`, no `OnCtx`, no `VExpr.WF` of the major premise** | `[propext, Quot.sound]` | 737 / **none** |
| **`TrProjG.mk'`** | **the eleventh field discharged**: the ten fields + `VEnv.WF env` + `OnCtx Γ` ⟹ `TrProjG`, via `VEnv.IsStructureG.projTermG_hasType` | `[propext, sorryAx, Classical.choice, Quot.sound]` | 5278 / `{weakN_iff, forallE_inv_stratified}` |
| `TrProj.toG` | **collapse, direction 1**: every `TrProj` derivation is a `TrProjG` derivation at `j = 0`, same major premise, same target | same | 5313 / the same two |
| `TrProjG.toNarrow` | collapse, direction 2 — **conditional on a G4-shaped hypothesis**, see §4 | `[propext, Quot.sound]` | 1723 / none |
| `TrProjG.mono` / `.weak'` / `.weakN` | the eleventh field **transports** through the structural cluster, at the *same* hypotheses `TrProj.weak'` takes | `[propext(, Classical.choice), Quot.sound]` | 1020 / 3581 / 3582, **all holes none** |
| `MutField.declEnv_trProjG` | **firing test** at the two-type mutual block, member `j = 1`, one field, eleventh field *discharged* | `[propext, sorryAx, Classical.choice, Quot.sound]` | 6756 / the same two |
| `MutField.declEnv_trProjG_ten_fields` | the ten fields at that block with **no hypothesis at all** | `[propext, Classical.choice, Quot.sound]` | — / **none** |
| `barEnv_trProjG`, `barEnv_trProjG_wf` | the collapse fired at the tree's only concrete `TrProj` derivation | same as `mk'` | 5355 / 5360, the same two |

Baselines for comparison, re-measured this round in the same instrument run: `TrProj.wf` cone
**5091**, holes `{weakN_iff, forallE_inv_stratified}`; `projTermG_hasType` **5271**, same two;
`projTerm_hasType` **5082**, same two; `TrProj.weak'` **3263**, none.  **[measured]**

**No new hole, nothing traded.**  Everything that carries `sorryAx` carries exactly
`{VEnv.IsDefEqU.weakN_iff, VEnv.IsDefEqU.forallE_inv_stratified}` — wall 2's own two, which are
the *narrow* `projTerm_hasType`'s own two.  "Built green" ≠ "sorry-free" ≠ "discharged": the
discharge of the eleventh field **inherits both holes**, and `TrProjG.wf` is hole-free only
because the content sits in the constructor.  Full `lake build` on the final state: **1542 jobs, exit 0**; guard 1
`24 frozen axioms ✓`, guard 2 `within whitelist ✓ (proof INCOMPLETE: sorryAx present)`, guard 3
`2/2 ✓` — all three unchanged.  **[measured]**

---

## 1. The relay was accurate.  Row 107d says what the brief said it says

Checked because the brief asked, and because it flagged the risk of a relay error.  Row 107d,
quoted: option (d) is "add the target's typing as an **eleventh field of `TrProj.mk`**"; its
rulings are "(i) do NOT widen `TrProj` now; (ii) when it is widened, prefer option (d); (iii)
take the `noRec` drop with it".  Row 174b's split — "widen `TrProj` via option (d) *keeping*
`noRec` and the eleventh field is discharged today" — is exactly what was relayed.  **No
correction needed on either.**  **[read off source]**

`TrProj.mk` does have exactly **ten** fields today (`IsStructure`, the major premise's typing,
three lengths, `i < fields.length`, `hus`, two `HasArgs`, F17), so "eleventh" is literally
right.  **[read off source]**

---

## 2. Where the record *is* wrong

### 2.1 Row 107a cites `MutField.declEnv_trProjG` as if it existed.  It did not

Absence claim, stated to the standard the brief asks for.  Symbol searched for:
`declEnv_trProjG`, whose definition site is now
`Lean4Lean/Verify/Typing/TrProjWideWitness.lean:80` (namespace `Lean4Lean.MutField`, read off the
file's own `namespace` lines).  Tree covered: **every `*.lean` file at `HEAD`**
(`git grep -n declEnv_trProjG HEAD -- '*.lean'` → **0 matches**), plus the working tree
(`grep -rn --include=*.lean` over all of `Lean4Lean/`).  Row 107a's own witness column says "measured in scratch", so this is a
scratch citation promoted to a row, not a fabrication — but a reader following the row would have
hit `Unknown constant`.  It exists now, at
`Lean4Lean/Verify/Typing/TrProjWideWitness.lean`, as a `TrProjG` (my new predicate), **not** as a
widened `TrProj`.  **[measured]**

### 2.2 "Every premise discharged outright at block index `j = 1`" (row 107a) is true of the ten
fields and **false** of option (d)'s eleven

`MutField.declEnv_trProjG_ten_fields` proves the ten unconditionally and **hole-free**;
`declEnv_trProjG` — the same instance *with* the eleventh field — needs `VEnv.WF declEnv` and
inherits both of wall 2's holes.  So option (d)'s cost is exactly identified: **the eleventh
field is what drags `VEnv.WF` and wall 2's hole cone into the construction site.**  Row 107a
predates option (d) being the plan, so it is not wrong about what it measured; it is wrong as a
description of what the *current* plan of record can discharge.  **[measured]**

### 2.3 "The eleventh field is discharged today" needs one qualifier, and it matters

Discharged **from `VEnv.WF env` and `OnCtx Γ (env.IsType U)`**, which is precisely what
`TrProj.wf` already demanded of its callers — so no consumer of `TrProj.wf` pays anything new.
But a caller that *cannot* supply `VEnv.WF env` (and today nobody can, at any `addInduct'`
environment — that is the keystone) faces the eleventh field as a **genuine extra hypothesis**.
Row 107e's flag — "if that hypothesis is false at some widened block, the widened `TrProj.wf` is
not merely unproved but false" — is **answered where `VEnv.WF` is available and open where it is
not**.  It is not answered unconditionally, and no wording in the ledger currently says so.

### 2.4 Outcome 1 of the brief was not reachable under my ownership, by construction

The brief's outcome 1 ("`TrProj` widened per option (d), consumers still building") requires
editing `TrProj`'s definition, which the same brief makes read-only to me.  I took outcome 2 and
**state the exact edit in §5 rather than making it**.

---

## 3. What the eleventh field costs the structural cluster — the measurement nobody had

Row 107c's "six structural lemmas widen and were compiled" was measured on a widening **without**
an eleventh field.  Under option (d) every structural lemma must also transport the target's
typing.  Two data points, both landed:

* **`mono` is free** — one extra `.mono`, `[propext, Quot.sound]`, hole-free.
* **`weak'` is not free but is available, hole-free, at `TrProj.weak'`'s own hypotheses**
  (`Ordered env` + `Ctx.Lift'`; **not** `VEnv.WF`, so the structural lemma is *not* forced to
  re-derive the typing).  The mechanism, since it is the reusable part: the target's type is
  `instAll (fieldᵢ.type.instL us) (ps ++ earlier projections)`, and `ProjClosedG.fields` pins
  that head `ClosedN (D.np + i)`, so `VExpr.lift'_instAll`
  (`Theory/Inductive/TelescopeLift.lean:175`) kills the lift on the head, while
  `projTermG_lift'` (`Verify/Typing/ProjGenLift.lean:289`) moves it through every spine entry.
  `weakN` is then one line.  **[measured]**

**Not attempted, and each is a real obligation for an in-place edit:** `instN`, `instL`,
`defeqDFC`, `defeqDFC_target`, `weak'_inv`, `uniq`, `noConstIn_of_spine`, and the three
`projDataCongr` bridges.  `instL`/`instN` should go the same way as `weak'` (`projTermG_instL`
and `projTermG_instN` both exist — `Verify/Typing/ProjGenInstWitness.lean` fires them); `uniq` is
row 107c's known casualty and I did not touch it.

---

## 4. Anti-vacuity, applied to this round's own output

Read §0 of `docs/vacuity-ledger.md` first, as instructed.

* **Firing test, not just a collapse test.**  `MutField.declEnv_trProjG` fires `TrProjG` at
  `MutField.decl` — two types, projected member at index **1**, one field — where
  `VEnv.IsStructure` is **false for every `T`, `C`** (`MutField.decl_not_isStructure`).
  `trProjG_fires_where_trProj_cannot` states the comparison in one theorem, including its honest
  limit: `TrProj` at the *name* `MutField.B` is not refuted outright, only shown to require some
  *other* block (`trProj_at_MutField_needs_other_block`), because `IsStructure` carries no claim
  that a name belongs to at most one block — ledger **G4**, which has no statement in the tree.
  So the widening is **strictly wider at the block**, and "wider at the name" waits on G4.
* **Which hypotheses survive, and their status.**
  * `VEnv.WF env` — **not discharged, and open for everybody**: nothing in this tree proves
    `VEnv.WF` of an `addInduct'` environment.  Re-measured myself rather than relayed from
    `docs/handoff-wall2.md`: over all of `Lean4Lean/`, `VEnv.WF` applied to a witness
    environment (`declEnv`, `barEnv`, `bazEnv`, `decl2Env`) occurs **only in binder position** —
    `ProjWfWitness.lean:68`, `ProjGenTermWitness.lean:29`, and my own five — never as a
    theorem's conclusion.  The nearest available facts are of the form `decl_WF : decl.WF
    VEnv.empty`, which is the *declaration's* well-formedness, not the environment's.
    `TrProj.wf`'s own witness `barEnv_TrProj_wf` takes the same hypothesis, so this is not a
    defect of the widening.  **[measured]**
  * Everything else at the firing — `IsStructureG`, `noRec`, the major premise's typing, three
    lengths, `i < fields.length`, `hus`, two `HasArgs`, F17 in its small-elimination branch — is
    **discharged outright**, and hole-free (`declEnv_trProjG_ten_fields`).
  * `TrProjG.toNarrow`'s `hsingle` (`every IsStructureG certificate for this name is an
    IsStructure certificate`) is **neither discharged nor proved inhabited**.  It is G4 in
    hypothesis form.  I flag it as such in its docstring and **do not** count it as evidence
    that the widening is faithful; direction 1 (`TrProj.toG`, fully discharged) carries that
    weight, and `barEnv_trProjG` fires it at a concrete narrow instance where the target term is
    the **unchanged** narrow `projTerm` (`trProjG_target_eq_projTerm`, hole-free).
* **Parameters quantified, not fixed.**  `TrProjG` quantifies `S, D, j, T, C, us, ps, ιs, Γ, e,
  i`; `env` and `U` are the relation's own `variable`s, exactly as for `TrProj`.  The witnesses
  necessarily fix them: `U = 0`, `Γ = bCtx`/`barCtx`, `us = ps = ιs = []`, `j = 1` (mutual) and
  `j = 0` (narrow), `i = 0` (mutual) and `i = 1` (narrow, over an *unused* field 0).
* **`#print axioms` on every headline result** — §0's table, read off the printout, not composed
  from paths.  Namespaces read off the files' own `namespace` lines: `Lean4Lean` and
  `Lean4Lean.MutField`.

---

## 5. The exact in-place edit, stated and NOT made

For the orchestrator to sequence.  File `Lean4Lean/Verify/Typing/Expr.lean`, the `inductive
TrProj` at line **82**, constructor `mk` at **83**, conclusion at **146**:

1. line 83: `| mk {S : Name} {D T C us ps ιs Γ e i} :` → add `j` to the implicit binders.
2. line 84: `env.IsStructure S D T C →` → `env.IsStructureG S D j T C →` **and** a new line
   `C.recFields = [] →` (keeping `noRec`; **do not** take row 107d ruling (iii)).
3. before line 146, the eleventh field, verbatim from `TrProjG`:
   `env.HasType U Γ (D.projTermG T C us ps ιs i j e) (VExpr.instAll ((C.fields.getD i default).type.instL us) (ps ++ (List.range i).map fun m => D.projTermG T C us ps ιs m j e)) →`
4. line 146: `TrProj Γ S i e (D.projTerm T C us ps ιs i e)` →
   `TrProj Γ S i e (D.projTermG T C us ps ιs i j e)`.

Ripple, measured from the compiled environment rather than by grep (an `#eval` walking every
declaration's value for a use of the constant `Lean4Lean.TrProj.mk`): **26 declarations use
`TrProj.mk`**, of which 6 are auto-generated `match_1_*` matchers, 2 are `casesOn`/`recOn`, and
2 are mine (`TrProj.toG`, `TrProjG.toNarrow`).  The **16 pre-existing hand-written** ones are
`TrProj.wf`, `.weak'`, `.instN`, `.instL`, `.mono`,
`.defeqDFC`, `.defeqDFC_target`, `.isStructure`, `.noConstIn_of_spine`,
`.uniq_of_projTermCongr`, `.weak'_inv_of_strengthen_onCtx`, `.weak'_inv_of_structStrengthen`,
`VEnv.ProjSpineCongr.projDataCongr`, `VEnv.ProjDataCongr.projTermCongr`,
`VEnv.ProjTypingAll.projDataCongr`, and `barEnv_TrProj`.  **206
declarations mention `TrProj` at all.**  **[measured]**

Of those 16, this round proves the transport for the pattern used by `mono`, `weak'`/`weakN` and
`wf`; `barEnv_TrProj` gains the eleventh field from `barEnv_trProjG`'s route; the rest are
unpriced.

---

## 6. What to pick up first

1. **Decide the in-place edit** (§5).  Everything needed to price it is now measured, and the
   two facts that were missing are: the eleventh field transports through `weak'` hole-free
   (§3), and it costs `VEnv.WF` at *construction* sites only (§2.2).
2. **`instN` / `instL` / `defeqDFC` transport**, in that order — the same `lift'_instAll` shape
   should work with `instAll`/`instL` commutation, and both `projTermG_instN` and
   `projTermG_instL` already exist.  Do this *before* the in-place edit, not after: it is the
   remaining unpriced part of the ripple.
3. **Do not re-derive `TrProjG.weak'`'s last bullet.**  The eleventh field's transport is 20
   lines of `lift'_instAll` + `List.map_congr_left` bookkeeping and is easy to redo badly.
4. **`uniq` is still row 107c's casualty** and nothing here changes that: the widened uniqueness
   must additionally conclude `j₁ = j₂`, which has no statement in the tree.
5. **Instrument blindness, flagged rather than fixed** (same as `docs/handoff-wall2.md` §5):
   both new modules are built by the `Lean4Lean.Verify.*` glob but **nothing imports them**, so
   any census that works from a fixed import list is blind to them.  Neither contains a `sorry`,
   so no census count moves either way.
