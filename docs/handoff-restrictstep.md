# Handoff: the restriction step at `SpineHargsK` — the hypothesis is still the consequence, and now provably so

**Written 2026-09-03.  WRITTEN INCREMENTALLY — earlier entries were true when written.**
One file, mine, new: `Lean4Lean/Verify/Inductive/RestrictStep.lean`.  Nothing else created or
edited.  Frozen files not read for editing, not written, not `touch`ed.

## 0. Status log (append-only)

* **entry 1** — read `RestrictCompanion.lean`, `ValAtPrice.lean`, both handoffs, plus
  `Theory/Typing/ConstSubst.lean` (`CSubst.WF`, `WF_of_hasType`), `Theory/Inductive/Restore.lean`
  (`csubstTy`, `tyVal`), `Theory/Inductive/RestoreBridge.lean` (`csubstTy_dom`, `csubstTy_eq_some`,
  `NoConsts.noCSubst`).  **Provisional answer, before any Lean: the hypothesis is still the
  consequence, and the three nodes form a CLOSED CYCLE rather than a sandwich.**  Reason:
  - `ArgsTypedK K e₁ occ → SpineHargsK K e₁ occ` — `SpineHargsK.of_argsTypedK`, free;
  - `SpineHargsK K e₁ occ → ValAt D K e₂ e₁` — `valAt_of_spineHargsK`, proved last round;
  - `ValAt D K e₂ e₁ + ArgsTypedK K e₂ occ → ArgsTypedK K e₁ occ` — `restrict_of_val`.
  So modulo the datum at `e₂` (which `D.WF` supplies) all three are **equivalent**, and the
  equivalence `ValAt → SpineHargsK` is obtained by going *forwards* through the restriction, i.e.
  **without `of_mkApp`** — which corrects `docs/handoff-valat.md` §2(a)'s "`ValAt → SpineHargsK` is
  `of_mkApp`" (true unconditionally; false in this configuration).
* **entry 2** — **§1 COMPILES, all hole-free.**  `RestrictStep.lean` §1: `RestrictStepCfg` (the
  shared side conditions, 11 fields), the three arrows (`cyc_datum_to_spine`, `cyc_spine_to_val`,
  `cyc_val_to_datum`), `restrictStep_cycle` (the three `↔`s), and `spineHargsK_of_valAt` (the
  `of_mkApp`-free converse).  10 declarations, every axiom line `[propext]` or
  `[propext, Quot.sound]`.  `lake build Lean4Lean.Verify.Inductive.RestrictStep` exit 0.
  Note the config's derived fields are free: `le₁` (`addConstList_le` on `stage₁`), `paramsIn` and
  `params₁` (from `D.WF.params` + `Ordered.constsIn`, via the new `ctxConstsIn_of_onCtx`),
  `argsFree` (from `argsNoK` + `csubstTy_eq_none`) — so the cycle's side conditions are ELEVEN
  facts about the staging and the block, none of them about the residual.
  **A `(kernel) invalid projection` was hit and fixed**: `OnCtx`'s head field is an `IsType`, i.e.
  an `Exists`, and `h.2.2` elaborates but does not kernel-check inside an equation-compiler
  definition; `obtain ⟨h1, u, h2⟩` fixes it.  Worth remembering: the bad version printed a
  `Lean4Lean.ctxConstsIn_of_onCtx._f` "axiom" on the `#print axioms` line, which is what exposed it.
* **entry 3** — **§2 COMPILES, 13 new declarations, all hole-free** (`[propext]` or
  `[propext, Quot.sound]`; 23 declarations in the file now).  **The answer to "route or circle" is:
  a circle, and its only entry is the strengthening hole — now machine-checked rather than argued.**
  Two nodes were added to §1's three, and neither is a judgement; both are *transports*:
  - `VInductDecl'.SpineStrengthen K e₂ e₁ occ` — the spine's `HasArgs` replays from `e₂` at `e₁`;
  - `VIndRestore.ValStrengthen D K e₂ e₁` — the one closed `HasType` replays from `e₂` at `e₁`.
  Both antecedents are **free**: `SpineHargsK.of_argsTypedK` on the datum at `e₂` for the first,
  and `valAt_e₂` (= `valAt_of_spineHargsK` run at `e := e₂` instead of `e₁`) for the second.  So
  `restrictStep_cycle₅` closes a **five-node** cycle, and `restrictStep_entry` is the punchline:
  `D.ArgsTypedK K e₁ occ ↔ R.ValStrengthen D K e₂ e₁` — *the entire residual is one
  constant-strengthening step, one closed `HasType` per companion member, across one
  `addConstList`.*  `valStrengthen_endpoints_clean` then shows **both endpoints of that judgement
  are already `e₁`-clean** (subject by `ValAtPrice.lean` §5's `tyVal_constsIn`, type by
  `WF.types_constsIn` + `le₁`), so node 5 is a **plain** instance of `VEnv.AxiomConservativityWF`
  with its side condition *discharged rather than assumed* — and that is `StrengtheningTarget`,
  `UniqueTyping.lean`'s recorded hole.  Because `restrictStep_entry` is an `↔`, no node of the
  cycle is a cheaper door: each one hands the strengthening instance straight back.
  Five config theorems were needed and are all free: `le₂`, `ordered₂` (`addIndTypes_ordered`),
  `params₂`, `ctxIn₂`, `paramsIn₁`.
* **entry 4** — **§3, §3a and §4 COMPILE; the config is now NINE fields, not eleven.**
  - **§4(a), machine-checked**: `occurs` and `argsNoK` were never side conditions —
    `occurs = Built.occurs.toOccurs`, `argsNoK = Built.kfresh.argsNoK` (guarded).  The *unguarded*
    quantifier the first version carried was an artefact of `ArgsTypedK.restrict_of_val`'s
    signature, whose `hargs` is unguarded although its body applies it only at guarded `j`;
    `cyc_val_to_datum` now inlines `ArgsTypedH.restrictC'` with the guarded form, and all of §1/§2
    re-elaborates over the nine-field structure unchanged.  *Note for `RestrictCompanion.lean`'s
    owner*: `restrict_of_val` can guard its `hargs` with no change to its body.
  - **§4(b)**: none of the nine is a typing at `e₁` — checked field by field (`Built`'s ten clauses
    are equations, an `OccursN`, an `OwnId`, a `Nodup` and a `KFresh`; no judgement).
  - **§4(c) — I was wrong, and so was entry 2**: `wf` is **not** residual-blind.  `D.WF`'s `ctors`
    clause is staged at `e₂` and `WF.recField_canonResult` turns it into the spine typing there; at
    the parameterised witness `ntreeAux_argsTypedK_of_wf` takes *only* the staging equation and
    produces the datum at `e₂` from `ntreeAux_WF'`.  So `wf + stage₂` already contains the
    residual's `e₂` shadow and `H₂` is barely an extra hypothesis — which is exactly why the gap is
    a strengthening step and nothing else.
  - **§3, inhabitation, closed**: `ntreeAux_restrictStepCfg_exists` — the nine fields **and** the
    datum at `e₂`, at the *parameterised* block (`ntreeAux`, `np = 1`, `uvars = 1`), nothing
    hypothesised.  `docs/handoff-valat.md` §4 flagged that witness as not instantiated; it is now.
    `ntreeAux_valStrengthen` adds the node-5 and node-4 instances there, and **§3a**
    (`ntreeAux_valStrengthen_nonvacuous`) shows the moved judgement is real:
    `ntreeVal : Type u → Type u`, at `e₂` *and* at `e₁`, with `_nested.List_1` in `csubstTy`'s
    domain and declared at `e₂`.  So node 5 is inhabited, not vacuous.
  - **Not shown, not claimed**: that the nine + `H₂` do *not* imply the residual.  That needs a
    separating witness and none is exhibited; `ValAtPrice.lean` §5 is evidence none exists.
* **entry 5 — verification record, end of round.**  `RestrictStep.lean`: 505 lines, **31
  declarations** (1 structure, 2 defs, 28 theorems), **28 `#print axioms` lines, every one
  `[propext]`, `[propext, Quot.sound]` or `+ Classical.choice` — no `sorryAx` anywhere**.  Names read
  off the file's own `namespace` lines.  `lake build Lean4Lean.Verify.Inductive.RestrictStep`: exit
  0, 200 jobs, **no warnings from my file**.  Full `lake build`: **1599 jobs, exit 0, zero `error:`
  lines** (earlier in the round the tree was red on `Theory/Inductive/IndexedWit.lean`, a concurrent
  stream's file, at two `omega` failures; it was green by the end.  `NestedRestoreWit.lean`'s
  missing `trSpine` field never appeared in my closure).  Census
  (`scripts/sorry-census-all.lean`): **13 holes**, `BUILT: 416`, **`NOT BUILT: 0`** — my file is in
  the population and adds none.  `scripts/dup-names.lean`: "no duplicate Lean4Lean declarations
  across the joined cone".  Guards: `guard 1 ✓ (24 frozen axioms)`,
  `guard 2 ✓ (whitelist; proof INCOMPLETE — sorryAx present, unchanged)`, `guard 3 ✓ (2/2)`.
  `automatically included section variable` warnings from Lean4Lean: **0** (the one on the log is
  `Foundation/FirstOrder/SetTheory/Z.lean`, upstream).  `of_mkApp`: **6 occurrences, all prose**, 0
  in code — the corner stays `PiInv`-free for a fifth round.  The flip was not made;
  `tryEtaStructCore.WF` / `isDefEqUnitLike.WF` untouched.  Frozen files not read for editing, not
  written, not `touch`ed; they do not appear in `git status`.  No state-changing `git`, no
  `lake update`, nothing sent outside the repo.
  **One lead checked and rejected** (so nobody repeats it): `VEnv.AllTypesInhabited.strengtheningTarget`
  (`Verify/Typing/ProjInhab.lean`) is *not* a cheaper entry — it needs `VEnv.WF env`, which is what
  this corner is deliberately avoiding (`HargsShared.lean` §8b's `PiInv` line), and
  `AllTypesInhabited` is false of any environment declaring an uninhabited type.
  **Open question this round leaves** (§2's caveat): is the node-5 instance family — empty context,
  one `addConstList` gap, `tyVal` subject, clean endpoints — *strictly weaker* than
  `AxiomConservativityWF`?  §3a discharges one instance with no hole at all, so pointwise it
  certainly is; whether the family has a general hole-free proof is the next question, and it is
  **not** the same question as the recorded hole.
