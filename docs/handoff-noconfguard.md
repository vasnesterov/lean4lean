# Handoff: the `¬ IsProof` no-confusion row is **TRUE**, and it was already in the tree

Round 13 of the `PiDescend`/injectivity-corner line.  One question, taken verbatim from
`docs/handoff-shapeindep.md` §7 item 1:

> **someone should check whether the `¬ IsProof` no-confusion row is even TRUE**;
> `Theory/Typing/ConstInvWitness.lean` is where dropping the guards is known to prove `False`,
> and is the right place to look for a refutation.

New file: `Lean4Lean/Verify/Typing/NoConfGuard.lean` (under `Verify/`, because the question needs
`Verify/Typing/ConstSpine.lean` and `Theory/Typing/ShapeIndep.lean` at once).  No other file
touched.

## 0. Verdict

**True.  And the round's premise is false: the tree already had the `¬ IsProof` form.**

`docs/handoff-shapeindep.md` §3 states, in bold,

> the tree's own `ConstNoConf` uses `IsType` too, so **nothing in the tree has the `¬ IsProof`
> form of constant no-confusion**

That is wrong, and the counter-example is one level under the name it checked.
`VEnv.IsDefEq.constApp_inv` (`Verify/Typing/ConstSpine.lean:248`) is the `Params`-level statement
that proves **both** (B) injectivity and (D) no-confusion, and its side condition is

```lean
    (hnp : ¬ IsProof env univs Γ ((VExpr.const c ls).mkApp as))
```

with its own docstring explaining the choice: "The `¬IsProof` side condition is exactly
`const_app_inv`'s, for the same reason: it is what blocks the `proofIrrel` constructor, and it
propagates down the spine by `IsProof.app'` **where `IsType` would not**."  The `IsType` guard
enters one level *above*, in the `VEnv`-facing wrapper `VEnv.constApp_inv_of_patWF`
(`ConstSpine.lean:579`), whose last argument is literally `IsType.not_isProof henv hΓ hty`.

So the "guard gap" is a **wrapper**, not a gap.  Going under the wrapper gives the row:

| statement | file | status |
| --- | --- | --- |
| `ConstNoConfNP` | this file | `ConstNoConf` with `IsType` replaced by `¬ IsProof`, nothing else changed |
| `constNoConfNP_of_patWF` | this file | **theorem**, modulo `PatWF`, same proof as the wrapper minus the conversion |
| `constNoConfNP_of_wf` | this file | **theorem** at every `VEnv.WF` environment (`patWF_of_wf`) |
| `RigidConstNoConfNP`, `rigidConstNoConfNP_of_wf` | this file | the same in `ShapeIndep.lean`'s vocabulary |

Two consequences the corner should record.

* **Brief outcome 1 is unreachable, provably.**  `not_wf_of_guardSeparated`: any environment at
  which the `IsType` form holds and the `¬ IsProof` form fails is **not** `VEnv.WF`.  So no
  refutation of this row exists at a well-formed environment, and any witness is a *control* in
  `RigidConstPrice.lean` §5's sense.  This is the precise sense in which the row is settled.
* **The strengthening target is not needed for this row.**  `ConstVar.axiomConservativityWF_iff_target`
  was named in `handoff-shapeindep.md` §3 as what "turning the guard round" costs.  For the
  *no-confusion fact* it costs nothing at all — the fact is proved with the `¬ IsProof` guard
  directly.  For the *row as `SpineVar.lean` states it* the guard-transport problem survives; see
  §4, which is where that handoff conflated two things.

## 1. The refutation attempt, done first, and how far it gets

Per the brief, refutation before proof.  `ConstInvWitness.lean`'s **W2** is one head applied to
two arguments (`mkP A ≡ mkP B`, by `proofIrrel`, in an environment with *no rules*).
No-confusion needs two heads, so §1 of the new file adds a **second axiom of `mkP`'s own type**:

```
  P : Prop        mkP : Type 0 → P        mkQ : Type 0 → P        (no δ-rules at all)
```

and `proofIrrel` then identifies two **distinct** rule-free constant spines,
`mkP Prop ≡ mkQ (Prop → Prop)`.  This is sharper than W2 in three ways, all machine-checked:

* the environment is built from `VEnv.empty` by three `.axiom` steps and **is `VEnv.WF`**
  (`wf_ncPropEnv`, `[propext, Classical.choice, Quot.sound]`) — a hard constraint, not a control;
* the spines are **non-empty**, and their arguments are W2's own non-convertible pair;
* so `not_constNoConfUG_ncPropEnv`: **constant no-confusion with both guards deleted is false at
  a well-formed environment.**  Hole-free.

And then it stops.  `isProof_ncPropEnv_lhs` proves the left spine **is** a proof, so the
`¬ IsProof` guard excludes the witness; `not_isType_ncPropEnv_lhs` proves it is not a type
either (tainted — the only route from "is a proof" to "is not a type" is `IsType.not_isProof`).
`ncPropEnv_guards_fail_together` packages both: at this witness **the two guards fail together**,
which is why it separates nothing.

That is not an accident of the construction.  `proofIrrel` is the only rule of `VEnv.IsDefEq`
that relates two spines with *distinct* constant heads without a δ/ι-rule, and its left endpoint
is a proof by construction.  A separating witness therefore needs a spine that is neither a proof
nor a type, which needs a δ-rule chain `c ≡ hub ≡ c'` — two rules on one constant, excluded at
every `VEnv.WF` environment by `DeltaUnique.WF.defEqHeadsUnique` — **and** a `¬ IsProof` fact at
a non-type, on which see §5.

## 2. The guard *bridge* is hole-free, and it is not hole A

`ConstNoConfNP.constNoConf` (the `¬ IsProof` form implies the `IsType` form) pays
`IsType.not_isProof`, whose cone is `IsDefEqU.forallE_inv_stratified` — hole A.  **It need not
pay that.**

`not_isProof_of_hasType_sort` (this file) proves "a type is not a proof" from
`SortInvIndep.PropAgreeOn` instead of from `WF.sortUniq'`, in four lines, cone **600, no holes,
`[propext]` only** — the cleanest print in the file.  Hence
`ConstNoConfNP.constNoConf_of_propAgreeOn`, cone 2138, **hole-free**.

The tree had this argument twice, both times narrower: `SortInvIndep.sortNotProof_of_propAgreeOn`
(the term must be a **sort**) and `SpineVarVacuity.spineVar_not_isProof_of_propAgreeOn` (one
fixed witness).  The general statement — `IsType.not_isProof` with `PropAgreeOn` in place of
universe uniqueness — was missing and is worth reusing: **every `¬ IsProof` guard in this corner
that is currently discharged through `IsType.not_isProof` can be discharged through `PropAgreeOn`
instead, and stop importing hole A.**  Candidates read off the grep in §5:
`SpineVarVacuity.spineVar_not_isProof`, `ShapeVar.lean`'s §10 discharges,
`Verify/Typing/ConstSpine.lean`'s two `IsType.not_isProof` calls (not this stream's to edit).

## 3. Anti-vacuity, instantiated rather than admired

`docs/vacuity-ledger.md` §0, in order.

* **Midpoint restriction?  No, structurally.**  Nothing here opens or constrains a conversion
  derivation: §1 is three `.axiom` steps plus one `proofIrrel`; §2 re-applies an existing
  theorem with one argument removed.  Not the twelfth collapse.
* **The guarded row fires at the refuting environment.**  `ncPropEnv_P_ne_mkP_spine`: at
  `ncPropEnv` — the *same* environment that refutes the unguarded row — every premise of
  `ConstNoConfNP` is discharged for **every** level list and argument list, and the conclusion is
  a real negative fact: `P` is not definitionally equal to any `mkP`-headed spine, at the very
  environment where `mkP` and `mkQ` *are* confused.  `ncPropEnv_P_not_isProof_of_propAgreeOn`
  gives the guard hole-free modulo `PropAgreeOn`; `ncPropEnv_P_not_isProof` gives it
  unconditionally but tainted.  Both recorded, neither assumed.
* **Inhabitation and hole-freeness, separately.**  `wf_ncPropEnv` is `VEnv.WF` — an inhabitation
  claim, hole-free.  `constNoConfNP_of_wf` is *not* hole-free (four holes, §6).  `ncPropEnv` is
  **consistent as far as this file goes and no further**: it declares one propositional axiom
  `P : Prop` and two inhabitants of it, so `P` is inhabited there by construction; nothing here
  claims or needs anything about other propositions.  Disclosed separately, per the standing rule
  about `svEnv`.
* **A hypothesis can be inert.**  `constNoConf_iff_constNoConfNP_over_wf` is stated **in order to
  be dismissed**: over `VEnv.WF` both sides are theorems, so the equivalence measures nothing —
  exactly the trap `ShapeIndep.rowsFromBridge_iff_rows` fell into for `RigidShapeUniq`.  The
  comparison with content is at a *fixed* environment, and there the two guards are
  **incomparable**: `¬ IsProof` admits data terms that `IsType` rejects, and `IsType` admits
  types that are not known non-proofs without §2's node.

## 4. Where `docs/handoff-shapeindep.md` — and this round — is wrong

1. **"Nothing in the tree has the `¬ IsProof` form of constant no-confusion."**  False; see §0.
   The check that would have caught it is one the corner already has a rule for: the handoff
   inspected `VEnv.ConstNoConf`'s *definition* and `RigidConstAppInv`'s *definition* and compared
   guards, without following `ConstNoConf`'s **supply**.  A guard on a wrapper is not a guard on
   a fact.
2. **`RigidConstAppInv` and `ConstNoConf` do not "sit on opposite sides of the guard".**  Both
   sides of the `¬ IsProof` / `IsType` split are supplied by the *same* theorem,
   `IsDefEq.constApp_inv`: its `.1` is (D), its `.2` is (B), and the guard it takes is
   `¬ IsProof`.  `rigidConstAppInv_of_wf` (this file) is that `.2`.
3. **The residue of rounds 10–12 was reported as one statement; it is two.**  (a) the
   no-confusion *fact* with a `¬ IsProof` guard — settled here; (b) `SpineVarAppDisj`'s guard,
   which sits on the **variable** side and has to *travel* through `axiomize_step`'s
   substitution.  (b) is still open and is still the `ConstVar` conservativity direction: pushing
   a judgement up moves `IsProof` forwards and `¬ IsProof` backwards, and swapping the endpoints
   with `IsDefEqU.symm` does not help, because `¬ IsProof` is antitone in the environment while
   `axiomize_step` grows it.  §0's second bullet should be read as narrowly as it is written.
4. **My own draft §5 first claimed the `¬ IsProof` guard could only be inhabited via
   `IsType.not_isProof`, hence hole A.**  False — `PropAgreeOn` does it hole-free (§2), and
   `SpineVarVacuity.lean` already had the special case.  Caught by grepping the tree for `¬ …
   IsProof` before writing the claim, which is what the ABSENCE rule asks for and what would
   have caught item 1 as well.
5. **`RigidConstPrice.lean` §6.1's "smallest open instance in this corner" is not open.**  §6 of
   the new file proves all three constant conjuncts at every `VEnv.WF` environment and
   instantiates at `rcEnv0`, that file's own witness (`constFamily_at_rcEnv0`,
   `rcEnv0_spine_ne_prop`: `rcRF.{0} ≉ Prop` there).  **This is not progress** — see §6 below —
   but the item should not be picked up as open.

## 5. The one thing not obtained, stated as a target

**A separating witness**: `GuardSeparated env U := env.ConstNoConf U ∧ ¬ env.ConstNoConfNP U`.
Not built.  What is proved about it:

* `not_wf_of_guardSeparated` — it forces `¬ env.WF`, so it can only ever be a control.
* It needs a `¬ IsProof` fact at a spine that is **typeable but not a type**.  Every route to
  `¬ IsProof` in the tree concludes it from the term being (or being convertible with) a type:
  `IsType.not_isProof`, `not_isProof_of_sort'`, `not_isProof_of_forallE'`, `sort_not_proof`,
  `forallE_not_proof`, `sortNotProof_of_propAgreeOn`, and `not_isProof_of_hasType_sort` added
  here; `IsProof.app'` propagates one but does not create it.  **ABSENCE claim, scoped:** the
  population is the 22 files that mention a negated `IsProof` anywhere (textual grep over
  `Lean4Lean/**/*.lean`, 226 matching lines, on disk 2026-09-03), and the compiled population is the
  import closure of `Verify/Typing/NoConfGuard.lean` (7 500-odd constants); I did **not** scan
  the other 400-module passes' constants for this, so read it as "no route of a different shape
  is visible in the corner's files", not as "none exists in the tree".
* So a separating witness needs a *new* kind of negative typing fact, at a rogue environment,
  plus a δ-hub chain `c ≡ hub ≡ c'`.  Both halves are new work, and the payoff is a control.
  **I would not sequence it.**

## 6. Measurements

* `lake build Lean4Lean.Verify.Typing.NoConfGuard`: **125 jobs**, green.
* `lake build` (whole tree): **fails in `Lean4Lean/Theory/Inductive/RecTyped.lean`** (lines 883
  and 998), which is a **concurrent stream's** file, not mine — `TeleMove2*`, `TeleCongr.lean`,
  `CtorBeta.lean`, `RecTyped.lean` are that stream's.  Nothing of mine is in that closure.
* `lake env lean --run scripts/sorry-census-all.lean` **crashes** while that module has no
  `.olean` (`importModules` throws on a stale importer).  Run instead from a `/tmp` copy that
  drops the unbuilt modules' reverse closure (`/tmp/census-skip.lean`, olean-header import graph
  rather than the textual one, which is lossy — it stops at the first comment line):
  **13 holes**, unchanged; `on disk 428; population 404; BUILT 403; NOT BUILT 1`; pass A 400,
  pass B 3; 34 orphans, of which this file is one (a leaf).  **This round adds no hole.**
* Layering: `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` → **empty**.
* `scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined cone".
* `grep -c "automatically included section variable"` over the (partial) build log: **18**, and
  **0** from this file.  The full-tree count is not obtainable while `RecTyped` is broken.
* Frozen files `Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`: not read for
  edit, not edited, not `touch`ed.  `ShapeIndep*.lean`, `SpineVar*.lean`, `ShapeVar.lean`,
  `Injectivity.lean`, `InjOneFact.lean`, `RigidConstPrice.lean`, `RigidNodeCircle.lean`,
  `ConstInvWitness.lean`, `Verify/Typing/ConstSpine*.lean`, `Verify/Typing/Rigidity.lean`:
  **unmodified** (imported only).  `scripts/` unmodified.
* Hole cones (`/tmp/noconf-cone.lean`, `allowOpaque := true`, transitive over type and value):

| seed | cone | holes in cone |
| --- | --- | --- |
| `not_isProof_of_hasType_sort` | 600 | none |
| `ConstNoConfNP.constNoConf_of_propAgreeOn` | 2138 | none |
| `isProof_ncPropEnv_lhs` | 3575 | none |
| `ncPropEnv_link` | 3585 | none |
| `wf_ncPropEnv` | 3586 | none |
| `not_constNoConfUG_ncPropEnv` | 3600 | none |
| `IsType.not_isProof` | 3456 | `forallE_inv_stratified` |
| `ConstNoConfNP.constNoConf` | 3464 | `forallE_inv_stratified` |
| `not_isType_ncPropEnv_lhs` | 5180 | `forallE_inv_stratified` |
| `IsDefEq.constApp_inv` (tree) | 4446 | `weakN_iff`, `forallE_inv_stratified`, `WF.rigidShapeUniqNS`, `NormalEq.descend` |
| `constApp_inv_np_of_patWF` | 7328 | the same four |
| `constApp_inv_of_patWF` (tree) | 7329 | the same four |
| `constNoConfNP_of_patWF` | 7329 | the same four |
| `constNoConf_of_patWF` (tree) | 7331 | the same four |
| `constNoConfNP_of_wf` | 7491 | the same four |
| `constNoConf_of_wf` (tree) | 7493 | the same four |
| `rigidConstNoConfNP_of_wf` | 7493 | the same four |
| `rigidConstNoConf_of_wf` | 7496 | the same four |
| `spineVarAppDisjT_wf` | 7634 | the same four |
| `constFamily_of_wf` / `constFamily_at_rcEnv0` | 7517 / 7526 | the same four |

Three readings, in order of how much they change:

1. **The `¬ IsProof` form is two constants *cheaper* than the `IsType` form, with an identical
   hole set** (7491 vs 7493; 7329 vs 7331).  The difference is exactly the `IsType.not_isProof`
   application.  The guard was never a strength question: the `IsType` form *is* the `¬ IsProof`
   form plus a paid conversion.
2. **`WF.rigidShapeUniqNS` — hole B — is in the cone of everything routed through
   `church_rosser`.**  That is the machine-checked form of `RigidNodeCircle.lean`'s "circular"
   annotation, and it is why §6 of the file closes `RigidConstPrice.lean` §6.1's instance
   **through its own target**.  Do not feed `rigidConstNoConf_of_wf` or `constFamily_of_wf` back
   into the bridge; the open item there is a route whose cone does *not* contain hole B, i.e.
   `RigidNodeCircle.lean` §5's untouched `PatWF` re-derivation.
3. **Hole-freeness is not discharge, and the two are on different objects here.**  The guard
   *bridge* is hole-free; the *row* carries four holes.  `handoff-shapeindep.md` §3 ran those
   together.

## 7. What to pick up first

1. **`SpineVarAppDisj`'s own guard** (§4 item 3) — the *only* surviving residue of rounds 10–13.
   It is a guard-transport question about `axiomize_step`, not a question about no-confusion, and
   the two should never again be reported as one item.  Note before starting: any route through
   `church_rosser` will have hole B in its cone, so a discharge of that row is worth having as
   *vocabulary* and is worthless as *supply* to the bridge.
2. **Retire hole A from every `¬ IsProof` discharge in the corner**, using
   `not_isProof_of_hasType_sort` (§2).  Cheap, mechanical, and it shrinks several cones that
   currently import `forallE_inv_stratified` for no reason.  `SpineVarVacuity.spineVar_not_isProof`
   is the model: that file already carries both routes side by side and says why.
3. **Do not look for a separating witness** (§5).  It is provably non-`VEnv.WF`, i.e. a control,
   and it needs two new pieces of machinery to build one.
4. **`RigidConstPrice.lean` §6.1 should be re-marked**: closed, circularly.  Its "smallest open
   instance" wording will otherwise cost someone a round.
