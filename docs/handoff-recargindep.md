# `VIndRecArg.exists_indep` — priced, split, half-closed, and its docstring corrected

Stream of 2026-09-03.  Owned files: `Lean4Lean/Theory/Inductive/RecArgIndep.lean` (new, 598
lines, **68 jobs**, builds green) and this file.  `Decl.lean` **was not touched**; nor were
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.

Verdict in one line: **not proved, not refuted; split into named halves, three of them closed
sorry-free; a second, previously unrecorded price found and proved to be sort uniqueness; the
statement shown to be under-strengthened for its own consumer, with the repaired statement
proved to do what the current one cannot; and the hole's own docstring shown to be wrong about
what needs repairing.**

---

## 0. Measurements (all measured by me, this session, after a full rebuild)

| quantity | value | how |
| --- | --- | --- |
| tree state at start | `lake build` green, **1550 jobs** | full build, commit `c69b40c` |
| holes in the tree | **13** | `lake env lean --run scripts/sorry-census-all.lean` |
| `exists_indep` transitive users, before this module | **0** | own reverse-reachability probe over the Guard+ConeJoin closure ∪ this module |
| `exists_indep` transitive users, after this module | **1**, and it is `VIndRecArg.indepGoal_of_exists_indep` — this file's *faithfulness check* | same probe |
| `exists_indep` direct deps | 39 (its statement's vocabulary + `sorryAx`) | same probe |
| my module's job count | **68** | `lake build Lean4Lean.Theory.Inductive.RecArgIndep` |
| my module in the census | **orphan** (nothing imports it), like `RigidConstPrice`/`SortPiDisjPrice` | census-all orphan list |

**Tree state at finish:** a full `lake build` reaches 1554/1555 and fails in
`Lean4Lean/Theory/Typing/PiDescendFstCod.lean:339` ("don't know how to synthesize implicit
argument `B`") — a concurrent stream's untracked file, not mine and not touched by me.  My
module builds green on its own (`lake build Lean4Lean.Theory.Inductive.RecArgIndep`,
68 jobs) and does not import it.

**Read the user count carefully.** It was 0 and is now 1 *because of an audit line I added on
purpose*: `indepGoal_of_exists_indep` applies the hole in order to machine-check that
`VIndRecArg.IndepGoal` is the hole's conclusion verbatim rather than a paraphrase.  It is the
only `sorryAx`-carrying declaration in my file and it carries it by construction.  A future
census reporting "`exists_indep`: 1 user" is reporting that line.  The substantive figure is
unchanged: **the hole blocks nothing that exists.**

Two instrument findings on the way, neither mine to fix:

1. **`lake build` reported success with a missing `.olean`.**
   `Lean4Lean/Verify/Environment/Boundaries.olean` did not exist while
   `Boundaries.olean.hash` and `Boundaries.trace` did, so lake considered it up to date and
   skipped it. `sorry-census-all.lean` then crashed (`object file … does not exist`) — the one
   census that takes its population from the filesystem is the one that dies on this, and a
   hole in such a module would be invisible to every other instrument while the build stayed
   green.  Fixed for the run by `lake build Lean4Lean.Verify.Environment.Boundaries` (160
   jobs); after that: 372 modules in population, 372 built, 0 unbuilt.
2. **`hasSorry` on a value is not `#print axioms`.** My first probe listed
   `VEnv.propLoop_sortUniq` as `sorry=false`; it is `WF.sortUniq' propLoopEnv_wf`, and
   `#print axioms` gives `[propext, sorryAx, Classical.choice, Quot.sound]`.  That is
   `docs/vacuity-ledger.md` §0 kind 3 (dropped qualifier) reproduced inside a probe I wrote in
   this session.  Every taint claim below is `#print axioms`.

---

## 1. What the hole says, and the two regimes

`VIndField.WF.binders_indep` requires `r.BindersIndep pre i`: no binder of `ξ` may mention an
earlier **recursive** field's variable.  `exists_indep` (`Decl.lean:561`) is the discharge
obligation — `ξ` may be replaced by a definitionally equal telescope that does not — under five
hypotheses: `pre.length = i`, `Γ` is field `i`'s context, `F.type : Sort F.lvl`, every binder is
block-free, and `F.type ≡ r.canonType D i` as types.

`BindersIndep` is non-vacuous exactly when **some earlier field is recursive and `ξ ≠ []`**.
That splits the obligation in two, and the split is the shape of this round's work.

## 2. Closed, sorry-free (`RecArgIndep.lean` §2–§3)

Drop-in replacements for the hole, each with its five hypotheses unchanged plus one extra:

| theorem | extra hypothesis | axioms |
| --- | --- | --- |
| `VIndRecArg.exists_indep_of_pre_norec` | `∀ F' ∈ pre, F'.recArg = none` | `[propext]` |
| `VIndRecArg.exists_indep_of_binders_nil` | `r.binders = []` | `[propext]` |
| `VIndRecArg.exists_indep_of_i_zero` | (none — `i = 0` and the hole's own `hlen`) | `[propext]` |

They are stated in a file I own, at `Lean4Lean/Theory/Inductive/RecArgIndep.lean:108/124/140`,
with the conclusion written out so substitution into `Decl.lean` is textual.  **Whether
substitution is worth doing is a different question — see §5, which argues the statement should
be replaced rather than proved.**  No forward-reference problem: `RecArgIndep.lean` imports
`Decl.lean`, so the material sits strictly downstream; an in-place substitution would need the
three `bindersIndep_of_*` lemmas moved into `Decl.lean` (they are 3–4 lines each and depend on
nothing outside it).

**These halves are degenerate and are labelled as such** (`RecArgIndep.lean` §7.1): the witness
is `r` itself, so nothing moves.  `docs/vacuity-ledger.md` rows 20–21 are the failure mode
being avoided.  Width of the degenerate regime, from `DeclExamples.lean`'s own theorems:
`accIntroRec_BindersIndep`, `forestCons_BindersIndep` and `wMk_BindersIndep` all land in it —
**no witness in the tree needs a binder to move.**

## 3. The second price, and it is new: sort uniqueness

`exists_indep`'s docstring names exactly one open input, `IsDefEqU.forallE_inv`.  There is a
second, and it bites on *any* proof that actually moves a binder:

> The caller has `F.type ≡ r.canonType D i` at some sort `u`.  A binder-wise congruence
> (`forallEDF`, iterated as `IsDefEq.mkPi_congrU`) delivers `r.canonType D i ≡ r'.canonType D i`
> at `.imax uB v`.  `VEnv.IsDefEq.trans` needs one type, not two.  Identifying them is
> `VEnv.SortUniq`.

Evidence, not assertion:

* **There is no `IsDefEqType.trans` in the tree.**  `Theory/Inductive/Lemmas.lean` §`IsDefEqType`
  has `toU`, `isType_l`, `isType_r`, `symm`, `instL`, `weak0`, `mono` — and no `trans`.
* `RecArgIndep.isDefEqType_trans_of_sortUniq` proves it **from `SortUniq`** (axioms
  `[propext, Quot.sound]`), which is where the charge is spent.
* `SortUniq` is a real restriction, not a triviality: `VEnv.sortUniq_badEnv`
  (`Theory/Typing/SortUniqDown.lean:88`) refutes it at `badEnv`, `[propext, Quot.sound]`,
  sorry-free.
* Every inhabitant of `SortUniq` in the tree is `sorryAx`-tainted, checked:
  `VEnv.WF.sortUniq'`, `VEnv.WF.sortUniq`, `VEnv.propLoop_sortUniq` — all
  `[propext, sorryAx, Classical.choice, Quot.sound]`.  So the second charge is against the
  injectivity family too, but at a **different node** from `forallE_inv`.
* `Decl.lean`'s own R3 note records this same obstruction for `VIndType.WF.canon` ("Composing
  the two needs those sorts to agree — i.e. sort uniqueness") **and does not connect it to this
  hole.**  Connecting them is a free correction to `Decl.lean`'s prose.

## 4. `TeleDefEq → IsDefEqCtx`: two things in the tree nobody had composed

`VEnv.TeleDefEq` (`Theory/Typing/ConstSubstNested.lean:148`) relates two telescopes entrywise;
`VEnv.IsDefEqCtx` (`Theory/Typing/Lemmas.lean:294`) relates two contexts and carries
`defeqDFC` for `IsDefEq`/`HasType`/`IsType`/`HasArgs`.  Nothing turned the first into the
second.  `RecArgIndep.teleDefEq_isDefEqCtx` does (`[propext]`), with
`OnCtx (As.reverse ++ Γ)` as the one extra input — needed because `TeleDefEq.rfl` deliberately
carries no typing.  `teleDefEq_length_eq` comes with it.

## 5. The statement is under-strengthened for its own consumer — with the repair proved

`exists_indep` exists to license one substitution: replace `r` by `r'` inside
`VIndField.WF.pos`'s `some` branch.  **Its conclusion does not license it.**  That branch has
nine conjuncts; three of them —

* `OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars)`,
* `HasType (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl)`,
* `∀ T', D.types[r.idx]? = some T' → HasArgs (r.binders.reverse ++ Γ) (liftTele …) r.args`

— live **in the binder telescope's context** and must be re-derived in the new one.  All the
conclusion hands back is `IsDefEqType Γ F.type (r'.canonType D i)`, and getting an entrywise
relation between the two telescopes out of a conversion between two `mkPi`s is
`IsDefEqU.forallE_inv` — the statement the hole is already waiting on.  **So even a proof of
`exists_indep` as stated would leave its consumer where it started.**

*(**[analysis, not proved]**: I do not show the three clauses are underivable from the
conclusion.  What is shown is that the natural derivation is pi-injectivity, and that carrying
a `TeleDefEq` instead makes all three free.)*

The repair, in `RecArgIndep.lean` §6:

```
def VIndRecArg.IndepUpgrade (env D Γ pre i r) : Prop :=
  ∃ bs, env.TeleDefEq D.uvars Γ r.binders bs ∧ (∀ B ∈ bs, D.NoBlock B) ∧
        (VIndRecArg.mk bs r.idx r.args).BindersIndep pre i
```

with, all sorry-free:

* `VIndField.PosSome` — `pos`'s `some` branch transcribed, and `VIndField.posSome_of_wf`
  machine-checks the transcription against `VIndField.WF` itself (so it is not a paraphrase);
* `RecArgIndep.posSome_transport` — `IndepUpgrade` transports the **whole** branch to `r'`
  (over `Ordered env`, `SortUniq`, `OnCtx Γ`).  This is the thing the obligation was for;
* `RecArgIndep.indepGoal_of_indepUpgrade` — `IndepUpgrade` implies the current conclusion, so
  it is a *strengthening*, not a different obligation;
* `RecArgIndep.indepUpgrade_of_bindersIndep` — `IndepUpgrade` is inhabited on §2's regime with
  `TeleDefEq.refl`, at no cost (ledger §0's "prove the hypothesis inhabited").

**Recommended edit to `Decl.lean`, for the orchestrator to sequence** (I did not make it):
replace `exists_indep`'s conclusion with `r.IndepUpgrade env D Γ pre i`.  It is strictly
stronger, strictly more useful, and it removes one of the two injectivity charges from the
*consumer* side (the `IsDefEqType` conjunct still costs `SortUniq`).

## 6. Where the hole's docstring is wrong

The docstring's argument is: *"every occurrence of `a` in a well-formed `B` sits under a redex
and disappears under `whnf`; the `(fun _ : T => Nat) r` example in `pos`'s `none`-branch comment
is the shape."*

**That shape is not an admissible binder.**  `T` is the earlier recursive field's type
`∀ ξ₀, I p π₀`, which mentions a block constant, so the redex does too — and `hbind` (a
hypothesis of the hole itself, and a conjunct of `pos`) requires binders to be **syntactically**
block-free.  Machine-checked at §7.2's block: `RecArgIndep.raiRedex_not_noBlock`
(`¬ raiD.NoBlock ((fun _ : I => Prop) x)`, by `decide`), together with
`raiRedex_betaHead : betaHead raiRedex = .sort .zero` confirming it really is the docstring's
redex.

Two caveats, both stated in the file:

* **[analysis, not proved]** the domain need not be `T` written out; any block-free type defeq
  to `T` would do, and whether one exists at the staged environment is a rigidity question, not
  a syntactic one.  So this refutes the docstring's *example*, not every redex route.
* "sits under a redex" is not exhaustive either: `raiB = raiP x` is block-free, well-typed,
  mentions `x`, and `betaHead raiB = raiB` (`raiB_betaHead`).

Also worth recording, **[analysis, not proved]**: `DeclExamples.wRecBad` (the tree's existing
`BindersIndep` control, `ξ = [.bvar 0]`) looks like it cannot be an instance of the hole's
premises — a binder must be a *type*, and `.bvar 0` there is a term of an inductive type, so
`hty` should fail — but ruling that out is `const_sort_inv`, which is open, so I did not prove
it.  Either way it is a data-level control; the premise-satisfying instance is §7.

## 7. The residual case is reachable — at a `VEnv.WF` environment

`RecArgIndep.lean` §7.2 builds `raiEnv` (two axioms: `raiI : Sort 1`, `raiP : raiI → Sort 1`),
a one-type block `raiD`, `pre = [raiF0]` with `raiF0` **genuinely recursive** (its stored type
*is* its canonical type, `raiF0_canon : rfl`), and a field 1 with `ξ = [raiP x]`:

* `RecArgIndep.rai_hyps` — `VEnv.WF raiEnv` **and all five hypotheses of the hole**;
* `RecArgIndep.not_bindersIndep_raiRec1` — `r` itself is **not** a witness there.

So the residual case is non-empty: on that instance any proof must produce a different
telescope.  §2's halves are not hiding the whole problem.

**The control, and it is the substantive finding.**  What makes the instance reachable is that
`raiEnv` declares a constant whose **type mentions the block**
(`raiCiP_type_hasBlock`, `hasConstB raiD.blockNames raiCiP.type = true`, by `decide`).  At the
environment `exists_indep` is applied in — the one `VEnv.addIndTypes` just produced — no such
constant can exist, because the block's constants were added last.  And the docstring's whole
justification is that *nothing in scope can eliminate an `I`*, which is a statement about that
environment.  **`exists_indep` has no hypothesis saying so.**  It also has no hypothesis that
`env` is `WF`, that `D` is `WF`, or that `pre`'s fields are `VIndField.WF` — and the docstring's
argument uses the last of those too (it rules out an earlier field of type `(∀ ξ₀, I p π₀) → Sort u`
by appealing to `pos`).

Control that the control is a control: `raiB_hasNoBlock` shows the binder itself *is* block-free,
so the instance is not excluded by `hbind`; and `raiF1_hasType` shows it is well-typed, so it is
not excluded by `hty`.

**[analysis, not proved]** whether the conclusion is actually *false* at `raiEnv`.  It would
follow from pi-injectivity plus rigidity of a constant spine, and both are open
(`Injectivity.lean`; `RigidConstPrice.lean`, where the three rigidity conjuncts are proved
*equivalent to* hole B).  Graded per the ledger: **candidate counterexample with a reachable
witness, not a refutation.**

## 8. Pick up first

1. **Make the `Decl.lean` edit** of §5 (conclusion → `IndepUpgrade`) — needs human sign-off since
   it is `Decl.lean`, but it is strictly a strengthening and it has a proved consumer
   (`posSome_transport`) and a proved inhabitant (`indepUpgrade_of_bindersIndep`).  Nothing
   depends on the hole, so the edit cannot break anything.
2. **Add the missing hypotheses** to the statement while editing it: `VEnv.WF env` (or the
   freshness condition "`env` declares nothing whose type mentions `D.blockNames`") and
   `VIndField.WF` for the fields of `pre`.  Without at least the first, §7's instance stands
   and the docstring's argument does not apply to the statement it justifies.
3. **The one route to a real refutation that does not go through the injectivity family**: a
   set-model soundness statement applicable to a two-axiom environment, interpreting `raiI` as a
   two-element set and `raiP` as a non-constant function, which would refute
   `IsDefEqU raiΓ raiB B'` directly.  **Not attempted this round.**  Everything in
   `Theory/SetModel/` I looked at is tied to `VEnv.WF` plus an oracle, so the question is
   whether the interpretation can be instantiated at a hand-built env at all.
4. **Do not price this hole as "blocked on `forallE_inv`" any more.**  It is blocked on
   `forallE_inv` *and* on `SortUniq`, at two independent points, and after §5 the second one is
   also charged to whoever *consumes* the conclusion.
5. If the goal is to make the clause disappear rather than to discharge it: the honest
   reformulation is **not** `∃ r'` at all but "`r.BindersIndep pre i` holds outright", which
   needs `const_sort_inv`-style rigidity instead of sort uniqueness and delivers `r' = r`, so
   `pos` transports for free.  §7.5's controls are evidence that the binder-movement story the
   `∃ r'` form was built for may not be the real one.

## 9. Where the brief was wrong

* *"its reverse-dependent count is not something I can quote to you reliably"* — it was
  quotable and correct in at least four places: `ORCHESTRATOR.md:725`,
  `docs/critical-path.md:309`, `scripts/kernel-sound-path.lean:22`,
  `docs/handoff-sortinv-route.md:304`, all **0**.  (`docs/handoff-injectivity.md:112` says
  something different and also true — the *forward* cone is empty.)  Measured again here and
  confirmed; the only thing that has ever changed it is my own audit line.
* *"The name suggests it asserts the existence of an independent recursor argument"* — flagged
  as a guess in the brief, and it is half right: `VIndRecArg` is a recursive **constructor
  field**, not a recursor argument, and what is existentially asserted is a replacement for its
  **binder telescope**.
* *"look for two things already in the tree that nobody had composed"* — this paid twice
  (§4: `TeleDefEq` × `IsDefEqCtx`; §5: `mkPi_congrU` × the caller's conversion, which is where
  the missing `IsDefEqType.trans` showed up).  It did **not** close the hole, and no composition
  can: the residual case is gated on the injectivity family at two nodes.
* The brief's guess that the recent `ResidualClean` / `OccursN` / `NestedNames` work might bear
  on `exists_indep`: **it does not**, as far as I can see.  `ResidualClean` is conditional on a
  uniform-occurrence trigger and `Decl.lean:519` already says it constrains neither `r.binders`
  nor a stored pi domain, precisely so as not to collide with this hole.

## 10. Anti-vacuity checklist

| requirement | this round |
| --- | --- |
| hypotheses discharged or inhabited | `pre`-norec / `binders = []` / `i = 0`: decidable, discharged at all `DeclExamples` witnesses. `SortUniq`: inhabited only through `sorryAx` (checked), **and refuted at `badEnv` sorry-free**, so it is a genuine charge and a genuine restriction. `IndepUpgrade`: inhabited free (`indepUpgrade_of_bindersIndep`). |
| existential witness checked for degeneracy | yes — §2's witness is `r` itself, said so in the file (§7.1) and here |
| smallest non-degenerate instance exhibited | yes — §7.2, at a `VEnv.WF` env, with `r` proved not to be a witness |
| negative control, shown to be a control | `raiRedex_not_noBlock` (the docstring's own shape is inadmissible) with `raiRedex_betaHead` showing it really is that shape; `raiB_hasNoBlock` + `raiF1_hasType` showing §7.2 is not excluded by `hbind`/`hty`; `sortUniq_badEnv` showing §3's hypothesis is not vacuous |
| `#print axioms` on every headline | yes, §8 of `RecArgIndep.lean`: 23 lines, one `sorryAx` and it is the labelled faithfulness check |
| qualified names read off the file's own `namespace` lines | yes (`Lean4Lean.VIndRecArg.*`, `Lean4Lean.VIndField.*`, `Lean4Lean.RecArgIndep.*`) |
| layering | `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` empty |
| duplicate names | `scripts/dup-names.lean`: "no duplicate Lean4Lean declarations across the joined cone" |
