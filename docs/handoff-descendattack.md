# Handoff: `NormalEq.descend` — attacked, found already refuted, branch-level closure added

Stream: `descendattack`.  Owns `Lean4Lean/Theory/Typing/DescendAttack.lean` and this file.
`ChurchRosser.lean` was read only, never edited.

## 0. Verdict up front

`Lean4Lean.VEnv.NormalEq.descend` (`Theory/Typing/ChurchRosser.lean`, `sorry`s at **2085,
2090, 2105** as of this commit) is **FALSE**, and was already machine-refuted before this
stream started, in `Theory/Typing/DescendRefute.lean`.  Nothing this stream could do would
make it true.  So there is **no edit to `ChurchRosser.lean` that replaces a `sorry` with a
proof**; the only correct edits are deletions/rewirings, listed in §6.

What this stream adds is the piece the prior refutation left as *prose*: the attribution of
each of the three `sorry`s to a witness, machine-checked, and the exact role of the induction
hypothesis in each branch.  See §4.

## 1. Timestamped measurement (a)

`scripts/users.lean`, run **2026-09-03 17:26 UTC**, population **425 built modules, 26013
non-internal declarations**:

| name | DIRECT | TRANSITIVE |
|---|---|---|
| `Lean4Lean.VEnv.NormalEq.descend` | **2** decls in **2** modules | **224** decls in **41** modules |
| `Lean4Lean.VEnv.NormalEq.appDF_extra_of_descend` | 1 decl in 1 module | 222 decls in 40 modules |

The brief's figure (2 direct / ~220 transitive in 40 modules) still holds; transitive has
grown 220 -> 224 and 40 -> 41 modules.  Prose elsewhere in the tree still says **193**
(`ChurchRosser.lean:1815`, `DescendRestate.lean:56`) — that figure is from `f4b32ea` and is
now an **undercount by 31**.  Do not requote it.

### The 2 direct consumers, and what each needs

1. **`Lean4Lean.VEnv.NormalEq.appDF_extra_of_descend`** (`ChurchRosser.lean:2201`) — the only
   *genuine* consumer.  All 222 transitive users pass through it, and it feeds
   `NormalEq.parRed` (`:2297`) and thence `IsDefEq.church_rosser` (`:2480`).  It calls
   `descend` once, on the **whole `.app` node** against the whole registered pattern
   (`ChurchRosser.lean:2282`).
   **What it actually needs: only the `q.NoApp` special case.**  That case is already proved
   and is *not* a hole: `KDescend.lean`'s `NormalEq.descendV` (arity 13, cone 3876) is
   `descend` + `q.NoApp`, its own value is not a hole, and `descend` is not in its cone.
   `Params.pat_app_noApp` (cone 133, `sorryAx`-free) shows `NoApp` is free at a registered
   pattern.  So **the highest-leverage thing the brief asked me to look for already exists**;
   see §6 for why it is nevertheless not wired in.
2. **`Lean4Lean.descendStatement_holds`** (`DescendRefute.lean`) — *not* a consumer of
   `descend`'s content.  It is the refutation's **anti-strawman check**: its body is literally
   `@VEnv.NormalEq.descend I`, which is what forces `DescendStatement` to be `descend`'s type
   on the nose.  It needs the **statement verbatim** and no special case retires it; it is
   *supposed* to break if `descend`'s statement drifts.  That is a feature: it means the
   refutation cannot go stale silently while the file compiles.

So: **one real consumer, needing one special case that is already proved.**

## 2. The obligation, stated honestly (b)

Unfolded, `descend` claims: for every `Γ`, every `q : Pattern`, every `g g'` with
`Γ ⊢ g ≡ₚ g'` (`NormalEq`) and `q.Matches g' n1 n2`, one of

* **(answer)** `∃ k`, `DescentLam k Γ q g g' n1 n2` — i.e. `g` **parallel-reduces** (`ParRedS`)
  to a term that matches *the same pattern* `q`, at level lists pointwise `≈` to `n1` (both
  lists `VLevel.WF`), with each matched argument `NormalEq` to the corresponding `n2 x`; or,
  at `k+1`, `g` reduces to a `.lam` carrying that answer one binder down against the
  eta-expansion `g'.lift.app (.bvar 0)`;
* **(proof escape)** `∃ P`, `Γ ⊢ P : .sort .zero` with both `g` and `g'` inhabiting `P`.

`sizeOf g ≤ N` plus the strong-recursion `N` is only the termination scaffold.

**Load-bearingness.**  `lean_minimal_hypotheses` cannot answer this (the brief is right: a
`sorry` body needs no binder, so it reports everything unused — I did not run it).  Measured
instead by **instantiation**: at `DescendRefute.refParams` every hypothesis of the statement
is *satisfied* at three separate witnesses and the conclusion still fails.  So the honest
answer is that **no hypothesis is load-bearing for truth** — the statement is false with all
of them discharged.  The two hypotheses that are load-bearing for the *refutation* are
`refEnv.SortUniq 0` and `refEnv.UniqTyping 0`, and only for the single step "the node is not a
proof" (`DescendRefute.refNotProof`).

## 3. Why it is false (c) — reused, not rediscovered

Root cause, one line: **`NormalEq` has two constructors `ParRed` does not** — `proofIrrel` and
`etaL`/`etaR`.  `ParRed` is `bvar, sort, const, app, lam, forallE, beta, extra`.  `descend`
asks a `NormalEq` to be pushed through to a *reduct*, so at exactly those two constructors it
asks for a reduction step the relation does not contain.  No hypothesis repairs that.

Three witnesses, all at `refEnv` (six axioms, **no defeq rules at all**), all in
`DescendRefute.lean`:

| witness | left `g` | right `g'` | pattern | `NormalEq` via |
|---|---|---|---|---|
| A | `C (bvar 0)` | `C D` | `.app (.const C) (.const D)` | `appDF refl (proofIrrel)` |
| B | `F (fun _ => E (bvar 0))` | `F E` | `.app (.const F) (.const E)` | `appDF refl (etaL)` |
| C | `(fun _ : P => C (bvar 1)) D` | `C D` | `.app (.const C) (.const D)` | `appDF (etaL …) refl` |

`refNoDescentOut{,2,3}` show `DescentOut` fails at each.  `not_descendStatement{,_etaArg,_etaFun}`
are `sorryAx`-**free** (arity 2, cone 6638), and `descend_uniq_sortUniq_not_all` (arity 0, cone
6640) is `sorryAx`-free and unconditional.  `descend` is **not** in either cone, so the
refutation is not circular.

(Status of the two side hypotheses is unchanged and is *not* settled — see
`DescendRefute.not_descendStatement_of_wf`'s docstring, which is careful about this.  I did not
improve on it.)

## 4. What this stream added: branch-level closure (`Theory/Typing/DescendAttack.lean`)

The prior refutation refutes the **statement**.  Its attribution of witnesses to individual
`sorry`s was *prose* ("Tracing `descend` on witness A: … the argument child's returns `.inr`"),
i.e. a claim about the proof that nothing checked.  That gap is real: a successor can ask "the
statement is false, but is *my* branch the false one?" and burn a round on the two branches the
refutation does not name.

`DescendAttack.lean` closes it.  For each of the three `sorry`s it states the branch's goal with
**every hypothesis in scope except the induction hypothesis**, and refutes that at the matching
witness — which means constructing the branch's own data at the exact eta depth that puts
`descend` in that branch:

| `sorry` | branch (goal-state case name) | statement | refuted by | new branch data |
|---|---|---|---|---|
| 2085 | `ind.appDF.app.inl.inl.succ` | `DescendBranchLocalEtaFun` | `not_descendBranchLocalEtaFun` | `refDescentLam_one_F3` (`Df` at depth 1, witness C) |
| 2090 | `ind.appDF.app.inl.inl.zero.succ` | `DescendBranchLocalEtaArg` | `not_descendBranchLocalEtaArg` | `refDescentLam_one_id` (`Da` at depth 1, witness B) |
| 2105 | `ind.appDF.app.inl.inr` | `DescendBranchLocalProofArg` | `not_descendBranchLocalProofArg` | the proof escape at witness A |

Plus:

* `descendBranchLocal*_of_descendStatement` — three anti-strawman bounds, so none of the three
  branch statements is stronger than the branch it names.
* `descendBranchesLocal_uniq_sortUniq_not_all` — the unconditional headline at branch
  granularity: axioms `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
* `DescendIH` + `descendIH_of_descendStatement` — `descend`'s induction hypothesis named, and
  bounded as a *weakening* of `DescendStatement`.
* `descendBranch{ProofArg,EtaArg,EtaFun}_iff_not_ih` — the residual, stated as an **`↔`**:
  with `IH` in scope, each branch goal at its witness is *equivalent to* `¬ IH`.  So closing any
  one `sorry` at that instance means refuting `descend`'s own induction hypothesis, which is
  refuting the statement again one size class lower.  There is no third option and no hypothesis
  that can be added.

**Deliberate ugliness, recorded at the statements (house style).**  `IH` is *omitted* from
`DescendBranchLocal…`.  That makes them stronger than the real goals, so refuting them shows
"no local argument closes this branch", not "the goal is false".  The omission must not be
"fixed": including `IH` makes the statement unrefutable **by construction**, because a
refutation would then have to *supply* `IH`, i.e. prove `descend` below size `N` at
`refParams` — a fragment of the statement already known false.  §3 of the file carries the
exact residual instead, which is why the `↔` lemmas exist.  `hszf`/`hsza` are omitted because
`descend` derives both from `hsz`.

### Cones (`scripts/exists.lean`, 2026-09-03 17:41 UTC, population 427 built modules)

| name | arity | cone | reaches `sorryAx` |
|---|---|---|---|
| `not_descendBranchLocalEtaFun` | 2 | 6648 | **no** |
| `not_descendBranchLocalEtaArg` | 2 | 6642 | **no** |
| `not_descendBranchLocalProofArg` | 2 | 6637 | **no** |
| `descendBranchesLocal_uniq_sortUniq_not_all` | 0 | 6687 | **no** |
| `descendBranch{ProofArg,EtaArg,EtaFun}_iff_not_ih` | 5 | 6630 / 6636 / 6640 | **no** |
| `refDescentLam_one_id` / `_one_F3` | 1 | 6567 / 6570 | **no** |
| `descendIH_of_descendStatement` | 3 | 679 | **no** |
| `descendBranchLocalEtaFun_of_descendStatement` | 2 | 686 | **no** |

`NormalEq.descend` is in **no** cone above (a hole in the cone would show as
`reaches sorryAx: true`), so nothing here is circular.  The file compiles with **zero
warnings**; `lake build Lean4Lean.Theory.Typing.DescendAttack` is green.

Elaboration trap worth one line, because it cost two iterations: two independently written
`nofun`s at `(Pattern.const c).Path` elaborate to **different** auxiliary matchers
(`refDescentLam_one_id.match_1` vs `Pattern.Matches.match_1`) and do not unify — the error
prints both types *identically*.  Fix: quantify over `{n2 : (Pattern.const c).Path → VExpr}`
rather than writing `nofun` in the statement.  Same for `DescentLam 1` vs `DescentLam (0+1)`,
which also do not unify.

## 5. A prose claim that overstates, corrected by measurement

`DescendRestate.lean:57-60` says `KSite7App.lean`'s `NormalEq.appDF_extra_of_descendVK` "is
that chokepoint's *unconditional* replacement (`hK` discharged by `ParRedK.hK`) and `descend`
is out of its cone", and concludes "the rewiring does drop the hole count by one".  Both halves
of the first clause are true; the word **"replacement" is not**, and read as licence to rewire
`ChurchRosser.lean` it is wrong on two counts, both checked:

1. **Different relation.**  `appDF_extra_of_descend` (`ChurchRosser.lean:2201`) is stated over
   `ParRed`/`ParRedS`; `appDF_extra_of_descendVK` (`KSite7App.lean:370`) is stated over
   `ParRedK`/`ParRedKS`.  It cannot be substituted into `NormalEq.parRed`, which is a `ParRed`
   induction.  The genuine drop-in — same relation, same conclusion, one extra hypothesis
   `hK : KStep → ParRed` — is `NormalEq.appDF_extra_of_descendV` (`KDescend.lean:209`, arity 25,
   cone 3991, holes `{forallE_inv_stratified, rigidShapeUniqNS}`, **no `descend`**), and its
   `hK` is *refuted* (`VEnv.not_hK_of_propMajor`, `ParRedPropRefute.lean:118`, cone 651, no
   `sorryAx`).  So at the `ParRed` level the descend-free route costs a refuted hypothesis, and
   at the `ParRedK` level it costs migrating the whole development.
2. **Wrong direction in the import graph.**  Measured import closures: `DescendRefute` (55
   modules), `KDescend` (59), `KSite7App` (64) and `ParRedPropRefute` (62) **all contain
   `ChurchRosser`**.  So no edit inside `ChurchRosser.lean` can call any of them.  The change is
   a *relocation* of `appDF_extra_of_descend`/`parRed`/`church_rosser` to a module downstream of
   `KSite7App`, not a rewiring in place.

Also: `DescendRestate.lean:48` cites `parRedKStatement_of_rows` with a cone of 4261.  That name
is **NOT FOUND** in the compiled population as written; the declaration is
`Lean4Lean.VEnv.…`-qualified (prose at `ParRedKGraded.lean:58` calls it
`KSite7Rows.parRedKStatement_of_rows`).  Requote it with a name `exists.lean` resolves.

## 6. The exact edits I would propose to `ChurchRosser.lean` — and why I made none

I own neither `ChurchRosser.lean` nor any frozen file, and I edited neither.  Stated exactly, as
required:

**There is no edit that replaces any of the three `sorry`s with a proof.**  All three goals are
false at a reachable instance; §4 pins each one individually.  Any patch that makes them
elaborate is either a change of statement or an appeal to a false hypothesis.

The two edits that *are* correct, in order of size:

* **Edit A (documentation only, safe, 3 lines).**  At `ChurchRosser.lean:1815-1818`, replace the
  transitive-user figure **193** with **224 declarations in 41 modules (`scripts/users.lean`,
  2026-09-03)**, and drop the parenthetical "206 users / 196 sole per `hole-rank.lean`" or
  re-measure it.  Same figure at `DescendRestate.lean:56`.  Nothing else in that paragraph needs
  to change; it is otherwise accurate and unusually careful.
  *This is the only edit I would recommend making today.*
* **Edit B (the real one, and it is not local).**  Delete `NormalEq.descend`,
  `NormalEq.appDF_extra_of_descend`, `NormalEq.parRed`, `NormalEq.parRedS` and
  `IsDefEq.church_rosser` from `ChurchRosser.lean` and re-land the last three in a module
  **downstream of `KSite7App`**, over `ParRedK`/`ParRedKS`, on
  `NormalEq.appDF_extra_of_descendVK`.  This is the only route that removes `descend` from the
  tree, and §5 says why it cannot be done as an in-place edit.  It is **blocked**, not merely
  unstarted: `VEnv.not_parRedStatement_of_propMajor` (`ParRedPropRefute.lean:83`, cone 673, no
  `sorryAx`) refutes `NormalEq.parRed`'s statement verbatim against the present `ParRed`, so the
  relocation has to be accompanied by route (2) of the `DescendRefute` inventory — giving
  `ParRed` the proof-replacement step — and `ParRedMissing.lean` reports that extension is
  cyclic.  Do not start Edit B expecting a hole-count win this round.

## 7. What I could not do, with reasons

* **Prove any of the three `sorry`s.**  Impossible: each goal is false (§4).
* **Discharge `refEnv.SortUniq 0` / `refEnv.UniqTyping 0`.**  Not attempted.  They are carried
  unchanged from `DescendRefute.lean`, whose docstring already lays out why the available
  derivations are not evidence of satisfiability (`piInvStratApp_iff_sortUniq` makes the obvious
  derivation assume what it checks).  I found nothing to add and did not want to restate it
  worse.  The unconditional results (`descend_uniq_sortUniq_not_all`,
  `descendBranchesLocal_uniq_sortUniq_not_all`) are the ones to quote.
* **Refute the branch goals *with* `IH` in scope.**  Impossible on purpose, and the reason is
  itself a result: doing so requires supplying `IH`, i.e. proving `descend` below size `N` at
  `refParams`.  §3 of the file states the exact residual as an `↔` instead.
* **Settle whether a `Params` condition on argument positions rescues the `.app` case.**  Not
  attempted.  Building the witness needs an environment with a registered ι-rule *and* a
  `Params` instance, and this tree has none; `DescendRefute.lean`'s argument that the natural
  condition is vacuous is analysis, not machine-checked, and I left it labelled as such rather
  than promoting it.
* **Run `lean_minimal_hypotheses` on `descend`.**  Deliberately not run: as the brief says, it
  drops a hypothesis and re-elaborates, and a `sorry` body needs none, so it reports everything
  unused.  Load-bearingness was measured by instantiation instead (§2 of this file).
* **Anything requiring the two co-occurring holes.**  `IsDefEqU.weakN_iff`,
  `IsDefEqU.forallE_inv_stratified` and `WF.rigidShapeUniqNS` appear in `descend`'s and its
  consumers' cones but in **none** of this stream's results (all `sorryAx`-free), so the
  residual here routes through **no** other hole.  For the record: `weakN_iff` is *incidental*
  to `descend` (it enters only through `parRed`, cone 4135, and `DescentLam.instN` explicitly
  avoids it via `NormalEq.instN₂`), while `forallE_inv_stratified` and `rigidShapeUniqNS` are
  *essential* to `descend`'s own cone (3874) — but not to its refutation.
