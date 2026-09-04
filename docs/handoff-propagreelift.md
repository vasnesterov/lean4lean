# Handoff — `PropAgreeLift`: can `propTypeAgreeOnCtx_of_stratifiedN` be lifted to `Theory/Typing`, and does it buy anything?

Stream owns exactly `Lean4Lean/Theory/Typing/PropAgreeLift.lean` and this file.
Everything else read-only. `Verify/{Soundness,Axioms,Guard}.lean` frozen and untouched.

Task, in one line: the hole audit (`docs/audit-hole-producers.md` §2.3) named exactly one
"genuinely under-explored move" — migrating
`Lean4Lean.SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` (arity 4, cone 2703,
`sorryAx`-free per the orchestrator's own re-measurement) up out of `Theory/SetModel` into
`Theory/Typing`, so that `Theory/Typing/Injectivity.lean` (home of holes #5 and #8) could cite it.
Step 0 is two measurements that decide whether the round has a subject at all.

---

## §1 PRIORS  (written before any Lean tool ran; NEVER edited — all corrections go in §2)

### §1.a Claims I was handed, and which of them I will verify rather than trust

| # | claim | whose | trust? |
|---|-------|-------|--------|
| P1 | `propTypeAgreeOnCtx_of_stratifiedN` "uses only `Theory/Typing` names (`stratifyN`, `PropTypeAgreeN`, `PropUniqN`, `equivZero_iff_eval_zero`)" | **the audit stream's, explicitly unverified by the orchestrator** | VERIFY FIRST — this is the single load-bearing claim of the round |
| P2 | it is arity 4, cone 2703, hole-free, no `sorryAx` | orchestrator, re-measured | verify cheaply (`exists.lean`), it is one command |
| P3 | `SetModel` is downstream of every `Theory/Typing` module, so `Injectivity` cannot cite it today | audit M6 | verify with `layer-check.py` / import closures |
| P4 | `PropAgreeOn` is proved in-tree **too weak** to deliver `SortUniq` (`SortInvIndep.lean` §-header: gives `u.eval ls = 0 ↔ u'.eval ls = 0`, never `u ≈ u'`) | audit §2.2 | VERIFY by reading the actual in-tree proof and quoting it |
| P5 | the two `∀ n` hypotheses (`∀ n, PropTypeAgreeN 0 n`, `∀ n, PropUniqN 0 n`) are open, only `n = 0` instances are theorems (`propUniqN_zero`, `propTypeAgreeN_zero`) | audit M5/§2.3 | verify — decides whether a lifted lemma is a producer or a conditional |
| P6 | `sortPiDisjUC_iff_rigidShapeUniqNS` and `shapeMidShapeless_iff` are genuine `↔`s, making every cheap #5/#8 producer a restatement | audit §2.5/§2.2 | verify the two `iff`s exist with those names |

### §1.b My own numbered predictions, with probabilities

| # | prediction | P |
|---|-----------|---|
| Q1 | P1 is **true**: the statement and proof of `propTypeAgreeOnCtx_of_stratifiedN` mention no `SetModel`/ZFC/Foundation name | 0.45 |
| Q2 | `Theory/Typing/Injectivity.lean` **cannot** cite a declaration in my new file, because the modules defining `PropTypeAgreeN`/`PropUniqN`/`stratifyN` (`PropConv.lean`, `PropShadow.lean`, or similar) themselves import `Injectivity` — i.e. the lift lands *downstream* of the hole, exactly like several rounds this week | 0.75 |
| Q3 | the re-proof, if it goes through at the `Theory/Typing` layer, has a **strictly smaller** cone than 2703 (dropping the `SetModel` prelude it inherited by position) | 0.7 |
| Q4 | the re-proof needs no new mathematics — a verbatim copy of the original proof term/tactic script compiles once the imports are right | 0.6 |
| Q5 | the lift supplies **nothing new** to holes #5/#8: what it produces is `PropAgreeOn`, which is exactly the ingredient the tree already proves too weak for `SortUniq`, so it hits the P4 wall | 0.85 |
| Q6 | even citable, the lifted lemma is **not a producer** — it stays conditional on two open `∀ n` statements — so the honest verdict is "the layer rule was not the obstruction" | 0.8 |
| Q7 | at least one in-tree docstring or comment I read while doing this commits the "open"/"is-a-hole" conflation that method rule 5 warns about | 0.35 |
| Q8 | I will find a *field of a structure in scope* that a previous round called absent (the usual miss per method rule 3) | 0.15 |
| Q9 | `python3 scripts/layer-check.py` passes on my new file with no new `Theory→Verify` edge | 0.9 |
| Q10 | the round ends with a **negative** headline (lift possible but useless, or lift impossible) rather than a discharged hole | 0.9 |

Prior tally in one sentence: I expect the lift to be *mathematically* fine and *strategically*
worthless — either uncitable from `Injectivity` (Q2) or citable but stalled at the same
`PropAgreeOn`-is-too-weak wall (Q5/Q6).

---

## §2 MEASUREMENTS  (append-only, in order; each row lands before the next tool runs)

### M1 — the declaration, read (`Theory/SetModel/PropAgreeWall.lean:133-155`)

Statement, verbatim:

```lean
theorem propTypeAgreeOnCtx_of_stratifiedN (henv : VEnv.Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n) :
    env.PropTypeAgreeOnCtx 0
```

Proof uses exactly: `equivZero_iff_eval_zero`, `VEnv.HasType.stratifyN`, `VLevel.equiv_def`,
`VEnv.HasTypeN.mono`, `.conv`, `.sortDF`, plus `pta`/`pun`. **Verdict on P1/Q1: the audit's claim
is essentially right** — every name is `Theory/Typing`-flavoured *except* `equivZero_iff_eval_zero`,
which is `SetModel/PreludeOracle.equivZero_iff_eval_zero` (model cone). So Q1 as I stated it
("mentions no SetModel name") is **WRONG**: one name is a SetModel name. It is, however,
a pure `VLevel` fact with no model content.

### M2 — **THE ROUND'S SUBJECT ALREADY EXISTS.** `Lean4Lean/Theory/Typing/PropAgreeGuarded.lean`

Found by `grep -rn propTypeAgreeOnCtx_of_stratifiedN`, not by the audit. That file's module
docstring §3 is titled **"Route B's hypotheses can carry the `OnCtx` guard — a genuine
weakening"** and says, verbatim:

> `propTypeAgreeOnCtx_of_stratifiedN`'s conclusion is `OnCtx`-guarded and its proof has the guard
> in hand at the point where it applies `pta` and `pun`; it just does not use it. §3 restates
> route B with the guard pushed onto its two hypotheses (`PropTypeAgreeNOn`, `PropUniqNOn`),
> which is strictly less to prove … The conclusion is `SortInvIndep.PropAgreeOn`.

It even carries **local copies of the one SetModel name M1 found**:
`Lean4Lean.VLevel.eval_indep_of_wf_zero` and `Lean4Lean.VLevel.equivZero_iff_eval_zero'`,
each with the comment "A local copy of `SetModel/PreludeOracle…`; that file is in the model cone,
which `Theory/Typing` must not import."

So the migration the audit calls "the one genuinely under-explored move I found" was **already
performed, in a stronger form (guarded hypotheses), before the audit was written**. The audit
missed it. This is a stale-absence-shaped miss of the kind method rule 3 exists to catch, and it
lands against *the audit*, not against me — I record it as such.

Consequence for the round: task item 1 ("re-prove it at the `Theory/Typing` layer") is
**already done in-tree**. Re-doing it in my file would be pure duplication, which the
"instantiate, don't admire" rule forbids. The round therefore becomes: **is the existing lift
citable from `Injectivity.lean`, and does it buy #5/#8 anything?** — i.e. task items 2 and 3,
which were always the ones that mattered.

Predictions answered: **Q1 WRONG (one SetModel name, `equivZero_iff_eval_zero`)**;
Q4 moot (no re-proof needed); Q8 **RIGHT in spirit** (the usual miss was not a structure field
but a whole already-landed module).
### M3 — citability, measured on the import closures directly

`Lean4Lean.Theory.Typing.Injectivity` import closure: **43 modules**. Computed with the same
closure routine `scripts/can-cite.py` uses (`re` on `^\s*import`, transitive).

| module | in `Injectivity`'s closure? | transitively imports `Injectivity`? |
|---|---|---|
| `Theory.Typing.PropAgreeGuarded` (the existing lift) | no | **YES** |
| `Theory.Typing.SortInvIndep` (defines `PropAgreeOn`) | no | **YES** |
| `Theory.Typing.AppCase` | no | YES |
| `Theory.Typing.SortClauses` | no | YES |
| `Theory.Typing.PropConv` | no | **no** |
| `Theory.Typing.PropShadow` | no | **no** |
| `Theory.Typing.Stratified` | no | **no** |
| `Theory.Typing.UniqueTypingN` | no | **no** |

Two verdicts, and they differ:

* **The existing lift (`PropAgreeGuarded.propAgreeOn_of_stratifiedNOn`) is NOT citable from
  `Injectivity`** — it is downstream, via `SortInvIndep → InjOneFact → … → Injectivity`.
  **Q2: RIGHT** (P=0.75). The already-performed migration landed *below* the hole it was
  supposed to serve, which is exactly the failure mode the brief warned about.
* **But the ingredients are not.** `PropConv`, `PropShadow`, `Stratified`, `UniqueTypingN` are
  **incomparable** with `Injectivity` — neither above nor below it. So a *fresh* module importing
  only those is acyclic with respect to `Injectivity`, and `Injectivity` could gain an import of
  it. Q2's reasoning ("the modules defining `PropTypeAgreeN`/`PropUniqN`/`stratifyN` themselves
  import `Injectivity`") is therefore **WRONG on the mechanism** while right on the verdict for
  the existing declaration: the blocker is not `PropConv`/`Stratified`, it is `PropAgreeOn`'s own
  home module `SortInvIndep`.

So a genuinely upstream lift is *possible* — my file can state the conclusion as its own
predicate rather than `SortInvIndep.PropAgreeOn`, import only the four incomparable modules, and
be citable from `Injectivity` after a one-line import addition to a file I do not own. That is
worth doing **only if the conclusion buys #5/#8 something**, which is the next measurement and
the one that decides the round.
### M4 — P4 verified: the "too weak" wall is machine-checked, and I read the proof

`Lean4Lean.VEnv.propAgree_conclusion_not_sortUniq` (`Theory/Typing/SortInvIndep.lean:493`):

```lean
theorem propAgree_conclusion_not_sortUniq :
    ∃ u u' : VLevel, (∀ ls, (u.eval ls = 0 ↔ u'.eval ls = 0)) ∧ ¬ u ≈ u' := by
  refine ⟨.succ .zero, .succ (.succ .zero), fun ls => by simp [VLevel.eval], ?_⟩
  intro h; exact absurd (congrFun h []) (by simp [VLevel.eval])
```

with the converse `sortUniq_conclusion_gives_propAgree` (`u ≈ u' → (u.eval ls = 0 ↔ u'.eval ls = 0)`),
so `PropAgreeOn` is on the **strictly weak** side of `SortUniq`'s conclusion, not incomparable.
**P4 CONFIRMED**, and the docstring is scrupulous about its own limit:

> **Does not establish:** that `PropAgreeOn → env.SortUniq U` fails at every environment — that
> would need a witness environment satisfying one and not the other, and none is exhibited here.

That named gap is the only place in this corner where new content is available, and I price it in §3.

### M5 — what `PropAgreeOn` actually buys, and why the layer rule is not the obstruction

`SortInvIndep.lean` already cashes the whole `PropAgreeOn` lead, downstream of `Injectivity`:

| declaration | what it gives | why it does not discharge #5/#8 |
|---|---|---|
| `sortNotProof_of_propAgreeOn`, `forallENotProof_of_propAgreeOn` | "a sort / a Π is not a proof" **without `SortUniq`** | side conditions of other lemmas, not the holes |
| `shapeLinkAgree_of_propAgreeOn` | `ShapeLinkAgree` ⟸ `WF ∧ PropAgreeOn ∧ ShapeMidShapeless` | `shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn` makes the hypothesis **equivalent** to the conclusion |
| `sortUniq_of_propAgreeOn` | `SortUniq` ⟸ `WF ∧ PropAgreeOn ∧ ConvStep2 ∧ ConvPiInv ∧ ShapeMidShapeless` | same `ShapeMidShapeless` collapse; and `ConvStep2 ⟸ SortUniq` |
| `sortLinkInvUC_iff_sortUniq`, `sortMidNonSortC_iff_sortUniq` | the sort-side residual **is** `SortUniq` | stated as `↔` by the file itself |
| `piInv_of_propAgreeOn` | `PiInv` off #5, onto #8 + the two `∀ n` | a trade between open statements; `SortInvIndep` §5 says so in those words |

And the decisive structural point, which the audit did not make: **every consumer of
`PropAgreeOn` that concludes #5 or #8 needs `RigidShapeUniqNS` / `ShapeMidShapeless` / `ConvStep2`,
which are `Injectivity`-and-below shape-lattice content.** So the consumption site is downstream of
`Injectivity` by mathematical necessity, and that is where it already sits and already compiles.
Moving `PropAgreeOn`'s *producer* upstream changes nothing about the consumers.

Verdicts: **Q5 RIGHT** (P=0.85) — the lift's output is exactly the ingredient proved too weak.
**Q6 RIGHT** (P=0.8) — route B stays conditional on two open `∀ n` statements
(`SortInvIndep` §5 route B; only `n = 0` is discharged). **P5 CONFIRMED**, **P6 CONFIRMED**
(`shapeLinkAgree_iff_shapeMidShapeless_of_propAgreeOn` is the `↔`, in file).

### M6 — the honest verdict on the audit's suggestion (recorded before I write any Lean)

The audit's "one genuinely under-explored move" is, measured:

1. **already performed** — `Theory/Typing/PropAgreeGuarded.propAgreeOn_of_stratifiedNOn`, in a
   *stronger* form (guarded hypotheses), with local copies of the one SetModel name;
2. **landed downstream of `Injectivity`**, which is not a mistake but the right place, because its
   consumers need `Injectivity`'s shape lattice;
3. **worthless for #5/#8 at any layer**, because what it produces is `PropAgreeOn`, whose
   deficit against `SortUniq` is machine-checked (M4) and whose every #5/#8-concluding consumer
   carries a hypothesis proved equivalent to its conclusion (M5).

So: **the layer rule was not hiding a usable ingredient.** The ingredient was never strong enough,
and the layer rule was not the obstruction. Q10 RIGHT.
### M7 — the file, built: `Lean4Lean/Theory/Typing/PropAgreeLift.lean`

`lake build Lean4Lean.Theory.Typing.PropAgreeLift`: **Build completed successfully (39 jobs)**,
**zero errors, zero warnings** (checked with `lean_diagnostic_messages severity=warning`: empty).
Every declaration `#print axioms`-clean — `[propext]`, `[propext, Quot.sound]`, one with none.
**No `sorryAx` anywhere in the file.**

### M8 — faithfulness of the restatement, measured (MCP `lean_run_code`, nothing written to the repo)

A scratch snippet importing my module *and* both downstream homes of the predicate:

```lean
example {env : VEnv} {U : Nat} : env.PropAgreeUp U ↔ env.PropAgreeOn U := Iff.rfl
example {env : VEnv} : env.PropAgreeUp 0 ↔ env.PropTypeAgreeOnCtx 0 := Iff.rfl
example {env : VEnv} (henv : VEnv.Ordered env)
    (pta : ∀ n, env.PropTypeAgreeN 0 n) (pun : ∀ n, env.PropUniqN 0 n) :
    env.PropTypeAgreeOnCtx 0 := VEnv.propAgreeUp_of_stratifiedN henv pta pun
```

**All four examples elaborate.** So the upstream restatement is *definitionally* the downstream
`SortInvIndep.PropAgreeOn` **and** the model side's `SetModel/PropSplitAudit.PropTypeAgreeOnCtx`,
and the upstream route B directly inhabits the SetModel original's conclusion. The lift is
faithful, not an approximation. **Q4: RIGHT in substance** — the proof transferred verbatim, only
`equivZero_iff_eval_zero` had to be re-proved locally (a third copy; see §3).

### M9 — cones (`scripts/exists.lean`, 466-module population)

| name | module | arity | cone | own value a hole | cone reaches `sorryAx` |
|---|---|---|---|---|---|
| `Lean4Lean.VEnv.propAgreeUp_of_stratifiedN` (**mine**) | `Theory.Typing.PropAgreeLift` | **4** | **2410** | false | **false** |
| `Lean4Lean.SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` (original) | `Theory.SetModel.PropAgreeWall` | 4 | **2703** | false | false |
| `Lean4Lean.VEnv.propAgreeOn_of_stratifiedNOn` (existing lift) | `Theory.Typing.PropAgreeGuarded` | 4 | **2410** | false | false |
| `Lean4Lean.VEnv.propAgreeUp_conclusion_underdetermines` (**mine**, new content) | `Theory.Typing.PropAgreeLift` | 2 | 1469 | false | false |
| `Lean4Lean.VLevel.propAgree_deficit_infinite` (**mine**, new content) | `Theory.Typing.PropAgreeLift` | 0 | 1465 | false | false |
| `Lean4Lean.VEnv.propAgree_conclusion_not_sortUniq` (the in-tree one-pair version) | `Theory.Typing.SortInvIndep` | 0 | 588 | false | false |
| `Lean4Lean.VEnv.PropAgreeUp` (**mine**) | `Theory.Typing.PropAgreeLift` | 2 | 578 | false | false |

**Cone comparison, as the brief demands it either way: 2410 vs 2703, a reduction of 293** —
exactly the `SetModel` prelude the original inherited by position. **Q3 RIGHT** (P=0.7).
My predicate's cone (578) equals `PropAgreeOn`'s measured 578 (audit M5), consistent with M8's
`Iff.rfl`. My two *new* results have cones 1465/1469, larger than `SortInvIndep`'s 588 one-pair
version — because they sit above `PropConv`/`UniqueTypingN` rather than above `InjOneFact`; that
is a cost of the upstream position, and the statements are strictly stronger.

### M10 — citability, run

`python3 scripts/can-cite.py Lean4Lean.Theory.Typing.Injectivity …`:

```
NO  Lean4Lean.VEnv.propAgreeUp_of_stratifiedN
     defined in Lean4Lean.Theory.Typing.PropAgreeLift
     Injectivity would have to gain Lean4Lean.Theory.Typing.PropAgreeLift
NO  Lean4Lean.VEnv.propAgreeOn_of_stratifiedNOn
     defined in Lean4Lean.Theory.Typing.PropAgreeGuarded
     Injectivity would have to gain Lean4Lean.Theory.Typing.PropAgreeGuarded
```

Both NO — **but they are different NOs, and the difference is the round's only positive finding**:

* gaining `PropAgreeGuarded` is a **cycle** (`PropAgreeGuarded ⇒ SortInvIndep ⇒ InjOneFact ⇒ …
  ⇒ Injectivity`), so the existing lift is *unusable in principle*;
* gaining `PropAgreeLift` is **acyclic**, demonstrated rather than argued: a scratch snippet
  importing `Injectivity` **and** `PropAgreeLift` together compiles, with both holes in scope and
  `propAgreeUp_of_stratifiedN` applied in the same file.

`python3 scripts/layer-check.py`: HARD RULE **passes**; my module appears in neither soft report
(12 of 284 Theory modules are downstream of `Verify/` — note the audit said 11; it is 12 today,
and none of them is mine). **Q9 RIGHT.**

### M11 — the instantiation test at the consumer position, run

In the same `Injectivity + PropAgreeLift` snippet:

```lean
example {env : VEnv} (henv : VEnv.WF env) (hT : env.PropAgreeUp 0) : env.RigidShapeUniqNS 0 := by
  exact?
```

`exact?` succeeds with **`exact @VEnv.WF.rigidShapeUniqNS env 0 henv`** — i.e. the only inhabitant
it can find is **hole #8 itself**, and `hT` is reported unused by the linter. That is the round's
instantiation test and it is negative in the sharpest possible way: with route B's output in scope
at the consumer position, the search still finds nothing but the hole.

### M12 — Q7, checked rather than assumed

I grepped `PropAgreeOn` against `open`/`hole`/`sorry` across `Theory/Typing` and `Theory/SetModel`
and found **no** "open"/"is-a-hole" conflation. The nearest thing is `SortInvIndep.lean` §3.1,
which gets it *right* and explicitly corrects `PiLevelPin.lean`: "`WF.rigidShapeUniq` is a
*theorem*, not a hole, and its inhabitant is `rigidShapeUniq_of_sortUniq …`". **Q7 WRONG** (P=0.35);
no docstring to flag. The one documentation error I did find is in `docs/audit-hole-producers.md`
itself (M2: it missed `PropAgreeGuarded`; M10: 11 vs 12 modules).

---

## §3 The edits this round implies in files I do not own — written out, NOT applied

### 3.1 The import that would make the lift citable (and why it should NOT be added)

File `Lean4Lean/Theory/Typing/Injectivity.lean`, import block. The edit would be, verbatim:

```lean
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.DeclRules
import Lean4Lean.Theory.Typing.NotProof
import Lean4Lean.Theory.Typing.PropAgreeLift          -- ← the one added line
```

Measured acyclic (M10) and it compiles (M11). **My recommendation: do not apply it.** M11 is why:
with `PropAgreeUp` in scope at that position, nothing in `Injectivity`'s reach concludes either
hole, and M4/M5 say why in general — `PropAgreeOn` carries one bit where `SortUniq` needs a natural
number, and every #5/#8-concluding consumer of it carries a hypothesis proved *equivalent* to its
own conclusion. An unused import into the module that holds two 700-user holes is a liability, not
an asset. If a later round finds a use, the line above is the whole cost of enabling it.

### 3.2 The duplication this leaves, and the tidy-up I am *not* proposing

`equivZero_iff_eval_zero` now exists in three places: `SetModel/PreludeOracle` (original),
`Theory/Typing/PropAgreeGuarded.equivZero_iff_eval_zero'` (second), and
`Theory/Typing/PropAgreeLift.equivZero_iff_eval_zero_up` (mine, third). Likewise route B itself
now has three statements (`PropAgreeWall`, `PropAgreeGuarded`, `PropAgreeLift`). The clean end
state would be: keep **mine** (upstream, smallest cone 2410), have `PropAgreeGuarded` and
`PropAgreeWall` import it and delete their copies. I am not proposing that as work, because §4's
verdict is that none of the three is on a live route; whoever holds the queued deletion of
`PropAgreeWall`'s copy should fold this in rather than treat it as a separate task.

### 3.3 A correction owed to `docs/audit-hole-producers.md` (not mine to edit)

Two factual corrections, for whoever maintains it:

* **§2.3 / M5 / M6.** "Migrating `propTypeAgreeOnCtx_of_stratifiedN` up out of `Theory/SetModel`
  … is the one genuinely under-explored move I found" — the migration **had already been done**,
  in a stronger (guarded) form, by `Theory/Typing/PropAgreeGuarded.propAgreeOn_of_stratifiedNOn`
  (arity 4, cone 2410, `sorryAx`-free), whose own module docstring §3 announces it as such. The
  audit cites `PropAgreeGuarded` nowhere. Its M6 citability row for
  `SetModel.PropAgreeWall.propTypeAgreeOnCtx_of_stratifiedN` is right about that declaration and
  misses that a `Theory/Typing` sibling already existed.
* **§4.1 third bullet / M6.** "it is **11** modules today, not 10" — as of today it is **12**
  (`layer-check.py`, M10). The list gained `ParamsCR` and `ParamsStruct` and lost none of the ones
  the audit named except that `ConfluenceRebuildPrice` etc. are still there; the count moves, so it
  should be re-run rather than quoted.

---

## §4 Verdict

**Is the lift possible?** Yes, and it is now done twice: once downstream (`PropAgreeGuarded`,
pre-existing, cycle-blocked from `Injectivity`) and once upstream (`PropAgreeLift`, mine, acyclic
and demonstrably co-importable with `Injectivity`). The audit's structural hypothesis — that the
layer HARD RULE was the obstruction — is **correct as a statement about import order and false as
a statement about the mathematics**.

**Does it supply anything new to holes #5 / #8?** **No.** It is not a third restatement in the
`sortPiDisjUC_iff_rigidShapeUniqNS` / `shapeMidShapeless_iff` sense — `PropAgreeOn` is *genuinely
independent*, and `propAgree_conclusion_not_sortUniq` proves it is not equivalent to the target.
It is the opposite failure: **independent but too weak**, and it runs into exactly the wall the
brief named. Quoted, in tree, `Theory/Typing/SortInvIndep.lean:493`:

```lean
theorem propAgree_conclusion_not_sortUniq :
    ∃ u u' : VLevel, (∀ ls, (u.eval ls = 0 ↔ u'.eval ls = 0)) ∧ ¬ u ≈ u'
```

with the file's own reading of it: "no instantiation of `PropAgreeOn` — at any subject, in any
context — yields universe uniqueness by reading its conclusion off". M11 is that sentence
re-measured at the consumer position, with the lift in scope.

**So the honest verdict on the audit's suggestion:** the layer rule was **not** hiding a usable
ingredient. The ingredient was never strong enough, the layer rule was not the obstruction, and
the relocation the audit asked for had already happened. `PropAgreeLift.lean` therefore does not
deliver a relocation as its result — §2 of that file delivers a **sharpening of the wall**, which
is the only thing in this corner that was actually missing:

| new result (all in `Theory/Typing/PropAgreeLift.lean`, `sorryAx`-free) | what it adds over the in-tree one-pair version |
|---|---|
| `VLevel.equiv_iff_eval_nil_up` | at `U = 0`, `u ≈ u'` **is** `u.eval [] = u'.eval []` — names the yardstick as a natural number |
| `VLevel.propBit_of_both_nonzero` | **any two** non-`Prop` `WF 0` levels satisfy prop-agreement's conclusion, at every `ls` — the conclusion is constant on the whole non-`Prop` class |
| `VLevel.propBit_iff_eval_nil_zero` | and that conclusion **is** agreement of the single bit `eval [] = 0`: two classes, against `ℕ` |
| `VLevel.propAgree_deficit_infinite` | an **infinite** pairwise-non-`≈` family agreeing on the bit — the deficit cannot be patched by excluding finitely many level pairs |
| `VLevel.propAgree_deficit_unbounded`, `VEnv.propAgreeUp_conclusion_underdetermines` | the two levels can be forced **arbitrarily far apart**, with witnesses independent of `env` |

The last of these is the round's headline in machine form: route B's strongest possible output,
at the only index it works at, is satisfied by level pairs at unbounded `≈`-distance, and the
witnesses do not mention the environment — so no choice of environment repairs the route.

### 4.a Prediction scorecard (§1.b, scored)

| # | P | verdict | note |
|---|---|---------|------|
| Q1 | 0.45 | **WRONG** | one `SetModel` name (`equivZero_iff_eval_zero`); pure `VLevel`, re-proved locally |
| Q2 | 0.75 | **RIGHT on verdict, WRONG on mechanism** | blocker is `SortInvIndep` (home of `PropAgreeOn`), not `PropConv`/`Stratified` — those are *incomparable* with `Injectivity`, which is what made an upstream lift possible at all |
| Q3 | 0.7 | **RIGHT** | 2410 vs 2703 |
| Q4 | 0.6 | **RIGHT** | proof transferred verbatim |
| Q5 | 0.85 | **RIGHT** | same wall, M4/M11 |
| Q6 | 0.8 | **RIGHT** | still conditional on two open `∀ n` |
| Q7 | 0.35 | **WRONG** | no conflation found; `SortInvIndep` §3.1 gets it right |
| Q8 | 0.15 | **RIGHT, in an unexpected form** | the missed thing was a whole already-landed module, not a structure field |
| Q9 | 0.9 | **RIGHT** | layer-check clean |
| Q10 | 0.9 | **RIGHT** | negative headline |

7 right, 2 wrong, 1 split. The two misses are both cases where I under-modelled the *import
graph* (Q2) and over-modelled the *documentation* (Q7).

---

## §5 Limits of my own result, and my method's gaps

1. **The unfalsified implication.** §2 refutes "instantiate prop-agreement and read `SortUniq` off
   its conclusion". It does **not** refute `PropAgreeUp env 0 → env.SortUniq 0`. That needs an
   environment satisfying the first and not the second, and I exhibit none. I priced the attempt
   and did not run it: the natural candidate is an `Ordered` environment carrying a rule
   `.sort 1 ≡ .sort 2` (both non-`Prop`, so plausibly prop-agreement-preserving), and proving
   prop-agreement *positively* there is a full inversion metatheorem for that environment —
   the same normalisation-shaped obligation the audit's §3.3 identifies as the shared missing
   ingredient of #5/#6/#8. **This is the one remaining piece of new content in this corner, and it
   is not cheap.** `SortUniqDown.sortUniq_badEnv` is where a candidate environment would come from.
2. **`U = 0` only.** Everything here is at `nv = 0`, because that is the only index at which
   route B's `equivZero_iff_eval_zero` step is legal; the step is refuted at `nv ≥ 2`
   (`SetModel/NotProofNoModel.propAgree_pointwise_not_from_equivZero`). §2's statements are
   correspondingly `WF 0`-guarded and say nothing about parametric levels. `PropAgreeUp` is stated
   at general `U` (to match `PropAgreeOn` definitionally) but only inhabited at `U = 0`.
3. **I did not re-derive the `↔`s I relied on.** `shapeMidShapeless_iff` and
   `sortPiDisjUC_iff_rigidShapeUniqNS` I verified exist and read their statements; I did not
   re-check their proofs. If either is wrong, M5's "every consumer restates the target" weakens.
4. **Method gap: I found `PropAgreeGuarded` by `grep`, not by the three prescribed scripts.**
   Method rule 3 tells you to run `exists.lean`, `shape.lean` and `can-cite.py` before writing "X
   does not exist" — but the audit's error was the *converse*: writing "X does not exist yet" about
   something present, having run `exists.lean` on the name it expected rather than on the *content*.
   A `grep -rn` on the original declaration's name found it in seconds. **The missing instrument is
   a reverse one: before calling a migration un-attempted, grep the tree for the name of the thing
   to be migrated and read every hit.** I recommend adding that sentence to the method rules; it
   would have saved this round's premise.
5. **`shape.lean` not run.** I never needed a conclusion-shape query, because I was not claiming
   absence — I was claiming presence, and presence is cheap to demonstrate. Recorded so the gap is
   visible rather than implied.
6. **What I did not measure.** Whether the *other* two `PropAgreeOn` consumers outside
   `SortInvIndep` (`PiInvResidual.lean` line 33's three-conjunct pricing, `SpineVarVacuity.lean`
   §'s hole-free conditional) would benefit from the upstream position. Both are downstream of
   `Injectivity`, so it cannot help them reach the holes, but neither did I check whether either
   has a use for the smaller cone.
