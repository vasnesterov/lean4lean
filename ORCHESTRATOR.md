# Orchestrator instructions

`CLAUDE.md` is for every agent. This file is for the orchestrator only.

## Handoffs, not resumes

**Avoid resuming an agent.** A resumed agent carries a long, mostly irrelevant transcript, and its answers drift toward what it already believes.

Instead:

1. When a stream reaches a boundary, ask it to write a **handoff file** — `docs/handoff-<topic>.md`, or a section in a file it owns.
2. Spawn a **fresh** agent and tell it to read that handoff first.

A handoff should carry what a newcomer cannot reconstruct cheaply:

- what is proved, what is stated-but-open, what is refuted — with the machine-checked names
- what was **tried and failed**, and the step it failed at; this is the half that gets lost, and re-deriving it is the most common waste
- which claims are measured and which are read off source, kept separate
- the invariants and traps of the files involved
- what the writer would pick up first, in one or two lines

**"Resuming" includes sending a follow-up message.** `SendMessage` to an agent that has already reported — "next, do X", "now take Y", "continue with Z" — is a resume, and is what this rule forbids. There is no short-follow-up exception; that phrasing was here and it was read as a loophole wide enough to run a whole session through.

When a stream reports and there is more to do on its topic: ask it to write the handoff and stop, then spawn a fresh agent pointed at it. The next assignment goes in the *new agent's brief*, not in a message to the old one.

Legitimate uses of `SendMessage`: relaying a fact a stream needs *for work already assigned* (another stream's finding, a blocker cleared, a correction to something you told it); telling a stream to stop; asking it to write its handoff. Not: giving it the next task.

If the answer to a question needs the transcript, it belongs in the handoff.

## Frozen files

`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean`.

- **Never delegate a frozen-file edit to a subagent.** Not as a "narrow exception", not with a tight scope, not because the change is mechanical. Subagents may never touch these files under any circumstance.
- **Never edit one yourself without explicit human approval for that specific change.** Prior approval of a similar change does not carry over.
- The flow: the subagent proves the content in a file it owns and states exactly what the frozen edit would be; you ask the human; on approval you make the edit; then PR it for review as usual.
- Watch for the shape of the request, not just its content. *"A check fails, so widen the whitelist"* is how a real failure gets laundered into a passing one. Verify independently that the assumption predates the change — a cone scan at the previous commit — and say so in the PR.

## Git

- The orchestrator owns git. Agents never commit, push, or open PRs.
- **Gate every commit on the build exit code.** `scratchpad/gated-commit.sh` does this and refuses on an empty diff. A commit chained with `;` after a build runs even when the build failed.
- **Stage explicit paths.** Never `git add -A` or `git add -u <dir>` — several streams share the tree, and a broad add sweeps in-flight work into an unrelated commit.
- Narrow the build target when another stream has an unrelated file red; do not wait, and do not commit unverified.
- **Before creating a PR or branch, check the content is not already in the target** (`git merge-base --is-ancestor`, or diff the files). A branch that builds is not evidence it contains anything: it may be behind, or already merged, or superseded.

## Rulings

- **Rule on measurements, not on reasons.** A plausible argument for a design choice is the weakest available evidence. Ask for the check that would falsify the plan, run, alongside the price — and if a stream sends a reason and waits, send back the check.
- When the argument forcing a complicated structure evaporates, the default is the **simple** structure, not the complicated one retained by momentum.
- A cheap outcome does not retroactively justify a ruling. Trust the criterion, not the outcome.
- Say plainly when a decision came from an instruction rather than a stream's instinct, and vice versa. Both are informative.

## Ownership

- **The session scratchpad directory is shared between streams.** A file one stream wrote there was overwritten mid-round by another agent. Tell every stream to use a **per-stream subdirectory** (`<scratchpad>/<short-task-name>/`) for anything it needs to survive its own round. This is not hypothetical — it has happened twice.
- One file, one stream. When two streams need the same file, **add a boundary** — a new file that imports the contested one read-only — rather than arbitrating.
- "Do not edit X" never means "do not read X". State this explicitly in briefs; it has cost real work.
- A file a stream does not own going red is not that stream's signal: wait, re-check, report, never fix.

## Relaying

Streams discover the same obligation independently. Relay findings across them deliberately — several times, one stream's blocker turned out to be another's already-proved lemma, or the same missing statement found from two sides. When a stream reports something that bears on another's file, send it, and say what to do with it.

## Reporting to the user

- Report what was verified and what was not, separately. "Green when I built it" is a different claim from "green".
- A count from a name-based search is not a measurement. Use structural instruments — import graphs, cone scans, arity checks, fully qualified names.
- Do not narrate the work; report results, corrections, and decisions needed.

## Statements that are false rather than open

Eight statements in this tree turned out **false**, not merely unproved. Every one read correctly. None was caught by a proof — **a proof consuming a vacuous obligation simply succeeds.**

The shapes seen so far:

- staged over a premise the intended case makes unsatisfiable
- guarded by a membership the intended case fails
- a parameter supplied by the caller and existentially quantified by the rule
- an invariant that fails in the very environments it is used in
- a binder silently captured (auto-bound implicit), so the statement is about the wrong variable
- a quantifier ranging wider than intended

**Audit against consumers, not only producers.** A statement is constrained from two
sides: what it must *describe* (the thing it abstracts) and what it must *support* (the
theorems that consume it). Checking only the first is how a "fix" gets prescribed that
breaks a proved theorem — this happened: `IsStructure.types` was found too narrow for
what the checker accepts, the obvious weakening was prescribed, and it was **refuted**,
because the weakened form admits blocks at which a consumer's term is a recursor
under-applied by two arguments, turning a *proved* lemma false. Before proposing a
weakening, enumerate the statement's consumers and check each.

**The check that generalises:** *does the statement carry enough information to determine its own conclusion?* Audit **information flow**, not binders. The narrow binder check catches only the fifth shape.

**Its mirror, which also bit:** an invariant **too strong to propagate**. The move is to ask what the hard case actually needs, confirm *that* weaker consequence is closed under the structural step, weaken until it propagates, and keep the strong hypothesis in the public statement to discharge at the root.

Put this check in every brief. It has now found more than the proofs have.

## Working rules that earned their place

1. **Definition, not check.** Make content a definition the caller cannot misstate, rather than a field the caller supplies and the spec validates. Worked five times; the alternative produced an actual inconsistency.
2. **Re-run the refutation against the fix.** A repair that does not *visibly kill its own witness* has not been shown to work. Required four times, caught a bad fix each time.
3. **Check the polarity before widening a predicate.** A predicate in a **negative**
   position is an *assumption*, not an obligation: dropping one of its fields
   **strengthens** what you are assuming, it does not weaken what you must prove. This
   nearly landed — an instruction to drop a field from `IsStructure` would have
   strengthened the structure-eta assumption to cover cases Lean's own eta gate
   excludes. And crucially: **a non-vacuity check cannot detect an over-strong
   assumption** — the witnesses still fire, because the predicate got easier to satisfy
   in the direction the witness tests. When a widening is wanted, define a *separate*
   widened predicate rather than editing the original in place.
4. **Non-vacuity is an acceptance criterion.** Fire every obligation at a non-degenerate witness. When no witness can exist, say **why**, and say plainly that *"no witness" is not evidence of truth*.
5. **Keep the reason, not the conclusion.** When a development inverts a structure to
   get at something inside it, the inversion usually throws away *why* the outer layers
   were there — and the proof then has to rebuild it. Carrying the development *down*
   through the structure instead is often free, because each layer's own shape lemma
   discharges it. This closed a site that had been "reduced to three named facts" for
   two rounds: two of the three did no work, and the escape the inversion discarded was
   the one that was stable under the operation being performed.
6. **A claimed reduction is not a reduction until the collapse test passes**: can the residual's quantifiers be instantiated so its premises degenerate into the target's? Two "reductions" were tautologies.
7. **Passenger test** (for whether an open lemma is really a primitive): if every call site inside proved theorems is on an IH output, it may be a passenger — but this is **necessary, not sufficient**. The conjunct must also be derivable from the invariant's components.

## Measuring

- **Never grep for `sorry`.** Use `scripts/sorry-census.lean` — it reads declaration *values* over both cones. A grep once reported 89 against a true 21, and three streams opened by correcting briefs built on it. One was sent to close five holes that were **inherited taint, not holes**.
- `ConstantInfo.value?` returns `none` for `.thmInfo`. A cone scan that does not handle this silently reports size 0. `scripts/cone-measure.lean` handles it.
- Counting `sorry` **tokens** can report progress as regression: one file went 8 → 13 tokens while going 4 → 2 *opaque statements*, because three theorems became written-out inductions with labelled sub-goals.
- **Read the elaborated program, not the source layout.** `do` notation restructures the program in ways the source hides, and this has now produced two *different* defects, each invisible in the source and to reasoning about the source, each found by one `#print` of the elaborated declaration:
  - **Binder nesting.** A recognizer's `false` half sat *inside* the `true` half's three binders — depth 3, not the base context — invalidating a prescribed proof strategy on both its clauses.
  - **Join-point duplication.** A mid-block `if` with **no `else`** makes the elaborator duplicate *everything after it* into a `__do_jp` join point reached along two paths.
  Also practical: `simp only []` (zeta) is what removes a `do` block's `have`s. Without it `split` keeps the `letFun` wrapper and `refine M.WF.bind` fails.
- **"Axiom cone" and "hole cone" are different measurements — do not conflate them.** The orchestrator did, repeatedly. A declaration can have an **empty hole cone** (reaches no `sorryAx`) while its **axiom cone** is `[propext, Quot.sound]` — which is the normal, healthy state for a real proof. Write which one you measured. "Sorry-free with an empty hole cone" is the strong claim; "empty axiom cone" is a much rarer and stronger one, and claiming it wrongly makes every other number in the report suspect.
- **Prefer the instrument to the assertion.** Committing the measuring script is what let three separate measurements be corrected.
- **Run `scripts/dup-names.lean` after any round that adds lemmas in two places.** Two modules can each declare the same name and both compile — `lake build` never imports them together. The pair is then *un-importable*, invisibly, until something needs both. This has happened three times, once walling an entire development off from `Verify/` so that nothing proved in it could reach `kernel_sound`.

## Relaying

Every brief's background is a relay. Say so in the brief — *"this is a relay of another stream's report, not ground truth"* — and ask to be corrected. Streams corrected the orchestrator on roughly half the rounds, including: a count inflated ~3.5×, a hole count inflated 4×, a "single step" that was neither single nor the step, a cited ledger row in the wrong document, a lemma named as a blocker that was never a blocker, and prior art missed twice.

When a brief's premise is wrong, that is usually the round's most valuable output. Commit it as such.

## Issue comments

The orchestrator posts to GitHub under the **same account as the human**, so the
PR/issue-comment monitor cannot tell them apart by author. **End every issue or PR
comment you write with the marker line**

    <!-- l4l-orchestrator -->

`scripts/monitor-pr-comments.sh` drops comments carrying it. Without the marker the
monitor echoes your own comments back at you, and a real reply from the human is
buried among them — which is the one thing that monitor exists to prevent.

## What gets an issue

Issues in the user's fork are for findings that matter **outside this repo's own
construction**. Exactly three kinds:

1. **Soundness bugs** — a kernel accepts `False`, or accepts a declaration that lets
   `False` be derived.
2. **Inconsistent axioms** — an axiom in `Verify/Axioms.lean` that is false, or a set
   of them that is jointly unsatisfiable.
3. **Mistakes in papers** — a published result that is false as stated, with a
   machine-checked counterexample and the scope stated in registers (our proxy / the
   paper / Lean itself).

**Not an issue: our own spec gaps.** A statement in `Theory/` or `Verify/` that turns
out false, vacuous, under-hypothesised, or missing — however severe, however
instructive, and *even when it yields an inconsistency in the abstract spec* — is
ordinary work in progress. It belongs in the commit message and the handoff doc,
which are already the durable record. Filing those inflates the issue tracker with
this repo's construction history and buries the findings someone outside it needs.

Ten such statements were filed as issues once, and removed. The commit messages and
`docs/handoff-*.md` already carried every one of them.

## Census 18: the remaining work is narrower than the count suggests

Measured on the canonical instrument after `b58b248`, once the fourth duplicate-name
collision was cleared and `sorry-census.lean` could see the whole tree again.

**Five of the six `Injectivity.lean` holes were the same goal**, and they are now one.
Sites 840/878/938/992/1049 were all the **`trans` case of an induction on `IsDefEqStrong`,
middle term arbitrary**. A stream verified that from the *goals* — both halves arrive at a
**common type `T`** with the middle term arbitrary, so the induction hypotheses are unusable
and it used none of them in any of the five. They now sit behind one named statement,
`VEnv.WF.rigidShapeUniq` (176 users). **Census 18 → 14.**

Its sharper correction to the comments at those sites: `trans` is not a residual *fragment*
of each theorem. `IsDefEq.trans` composes the two halves back into the theorem's own
hypothesis, so each induction reduces its statement **to itself** — the other ten cases are
shape bookkeeping and `trans` *is* the theorem. That is why five separate attempts had all
stalled in the same place.

**I had the supplier direction backwards, and it matters.** I wrote below that closing
`NormalEq.descend` would close the `trans` case and drop five holes. That is **circular**:
`ChurchRosser.lean` imports `UniqueTyping` imports `Injectivity`, and `descend`'s own proof
region calls `IsDefEqU.forallE_inv`. `descend` **consumes** the injectivity holes. Worse,
`descend` is **false at three of its five branches** — `Theory/Typing/DescendRefute.lean`,
`not_descendStatement`, with `NormalEq.etaL` and `NormalEq.proofIrrel` as witnesses. I sent a
stream to "supply hypotheses" for branches that cannot be proved at all.

**The rule that would have caught it:** before declaring X the supplier for Y, check the
import edge and check whether X's own proof already calls Y. Both are one `grep`. I checked
neither, and the brief asked a stream to match an interface to a statement that had already
been refuted **in this repo**, in a file named for the refutation.

**And the standing caution applies to the refutation too.** `not_descendStatement` is
conditional on `refEnv.SortUniq 0` and `refEnv.UniqTyping 0`, carried as hypotheses because
`IsDefEq.uniq` is tainted here. Whether it bites depends on those being satisfiable — the
same structure as the `church_rosser` claim I overclaimed and retracted. Unsettled; asked.

**Method note.** I found this by reading the five `sorry` sites, not by reading the
count. The count treats holes as independent; they are not, and no instrument I have
reports the *shape* of a residual. When the census stalls, read the goals — the number
cannot tell you that five of its entries are one problem, nor that its largest entry is
unrelated to the other five.

**Corollary for briefs.** A consumer can be written against the supplier's conclusion
*before* the supplier exists, so long as the interface is the supplier's real one. That is
worth doing precisely when several consumers share it. The failure mode to avoid is
inventing a convenient interface: `descend`'s docstring records that an earlier version of
its own interface was **refuted** by `NormalEq.etaL` and `NormalEq.proofIrrel`, so any
bridge stated against it must survive those two witnesses.

## Round: census 14, descend refuted, four streams out

### Decision made: `IsStructure.decl` strengthening APPROVED

Stream C stated it and stopped, judging it an orchestrator call. It is: `IsStructure`
lives in `Theory/Inductive/Structure.lean:478`, which CLAUDE.md designates proof
machinery I may freely design. Polarity is favourable — `IsStructure` is a *hypothesis*
of `TrProj.mk`, so strengthening helps all four `TrProj` consumers (`wf`, `uniq`,
`weak'_inv`, `defeqDFC`) and charges the construction sites (`inferProj.WF`, `TrExprS`'s
`proj` sites). Target: `TrProj.uniq` [89] + `TrProj.weak'_inv` [29].

Constraint the stream must respect: `IsStructure.mono` exists and `TrProj.mono` needs
monotonicity in `env`. A field placing a step in `env`'s own WF chain is at risk there.

### Dead route, checked and killed — do not retry

I hoped to avoid touching `IsStructure` at all: distinguish a `.def` from an inductive by
the constant record (no value ⇒ not a `.def` ⇒ no δ-rule ⇒ `RuleFreeHead`). **Dead at the
representation level.** `VConstant` (`Theory/VEnv.lean:5`) has exactly two fields, `uvars`
and `type` — no value — and δ-rules live in a separate `env.defeqs`. Nothing in the
constant record separates them. Stream C's route really is the cheapest.

### New instrument rule: `allowOpaque := true` or the measurement is a lie

I wrote an ad-hoc cone script and it reported `descendV`'s hole cone as **empty** while
`#print axioms` on the same declaration reported `sorryAx`. The bug: `ci.value?` without
`allowOpaque := true` returns `none` for `.thmInfo`, so the walk saw types only and every
theorem cone looked clean. `scripts/hole-cone.lean` documents this in its own header and I
did not read it before writing a competing script.

**Rule: cone measurements go through `scripts/hole-cone.lean`'s `deps`, not a fresh script.**
This is the second instrument-trust failure of the session (the first: grep-for-`sorry`
reporting 89 against a true 21). Both times the ad-hoc tool was the wrong one and a
canonical one already existed.

Measured properly, and this is what licensed the rewiring round:

    descendV                  {rigidShapeUniq, weakN_iff, forallE_inv_stratified}
    appDF_extra_of_descendV    same three
    descend                    those three + itself
    church_rosser              those three + descend

`descend` absent from `descendV`'s cone ⇒ genuine replacement, not a relabelling.

### `descend`: 44 transitive users, one direct consumer

The 44 all route through a single chain, which makes the rewire tractable:

    parRed (ChurchRosser:2117) → appDF_extra_of_descend (2021) → descend (1831)

Real obstacle is layering, not proof: `KDescend` → `DescendRefute` → `ChurchRosser`, so
`parRed` sits *above* `descendV` and cannot call it in place. Either lift `descendV` up
(friction: `appDF_extra_of_descendV`'s K-step hypothesis lives in the downstream
`KRule.lean`) or push `parRed` and the `church_rosser` chain down. Left to the stream on
evidence, with one hard constraint: **do not propagate the `NoApp` hypothesis up into
`church_rosser`'s statement** — that would weaken the confluence theorem rather than fix it.

### `forallE_inv_stratified` [449]: syntactic side declared closed, model round opened

Accumulated verdict across three rounds, all machine-checked: the hole **is** `SortUniq`
(`piInvStratApp_iff_sortUniq`); a counterexample at *any* WF env sinks the whole Π/sort
family unconditionally (`not_piInvStratApp_of_not_sortUniq`, sorry-free); level bookkeeping
alone provably cannot finish the `app` case (`imax_cod_not_pinned`); and the last syntactic
hope — `sort_not_proof` from the descend side — is closed, because ChurchRosser's E3
branches *consume* `Params.sortUniq` and so sit inside the circle. A model is the only
remaining candidate source. Stream sent at `Theory/SetModel/` + `~/lean-type-theory/unique.tex`,
briefed to establish the *transfer* direction before building any semantics, since a model
argument that cannot reflect back to `IsDefEq` is no progress.

### Two satisfiability arguments retracted this session

Both were assuming what they were checking. Worth remembering as a pattern: (1) the
`refEnv.SortUniq` derivation went through a statement `piInvStratApp_iff_sortUniq` proves
*equivalent* to its own target; (2) "the `badEnv` failure route is closed at `refEnv`" rests
on `WF.instL_lhs_ne_sort`, which holds at every WF env and so says nothing about `refEnv`.
What survives is that `refEnv_no_defeqs` kills the `extra` constructor, reducing
`SortUniq refEnv 0` to beta/eta/proofIrrel/trans confluence over six axioms with no rewrite
rules — the first finite, self-contained instance of this circle in the tree.

### The model route to `sort_not_proof` is CLOSED — and my brief's premise was a non-sequitur

I sent a stream at `Theory/SetModel/` on the reasoning that `sort_not_proof` survives
cumulativity, so "unlike `SortUniq` it is not blocked for the n-inaccessible model." That
inference is invalid and the stream said so: **surviving cumulativity means a model cannot
*refute* it; it does not follow that a model can *prove* it.** A negative check rules a route
out; passing one does not rule a route in. The claim came from `Typing/SortUniq.lean`'s
closing paragraph ("`sort_not_proof` is the statement worth asking the model stream for"),
which I repeated without checking. That paragraph is wrong.

The machine-checked reason the route is closed is stronger than the correction
(`Theory/SetModel/NotProofNoModel.lean`, 559 lines, 16 of 18 declarations sorry-free):

    nonempty_propSplit_iff_agree : Nonempty (PropSplit env nv) ↔ PropUniq nv ∧ PropTypeAgree nv
    sortNotProof_of_propSplit    : gets sort_not_proof from PropSplit with NO interpretation

No ZFC, no inaccessibles, no `Stable`. **The semantic construction is strictly dominated: it
cannot prove anything about `sort_not_proof` that its own hypothesis does not prove more
cheaply.** Building the model to get `sort_not_proof` is circular.

Independent corroboration, which I should have found before briefing: `Typing/UniqueTypingN.lean`'s
`PropTypeAgreeN` section already said the model route is closed, for the same reason (a
cut-down model bottoms out at `sort_not_proof`, which is `PropTypeAgreeN` at a sort). It was
prose there; it is now machine-checked. Two independent derivations agreeing is worth having,
but a third of that round was rediscovery, and reading the existing analysis first was one grep.

Also from that round, all sorry-free: `sortNotProof_of_propTypeAgree` and
`forallENotProof_of_propTypeAgree` drop **both** the `SortUniq` and `OnCtx` hypotheses the
existing `sort_not_proof` carries; and the transfer obstruction is isolated exactly —
`Sound`'s fields quantify over `ρ ∈ interpCtx M L Γ`, `interp_falseProp` gives
`⟦∀p:Prop,p⟧ ∅ = ∅`, so `Sound M L [falseProp] e₁ e₂ A` holds for **arbitrary** terms with no
typing premise, at precisely the context shape every consumer of `sort_not_proof` supplies.
The semantics is easy; the quantifier is empty where the hole is used. Closing over the context
moves it to `[]` but makes the term a `lam`, whose obligation is false — which is *why*
cumulativity is semantically valid.

**New composition defect found, at the level layer.** The model's `PropTypeAgree` is pointwise
in `ls`; the syntactic `IsPropN` is the `≈ .zero` shape. `propAgree_pointwise_not_from_equivZero`
**refutes** the direction needed (`.param 0`, `.param 1`, both `WF 2`, both `≉ .zero`,
disagreeing at `ls = [0,1]`). So a completed `PropTypeAgreeN` would *not* discharge
`PropSplit`'s import. Cheap repair: nothing in `Interp.lean` evaluates a level at any `ls`
other than `M.ls`, so the `∀ ls` is unused generality — narrow it. Authorised.

### Revised frontier for the 449-user family

The target is **not** `SortUniq` and **not** `sort_not_proof`. It is `PropTypeAgreeN`, and per
`UniqueTypingN.lean` that is not self-sufficient either — the primitive to route or fund is

    SortForallEDisjoint env U n : ∀ {Γ e A B u},
      HasTypeN U n Γ e (.sort u) → HasTypeN U n Γ e (.forallE A B) → False

`eta`'s case of `PropTypeAgreeN` is exactly this; `proofIrrel`'s case is by contrast a
self-reference (an instance of `PropTypeAgreeN` at another subject, measure `≤` not `<`).
`sortForallEDisjoint_of` forces any counterexample to have an **application** subject and the
`const` case is proved, so it is a narrow target.

**The open risk, and the thing I most need answered:** `UniqueTypingN.lean` claims
`PropTypeAgreeN`'s `forallEDF` case drops an index exactly as `SubstC` does and therefore sits
in the family **refuted** in `Theory/Typing/SubstCRefute.lean`, with no rule able to repair it.
If that holds, `PropTypeAgreeN` is unreachable by its own induction and the question becomes
whether `sort_not_proof` can be had from `SortForallEDisjoint` + `SortInvN` alone. Sent back
to be verified rather than inherited — this session has caught several stale docstrings.

### RETRACTION: the `IsStructure.decl` ruling above was wrong, and the strengthening would have been unsound

The "Decision made: `IsStructure.decl` strengthening APPROVED" section above, and its
"Stream C's route really is the cheapest" conclusion, are **both retracted.**

`VEnv.RuleFreeHead env s` at a structure name **is** derivable from `VEnv.WF env` +
`IsStructure S D T C` exactly as `IsStructure` already stands. `StructureRuleFree.lean`
(new, sorry-free) proves `IsStructure.ruleFreeHead` in four lines from
`VEnv.WF.iotaTypeNotKey` (`Theory/Typing/DeltaUnique.lean`, sorry-free). The provenance
argument I approved building into `decl` — "the declaring step was the `.induct` step" — had
**already been run**, for this exact name, in `iotaTypeNotKey`'s `WF'` induction. `env₁ ≤ env`
was never asked to carry it. The only real gap was **notational**: the injectivity family
speaks `VExpr.headConst?`, DeltaUnique Part III speaks `VDefEq.key`, and nothing related the
two. One bridge lemma closed it.

**And the strengthening was not merely unnecessary, it was unsound as design — provably, not
riskily.** `RuleFreeHead env s` is *anti*-monotone in `env`; `IsStructure` is *monotone*
(`IsStructure.mono`). So any `IsStructure` field strong enough to imply `RuleFreeHead` must
break `mono`: `env.addDefEq (δ-rule at S)` is `≥ env`, so no monotone field can exclude that
rule. The cascade would have been `IsStructure.mono` → `TrProj.mono` → `TrExprS.mono` and its
~15 call sites. What reconciles the polarities is passing `VEnv.WF env`, which is what the
real proof does. I did flag `mono` in the brief as "a risk to check"; I should have seen it
was decisive rather than a risk, because it settles the question a priori and in one line.

**New reusable check, and it would have caught this ruling before I made it:** before
strengthening a hypothesis-position predicate to imply a target, compare their monotonicity
in `env`. A monotone predicate cannot imply an anti-monotone one. `IsStructure` is monotone
by design (`TrProj.mono` needs it); `RuleFreeHead`, `PatFreeHead`, `WeakNorm` and the whole
rigidity family are anti-monotone, because adding rules can only destroy them. Any future
"just strengthen the structure predicate" proposal dies to this in one line.

**Third error of this class today**, and the pattern is now unmistakable: stream C reported
"not derivable as `IsStructure` stands", I ruled on it without checking, and it was derivable
from a lemma already in the tree. The earlier two were the inverted supplier direction
(`descend` vs. `Injectivity`) and the cumulativity non-sequitur in the model brief. In all
three the check was one grep or one line of reasoning, and in all three I passed a stream's
analysis through as a premise instead of testing it. **Rule: a stream's negative claim
("X is not derivable", "Y is closed") is a lead, not a finding, until I have checked it or
had a second stream check it.** Positive claims come with a build; negative ones do not.

Nothing was cost-shifted: `IsStructure`, `mono`, all four concrete witnesses, and every
construction site (`inferProj.WF`, `TrExprS`'s `proj` sites, `StructureBridge.lean`'s two
bridges) are untouched. `docs/audit-classes.md:181` also references `IsStructure.decl` and
should be re-read against this.

### Where the two `TrProj` holes now stand (census still 14 — neither closed)

`ProjSpineInv.lean` (new, sorry-free, placed upstream of `Verify/Typing/Lemmas.lean`) reduced
`TrProj.uniq` from four obligations to **one**. Obligations (B) `const_app_inv` and (D)
no-confusion fall together to `VEnv.constApp_inv_of_wf`, with both `RuleFreeHead` side
conditions from the new lemma — no `PatWF`, no `Params`, and `S₁ = S₂` comes out as a
*conclusion* rather than a hypothesis.

The single residual is `VEnv.ProjTermCongr`: congruence for `VInductDecl'.projTerm` at one
context and one structure name, mentioning no environment invariant. It is implied by
`TrProj.uniq` itself via `IsDefEqCtx.refl`, so the reduction smuggles nothing in. Route:
`instL_r` for the `≈`-levels half; `mkAppDF` at the recursor telescope for the spine half,
recursing on `i` as `VInductDecl'.projArgs` does, each step wanting the typing the
`Verify/Typing/ProjGen*` family already supplies for `TrProj.wf`. Mechanical, comparable in
size to that family.

`TrProj.weak'_inv` is now blocked on **`VEnv.WeakNorm` alone** (`Verify/Typing/ConstSpine.lean:526`
— defined, consumed twice, proved nowhere) plus the shared `weakN_iff`. Its docstring's
"provably cannot supply `RuleFreeHead`" claim is retracted in place.

## Round record — the confluence/strengthening cycle, measured (2026-08-31)

`StrengthenNarrow.lean`'s round-5 verdict says the normalisation route to `weakN_iff` is
"cyclic here for import reasons". I checked whether the cycle is *logical* or merely
*incidental*, using `scripts/hole-cone.lean`'s `deps` plus a BFS for the shortest dependency
path. The `weakN_iff` dependence enters the confluence chain at exactly **two independent
places**:

```
NormalEq.descendV -> DescentLam.beta -> DescentLam.instN -> NormalEq.trans
                  -> NormalEq.weakN_iff -> NormalEq.weakN_inv_DFC -> IsDefEqU.weakN_iff
NormalEq.parRed   -> ParRed.weakN_inv  -> IsDefEqU.weakN_iff
```

Measured cones: `church_rosser` = `parRed` = `descend` = `{weakN_iff,
forallE_inv_stratified, rigidShapeUniqNS, descend}`; `descendV` = the same minus `descend`;
`ParRedK.defeq` = `{forallE_inv_stratified, rigidShapeUniqNS}` — **already clean of
`weakN_iff`**; `ParRed.toK` = `{}`.

The reason to think the cycle is incidental: `NormalEq` has **ten constructors and no `trans`
constructor** (`NormalEq.trans` is a theorem). `Strengthen.lean` §5 establishes that eleven of
the twelve conversion rules close from `TypingStrengthening` alone and only `trans` resists —
so induction on `NormalEq` is missing precisely the case that defeats the direct route. And
reading `weakN_inv_DFC`'s nine cases, every invocation of full conversion-strengthening looks
either **reflexive** (`refl`, `etaL`/`etaR`'s first use, `proofIrrel` — i.e. typing
strengthening, which §5 of `StrengthenNarrow.lean` already discharges) or **restricted to a
type shape**: `A := .sort ..` in `lamDF`/`forallEDF`, `A := .forallE ..` in `etaL`/`etaR`,
and `appDF`'s conversion is between the *types* of the two heads.

If that holds, `NormalEq`-strengthening is independent of the hole, and the hole closes by
transport once confluence is repaired: `e1↑ ≡ e2↑` upstairs → `church_rosser` → `NormalEq`
upstairs → `NormalEq`-strengthening → `NormalEq` downstairs → `NormalEq.defeq`. 131 users.

This also makes the concurrent `ParRedK` work load-bearing rather than hygienic: repairing
`parRed` stops being "delete a false lemma, census 14→13" and becomes the enabling half of
the largest hole in the tree.

**Booked as a lead, not a finding.** Per the rule from earlier this round, my reading of the
nine cases is exactly the kind of claim that has to be checked before it is spent: the brief's
task 0 is to falsify it, and the honest failure mode is that the `.sort`/`.forallE`
restrictions are just as hard as the general case, in which case the round ends with a sharp
negative. Second risk, named: entry (2) `ParRed.weakN_inv` is a separate obligation, and the
transport argument needs `church_rosser`, which routes through it.
