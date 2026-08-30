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
5. **A claimed reduction is not a reduction until the collapse test passes**: can the residual's quantifiers be instantiated so its premises degenerate into the target's? Two "reductions" were tautologies.
6. **Passenger test** (for whether an open lemma is really a primitive): if every call site inside proved theorems is on an IH output, it may be a passenger — but this is **necessary, not sufficient**. The conjunct must also be derivable from the invariant's components.

## Measuring

- **Never grep for `sorry`.** Use `scripts/sorry-census.lean` — it reads declaration *values* over both cones. A grep once reported 89 against a true 21, and three streams opened by correcting briefs built on it. One was sent to close five holes that were **inherited taint, not holes**.
- `ConstantInfo.value?` returns `none` for `.thmInfo`. A cone scan that does not handle this silently reports size 0. `scripts/cone-measure.lean` handles it.
- Counting `sorry` **tokens** can report progress as regression: one file went 8 → 13 tokens while going 4 → 2 *opaque statements*, because three theorems became written-out inductions with labelled sub-goals.
- **Read the elaborated program, not the source layout.** A `do` block's binders do not nest the way the source suggests. One recognizer's `false` half turned out to sit *inside* the `true` half's three binders — depth 3, not the base context — which invalidated a prescribed proof strategy on both of its clauses. The defect was invisible in the source and invisible to reasoning about the source; a single `#print` of the elaborated declaration found it.
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
