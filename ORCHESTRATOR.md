# Orchestrator instructions

`CLAUDE.md` is for every agent. This file is for the orchestrator only.

## Measuring the checker: the arena is not what it looks like

- **`lka.py run` does NOT build.** `build-checker` copies the whole source tree into
  `_build/checkers/<name>/src/` and builds *there*; `run` executes that copy's binary and never
  rebuilds it. Run `uv run lka.py build-checker lean4lean-local` first -- the checker name is
  **positional** there, unlike `run --checker <name>`. Then verify the copy really is this tree:
  `grep` it for the behaviour you just added and check the binary's mtime. A whole session's
  figures, and three commits' verification claims, were fiction for want of this.
- **Name the expected flip BEFORE running, and treat its absence as a harness fault.** "Identical
  to the last recorded result" is the signature of a safe change *and* of an untested one, and
  only a named flip tells them apart. A rejection-boundary change that moves nothing is a
  red flag, not a pass -- especially when the test that should move is graded `either`, where a
  flipped verdict does not change the summary line at all.
- **Three tests carry the whole scale signal**: `init`, `std`, `perf/grind-ring-5`. The other 188
  are small hand-built cases. A regression that only fires at real-library scale shows up in
  exactly those three and nowhere else, so a clean summary minus those three is not a clean suite.
- **Ask whether the constant was ever ADDED before asking why the lookup failed.**
  `lean4lean --import --verbose` prints `adding <name>` per declaration;
  `grep -c "adding <thatName>"` returning 0 separates "never inserted" from "inserted but
  unfindable" in one command. This killed a plausible and wrong hypothesis (the HAMT/`SMap`
  replacement, whose real failure mode *is* a lost entry) before it cost a single build.
- **Bisect over implementation-touching commits only.** 550 commits since the snapshot, 29 of them
  touching anything the binary is built from; `git log --oneline --reverse <base>..HEAD -- Lean4Lean/
  ':!Lean4Lean/Theory' ':!Lean4Lean/Verify' ':!Lean4Lean/Experimental' ':!Lean4Lean/Tests'` gets the
  list, and `lake build lean4lean` (95 jobs, not 1497) is the only target needed. Five probes, and
  `git show <sha> -- <path>` reads objects without disturbing the working tree, so the diff can be
  inspected while the bisect is still running. **Do not run streams during a bisect** -- the tree is
  checking out old commits underneath them.

## Never stage with `-u` or `-A` while streams are live, and check HEAD is self-consistent

I broke `HEAD` once today with `git add -u`. It stages every tracked modification, which in a
multi-stream session includes other streams' half-finished edits — so a commit picked up a live
stream's new `import` line while the file it imports was still **untracked**. `HEAD` then imported a
module absent from the repository: **the build is fine locally, because the file is on disk, and
only a fresh checkout fails.** The same command also swept a second stream's file mid-work, under an
unrelated commit message. Both were noticed by the streams, not by me.

**Use explicit paths, always.** I did for every other commit today and reached for `-u` once, in the
one environment where it is unsafe.

And because the failure is silent locally, check it after committing:

```python
# every import of a Lean4Lean module, in every tracked .lean file, must name a tracked file
import subprocess, re
tracked = set(subprocess.run(['git','ls-files'],capture_output=True,text=True).stdout.split())
bad = [(f, m.group(1)) for f in tracked if f.endswith('.lean')
       for m in re.finditer(r'^import\s+(Lean4Lean[\w.]*)', open(f).read(), re.M)
       if m.group(1).replace('.','/') + '.lean' not in tracked]
print(len(bad), bad[:10])
```

Run after the day's commits, not after each one. It reported **0** once the one-off was fixed, which
is what makes it worth keeping: it is a cheap check for a class of damage that no build catches.

**And then I broke `HEAD` a second time the same day, with the OPPOSITE error.** Staging by explicit
path for a spec-clause change, I committed the clause and **left out the nine files that discharge
it** — `HEAD` failed with 4 errors while my working tree was green. So the rule is not "use `-u`" or
"use explicit paths"; each fails in its own direction:

> **After any commit, build WHAT YOU COMMITTED, not what is in the working tree.**

The working tree was green through *both* failures, which is precisely why neither surfaced. The
cheap version, for a commit you are unsure about:
`git stash push -u && lake build; git stash pop` — that is how the second and third breakages
were diagnosed, and it takes one command.

**But use the right form, and I got this wrong once.** `git stash push -u` stashes the **index as
well**, so the build then tests bare `HEAD` — correct for *"did my last commit break `HEAD`?"* and
**vacuous** for *"will what I am about to commit build?"*. For the second question:

    git stash push -u --keep-index && lake build; git stash pop

which leaves the staged set in the working tree and hides everything else. I ran the wrong one and
got a green that meant nothing, because `HEAD` was already green. Note also that the `--keep-index`
pop can leave files **modified but unstaged**, so re-check `git status` before committing.

## Briefs can get too heavy to start

A stream stalled (no progress for 600s, watchdog did not recover) having produced exactly one
line: "I'll start by reading the required context." Its brief told it to read **3365 lines** across
four files — two handoff section-ranges, two Lean modules — plus §0 and three row ranges of a
1034-line ledger, all before any work.

The other two streams launched in that same round, with reading lists half the size, both finished.

So: **inline the five or six facts the task actually turns on, and point at ONE file.** A stream
does not need the corner's whole history to prove one lemma; it needs the names, the measured
figures, and the traps specific to its target. The long trap lists earned their place one at a
time, but pasting all of them into every brief is how a brief stops being readable — and the
stall came at the reading step, not the proving step, so the cost was the whole round for nothing.

Symptom to watch for: a brief where the "read this first" list is longer than the task
description. Two of mine were, and one of those two stalled.

**CORRECTION, same day: this diagnosis is not confirmed and is probably wrong.** The task was
relaunched with a brief a fifth the size — one file, facts inlined — and **it stalled again**, this
time at "I'll read the target file now". Then I measured the file: **1.9 s** to elaborate, *faster*
than a 783-line file another stream read without trouble (4.1 s), and it contains no `decide` at
all. So neither brief weight nor a pathological file explains it.

What is actually established: **five infrastructure failures in one session** — three
`API Error: context canceled` and two watchdog stalls — and the two stalls hit **the same task
twice**, both at the reading step, under very different loads. I do not know the cause. Keep the
"inline the facts, point at one file" advice, because it is cheap and good practice regardless, but
**do not treat it as the fix for a stall.**

The operational rule that follows: **after two failures on one task, change a variable other than
the brief.** Reassign to the graded fallback, or to a different target in the same corner, rather
than launching a third identical attempt. A third try tests nothing.

## Streams that write their artefact last lose everything when they crash

Two streams died with `API Error: context canceled` on 2026-09-02, both long-running, and **both
at the moment they were about to write their output**. One left ~800 lines of good work on disk
because it had been editing as it went; the other left **nothing at all** — its last words were
"Now let me write the final file", and its whole session was unrecoverable.

So brief every stream to **write incrementally**: land each proved lemma in its file as it is
proved, and write the handoff section by section rather than composing it at the end. A crash then
costs the last step instead of the round.

**Confirmed by a controlled repeat.** A third stream crashed the same way, on the same task as the
second, with the same last words ("Now let me write the handoff section") — but this one had been
briefed to write incrementally, and **503 green lines survived** (396 in `ConstSubstNested.lean`,
107 in `NestedTele.lean`, building clean at 69 jobs) where its predecessor on that identical task
had left nothing at all. Same task, same crash, same failure point, opposite outcome: the
instruction is worth the line it costs in every brief. This also makes a partial result inspectable, which is
what let me recover the `fieldB` work by building its modules myself.

Two related habits from the same pair of failures:

- **Check `git status` before assuming damage.** The second crash looked worse than the first and
  was actually harmless: nothing was written, so nothing was corrupted.
- **Do not resume a crashed agent.** Its context is gone or polluted; spawn a fresh one with the
  same brief plus whatever the dead one established. That is the handoff rule, and a crash is the
  case it was written for.

## A soundness fix can introduce a completeness regression

`f743c46` closed a real hole (a lying `Nat.gcd` passing the recognizer while `reduceNat`
accelerates it by name) and, in the same edit, made the checker reject the *genuine* `Nat.gcd`.
Reverting was not available: it reopens the hole. Two habits follow.

- **When a check constructs a reference term, ask which constants that term names and whether the
  declaration under test depends on them.** Anything outside the declaration's own cone is absent
  under minimal-cone replay, and the check dies on a valid input. Nothing in this repo measures
  this; the arena's real-library tests are the only instrument that sees it.
- **Check what the available fallbacks actually do before designing around them.** Here neither was
  open: `fail` throws, and `return false` makes `checkName` throw because the name is in
  `Environment.primitives`. A name in that list may be declared only if the recognizer *succeeds*,
  so "decline to accelerate" was not a repair. I had designed the wrong fix before reading that,
  and would have shipped a second rejection.
- The repair route that worked is worth remembering generally: **a proof argument can be bound as a
  variable instead of constructed.** Proof irrelevance makes the check equivalent, the statement
  universally quantified (if anything stronger), and the constant cone smaller.

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

## Lessons from the 2026-09-01 session — read before commissioning anything

**I violated the handoff rule above, all session, and the rule won.** Every "continue: X" message
was a resume by the definition three paragraphs up. The evidence for the rule is now concrete:
**four proofs duplicated theorems the tree already had** (`WF.defEqHeadsUnique`,
`Ordered.noCSubst`, `WF.instL_lhs_ne_forallE`, `ParRedKS.defeqDFC`), a parameterised witness that
settled a two-round question had been sitting in the tree **unlooked-for through six rounds of the
same agent**, and the first *fresh* agent pointed at a handoff found a dropped obligation those six
rounds had propagated. Resumed agents stop re-exploring. Write the handoff; spawn fresh.

**Verify the binary before quoting an arena result.** Every arena run reported on 2026-09-01–02
tested a **two-day-old binary**: the checker config's `build:` step did not take, silently, and two
commits cite verification they did not have (ledger rows 120, 120a). Before quoting an arena
summary, check `.lake/build/bin/lean4lean` is newer than every implementation file changed since the
last run, and for a change that adds a check, `strings` the binary for the new behaviour's own
message. **A rejection-boundary change must FLIP a named test. If nothing moves, suspect the harness
before concluding the change is safe** — "identical to the last recorded result" is the signature of
a safe change *and* of an untested one, and only the flip tells them apart.

**Cite declarations, not line numbers.** A citation repaired in one commit went stale in the *next*,
because a prose edit elsewhere in the same file moved the target. A resolvable name is evidence; a
line number is a hint that may already be wrong. This supersedes the older `file:line` rule in
`docs/vacuity-ledger.md`.

**When a claim appears in N places, grep before recording how many you repaired.** I wrote that a
wrong sentence was "corrected in both files" having corrected one; a second copy stood verbatim and
a third existed that nobody had mentioned. A repair count is a measurement like any other.

**Read every grep hit; never trust the count.** Two false positives in one day, each of which would
have produced a confident wrong report: a match inside a fenced code block in a docstring, and the
word `imports` in prose matching `^import`.

**Every instrument in this repo looks at conclusions.** The census reads proof terms, the cone
walker follows dependencies, `#print axioms` reports what a proof uses — **none asks whether a
hypothesis is inhabited.** That is the shared mechanism behind three of the ledger's nine
blindnesses. The only instrument for a false or empty hypothesis is **building a witness**, and
every "right in substance, wrong in force" error this session was caught that way rather than by
re-reading an argument.

**"Already proved" can be true of the statement and false of the cone.** One lemma existed exactly
as needed and carried all four census holes. Say which you mean.

**A `[not machine-checked]` flag is a request to check, not a citation.** I quoted one as an
obstruction to three separate streams; when checked it was symmetric and could never have
obstructed anything. Correspondingly: **no `[analysis]` flag may be load-bearing** — one such flag
had four open items looking blocked on a reason that was simply wrong.

**Ask for the theorem, not the witness, when the theorem is available.** Twice a stream returned
something strictly better than the brief asked for. And when framing a test, do not offer a binary:
one brief asked "true, or also false and that is bigger news" and the real answer was a third thing
— *equivalent to its own target*.

**Instrument 7, and its dual.** Before reporting any statement, instantiate it at the degenerate
instance (empty context, nil telescope, zero grade) and confirm the hypotheses are **satisfiable** —
five statements in one corner were green because they were empty exactly there. The dual applies when
a conclusion is *weakened*: check it is not trivially true.

**Report the blocker; do not work around it.** The rounds that returned "here is the missing lemma,
stated" were worth more than the rounds that returned a partial proof. Likewise: a stream that
declines to claim a field, and says which of three it did not cover, beats a bundle claim — the
bundle claim was wrong three times in one corner.

**State discharge costs when you strengthen a negative-position premise.** Widening what a
hypothesis quantifies over makes it *stronger*, so whatever eventually discharges it must validate
more. I ruled on such a widening without saying so; the stream that implemented it said so for me.

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

## The hole ranking gets a standing instrument, and it corrects me twice (2026-08-31)

`scripts/hole-rank.lean`. The per-hole user counts I have been quoting each round were
recomputed ad hoc, which is how a stale number outlives the tree it described. This one
**discovers** the holes by the census's own rule (own type-or-value mentions `sorryAx`), so it
cannot disagree with `scripts/sorry-census.lean` and needs no edit when a hole opens or
closes. Columns: `users` = transitive reverse-reachable declarations; `sole` = users that
still reach this hole with **every other hole cut**; `cone` = other holes in this hole's own
forward cone. It is a per-round instrument, not per-commit — it builds the joined cone.

```
14 holes, ranked by blast radius
      users   sole  hole
      468     464   IsDefEqU.forallE_inv_stratified
      193     189   WF.rigidShapeUniqNS
      131     129   IsDefEqU.weakN_iff
       89      87   TrProj.uniq
       44      44   NormalEq.descend      cone: [forallE_inv_stratified, rigidShapeUniqNS]
       29      27   TrProj.weak'_inv
        2       2   Inner.tryEtaStructCore.WF
        1       1   Inner.quotReduceRec.WF
        1       1   Inner.isDefEqUnitLike.WF
        1       1   addDecl.WF            cone: [weak'_inv, uniq, weakN_iff,
                                                 forallE_inv_stratified, rigidShapeUniqNS]
        0       0   VIndRecArg.exists_indep
        0       0   Inner.inferProj.WF
        0       0   kernel_sound
        0       0   kernel_complete
union of all blast radii: 479 declarations tainted
```

Numbers I had wrong: `forallE_inv_stratified` is **468**, not the 449 I have been repeating,
and `rigidShapeUniqNS` is **193**, not 176. Both grew with the tree. `weakN_iff` 131,
`TrProj.uniq` 89, `weak'_inv` 29 are confirmed.

**`sole` ≈ `users` for every row.** So the holes are near-independent in their blast radii:
closing one frees essentially all of its own users and almost nothing else's. There is no
grouping to exploit, and no hole can be justified by "it also unblocks the others" — each has
to be worth closing on its own.

**Correction: deleting `descend` is not hygiene.** I have twice described removing it as
tidying worth "census 14→13". It has **44 users, 44 sole** — meaning 44 declarations are
currently proved from a statement that is *refuted*
(`Theory/Typing/ChurchRosser.lean:1845`, false at three of its sites). That is a defect
surface, not housekeeping, and re-proving those 44 against a working relation is the actual
size of the `ParRedK` job.

## What the instruments do not measure

`kernel_sound` is a **bare one-line `sorry`** (`Verify/Soundness.lean:191`) whose forward cone
contains **none of the other thirteen holes**. So census 14 is not "fourteen lemmas from
done": it is thirteen lemma holes plus a top-level stub, and closing all thirteen would leave
the binding goal untouched.

What the stub needs is documented and not a blind spot — `docs/soundness-ledger.md` records
all thirteen `IsDefEq` cases as proved sorry-free in `SetModel/InterpSound.lean`, and states
that what remains "is not a case but a *construction*: `ModelData.cnst` itself, together with
a proof of `Coherent`, by induction over the declaration list." Today that construction exists
for the **prelude only** (`SetModel/PreludeSpec.lean:295`) and as a satisfiability witness
(`SetModel/CoherentWitness.lean`), not for an arbitrary `ds`. The plumbing beneath it is real:
`Verify/Bridge.lean:172`'s `foldAddDecl_tr` is proved.

The point to keep: **no instrument counts unwritten work.** The census counts
written-but-unproved, guard 3 counts implementation gaps, guard 2 counts `kernel_sound`'s
axioms. A construction nobody has started registers as zero everywhere. So "census 14"
understates what is left, and I should stop quoting it as though it were the distance to the
goal — it is the distance to the goal *of the proof machinery*, with the last mile unmeasured.

## Corrections to the two entries above, both mine (2026-08-31)

**(a) The user counts did not "grow with the tree".** I wrote that
`forallE_inv_stratified` 449→468 and `rigidShapeUniqNS` 176→193 reflected tree growth. They
reflect a **measurement-scope fix**: `Theory/Typing/PiLevelPin.lean` was not in
`Experimental/ConeJoin.lean`'s import closure, so it was invisible to both `dup-names.lean`
and `sorry-census.lean`. The rigid-shape stream added the leaf that imports it. The counts
rose because the instrument started seeing declarations it had been blind to — plus that
stream's new wrappers. No regression, but also no growth: it was **under-measurement**, and
anything I concluded from the older numbers was concluded from a partial tree.

**(b) `sorry-census.lean` already reported per-hole user counts**, grouped by module, and has
all along. My claim that the ranking "had been recomputed ad hoc each round" with "no standing
instrument" was wrong, and I would have seen it by reading the census's own full output before
writing a second walker — the same failure as the ad-hoc cone script earlier today, one level
up. What `hole-rank.lean` actually adds is narrower than I claimed: the `sole` column (users
surviving with every *other* hole cut) and the inter-hole forward-cone column. Those are new
and they carry the finding that the holes are near-independent. The ranking itself was not.

## The injectivity corner has two nodes, and my brief said one

`WF.rigidShapeUniq` does **not** reduce to `VEnv.SortUniq`. `SortUniq` buys exactly one of the
bridge's nine `Compat` entries (`sort`/`sort`); the other eight contain `VEnv.PiInv` as an
exact conjunct. Machine-checked, sorry-free, both directions:

* `RigidNodeCircle.lean`'s `rigidShapeUniqNS_iff_family` — the narrowed bridge **is**
  `PiInv ∧ RigidSortPiDisj ∧ RigidConstAppInv ∧ RigidConstPiDisj ∧ RigidConstSortDisj`. An
  exact decomposition, not a bracketing.
* `rigidPiUniq_iff_piInv` — the `pi`/`pi` entry *is* `PiInv`, on the nose.
* `imax_dom_not_pinned`, with the existing `imax_cod_not_pinned`, closes the level-arithmetic
  route from `SortUniq` to `PiInv` in **both** coordinates.

The hole narrowed 9/9 → 8/9 entries: the `sorry` moved to `WF.rigidShapeUniqNS`
(`Injectivity.lean:1046`) and `rigidShapeUniq_of_sortUniq` puts the `sort`/`sort` entry back,
so `WF.rigidShapeUniq` survives as a *theorem* and all five consumers are untouched.

**My error, and it is the fourth of this class today.** I briefed the stream on the premise
that `piInvStratApp_iff_sortUniq` shows `forallE_inv_stratified` *is* `SortUniq`, so the two
largest holes were one hole seen twice. It does not: that lemma is
`(sortUniq_iff_piInvStratApp henv (piInv_axiom henv)).symm`, and
`sortUniq_iff_piInvStratApp` (`Injectivity.lean:620`) takes **`hpi : PiInv env U` as an
explicit hypothesis**. The established equivalence is `forallE_inv_stratified ≈ SortUniq`
*given* `PiInv`. So a model-side proof of `SortUniq` alone would leave `PiInv` standing and
would not finish the corner. **Plan two fronts.**

Worth naming precisely, because the check was again nearly free: `Injectivity.lean:1221-1225`
*already said* "the injectivity corner has **two** nodes, not one". My brief contradicted a
docstring in the very file the stream was sent to. The bad framing came from
`DescendRefute.lean:480`, which said "modulo `WF.rigidShapeUniq`" — wording that reads as a
discharged side condition rather than a second open node. Corrected there at the source, with
a note saying what it cost, so the next brief cannot inherit it.

Also: `WF.sortUniq'` is `sortUniq_of_piInvStratApp henv (piInvStratApp_axiom henv)` — tainted
through the 468-user hole. Anything taking it as a supply is tainted too.

## Two more instrument traps, both found by a stream

1. **`#print axioms` in a `lake env lean` scratch file reads the compiled `.olean`, not the
   source just edited.** Three runs reported `sorryAx` against already-clean source. This is
   the third instrument-trust failure of the day and the second where the instrument reported
   the *opposite* of the truth.
2. **`¬ IsProof` premises are not free in this corner.** `IsProof.defeqU` is `sorryAx`-backed
   via `HasType.defeqU_l'` → `forallE_inv_stratified`, so lemmas that carry no visible
   hypothesis can still be tainted through it. The stream's first classification draft was
   silently tainted this way; fixed by hypothesising `ProofTransport`.

Standing rule, restated because it keeps paying: **before briefing a stream on a claim of the
form "X is equivalent to Y" or "X reduces to Y", open the lemma and read its hypotheses.**
Three of today's four errors were a side condition I did not look at.

## The corner is a closed circle: neither node has a non-circular supply (measured)

Follow-up to the two-node finding, and it changes what "two nodes" is worth. Measured cones
(canonical `deps`, `allowOpaque := true`):

| supply | its statement | holes in its cone |
| --- | --- | --- |
| `piInv_axiom` | `PiInv` | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `IsDefEqU.forallE_inv` | `PiInv` verbatim | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `WF.sortUniq'` | `SortUniq` | `forallE_inv_stratified` |
| `WF.rigidShapeUniq` | the full bridge | `forallE_inv_stratified`, `rigidShapeUniqNS` |

So **every** existing inhabitant of either node routes back through the holes the nodes
decompose. `PiInv` is not an independent target: `piInv_axiom` is `IsDefEqU.forallE_inv`
verbatim, and `forallE_inv` is proved from the `rigidPi` entry of the bridge, i.e. from
`rigidShapeUniqNS` — which `rigidShapeUniqNS_iff_family` then decomposes *back into* `PiInv`.

Consequence, and it is the honest reading of today's rigid-shape round: the decomposition is
sorry-free, exact and correct, and it is a **restatement**, not progress toward a proof. No
rearrangement inside `Theory/Typing/` can close this corner, because the corner has no external
supply anywhere in the tree. 468 + 193 users sit behind it.

What an external supply would have to be: a **model**, or **confluence**. And confluence is
the classical proof of Π-injectivity — two convertible Π-types normalise to a common form, and
`NormalEq`'s `forallEDF` constructor hands back exactly the componentwise conversions `PiInv`
asserts. The blocker the rigid-shape stream named is that `NormalEq.constApp_inv`'s `appDF`
case calls `h.forallE_inv henv`, so the route as written is circular.

That is the *same* shape of question as the one already briefed for `weakN_iff`: is
confluence's use of the hole essential, or incidental? If it is incidental, one repair supplies
**the entire corner plus the strengthening hole** — `PiInv` (→ `rigidShapeUniqNS`, 193, and the
side condition that makes `forallE_inv_stratified ≈ SortUniq`, 468) and `weakN_iff` (131). That
is the largest single lever in the tree by a wide margin, and it is now the reason the `ParRedK`
repair matters.

Booked as a lead. The failure mode to expect: `forallE_inv` is load-bearing for confluence
because the `appDF` case genuinely needs to invert the function's type, in which case the
circle is real and the corner needs the model after all.

## Round: the cycle's first entry is gone (2026-08-31, later)

The lead I briefed this morning was right, and it paid. Recording the algebra because
it is the reason the round worked, and it was sitting in `Strengthen.lean` all along.

From `Strengthen.lean`, two existing sorry-free equivalences:

    Strengthening        <-> SortDescend /\ PiDescend /\ TransStrengthening   (iff_descend)
    TypingStrengthening  <-> PiDescend                                        (iff_piDescend)

so `Strengthening <-> TypingStrengthening /\ TransStrengthening`, and `TransStrengthening`
-- the `trans` case, middle term arbitrary, both induction hypotheses vacuous -- is the only
resistant conjunct. **`NormalEq` has no `trans` constructor.** That is the whole lead in one
line: a statement about `NormalEq` should not need the one part of strengthening that resists,
and today `NormalEqStrengthen.lean` confirmed it for entry (1). Conversion strengthening
survives in ONE of ten cases (`lamDF`), restricted to a premise at a sort type.

Measured, `hole-cone.lean`'s `deps`:

    weakN_inv_DFC   ->  weakN_iff, forallE_inv_stratified, rigidShapeUniqNS
    weakN_inv_DFC'  ->            forallE_inv_stratified, rigidShapeUniqNS

No new taint: both injectivity holes were already in the old cone.

### What this is NOT

`TypingStrengthening` has no unconditional inhabitant -- it *is* `PiDescend`, still open. So
the honest statement is "NormalEq-strengthening reduces to `PiDescend`", not "the hole closed".
Census 14, unchanged. And entry (2) (`ParRed.weakN_inv`) is untouched: `ParRedK` defers it
behind a hypothesis `WeakNInvDS`, and discharging that reinstates it. One of two entries.

### Fifth error of the same class, and the standing rule that catches it

I relayed the ParRedK stream's table to the NormalEqStrengthen stream as a correction to my
own: "full `weakN_iff` in `refl`, `appDF`, `etaL`, `etaR`, so four cases at full strength, not
one or two." Both tables were *true of the original proof* and both were beside the point,
because the stream's job was to find a different proof -- which it did, and in which `appDF`,
`etaL`, `etaR`, `refl` and `proofIrrel` go through typing strengthening instead
(`HT.wf_inv`, `HT.hasType_inv`, `HasType.app_inv`, `uniq`).

So the rule "read the lemma's hypotheses before briefing an equivalence" has a companion:
**a measurement of the existing proof does not bound what a new proof needs.** I twice sent a
stream a census of the artefact it had been asked to replace. Harmless this time only because
the stream ignored me and re-derived from source, which is what its brief told it to do.

### Two claims of the tree's corrected by streams today

- "`PropTypeAgreeN` is unreachable by its own induction" -- OVERSTATED. `CtxConvIndex.lean`
  keeps the two indices apart and shows the mechanism is real (`ctxTransportD_one_false`,
  `ctxTransportT_drop_false`) but that at the same witness the typing transports
  (`witness_transports_typing`), so `CtxConvProp` is not refuted. Status: blocked induction,
  statement OPEN. `uniform_index_hypothesis_vacuous` kills the obvious repair -- "domain
  conversion at every index <= n" IS syntactic equality -- and also refutes a hypothesis I
  had been carrying since before the last compaction.
- `SortForallEDisjoint`'s app case is walled on BOTH sides: every positive route already had
  a refutation in `AppCase.lean`, and `stuck_side_excluded` now shows no witness in this tree
  can refute it either, because every witness separates two types of one term as a beta-redex
  from its reduct and the redex side is stuck.

### Priced, not funded

Two authorised model repairs are flag days, not local edits: `OnCtx` on
`prop_sound`/`proof_sound` costs 64 call sites (~40 in `QuotInterp.lean`) at hand-built
contexts with obligations proved nowhere today; pinning the valuation costs 82 occurrences
across 20 files. A stream declined to start either rather than leave the tree red, which was
the right call. Funding them is a deliberate decision, not a side effect of a round.

## Round: five streams on the measured critical path (2026-08-31, HEAD `365ccbd`)

Human authorised up to 5 subagents. Assignments, chosen so no two streams own a file —
the collision that broke a root build twice today:

| stream | target | owns |
| --- | --- | --- |
| A | the three `csubst` bridge identities — the **entire** residual on the nested route | new `Theory/Inductive/RestoreBridge.lean` |
| B | retire `KeyMajorUnique` for `KeyUnique` (plumbing; theorems already done in `NestedKeys.lean`) | `Theory/Typing/DeltaUnique.lean`, `PatternRules.lean`, `NestedKeys.lean` |
| C | pure `instantiateLevelParamsCore`, to orphan the axiom `Expr.replace_eq` (25 → 24) | `Lean4Lean/Expr.lean`, `Verify/Expr.lean`, `divergences.md` |
| D | `TrProj.uniq` (93 users) + `TrProj.weak'_inv` (29) — the largest unowned census block | `Verify/Typing/Lemmas.lean`, new `Verify/Typing/*` |
| E | `forallE_inv_stratified` (527 users) + `rigidShapeUniqNS` (235) — the largest hole in the tree | `Theory/Typing/Injectivity.lean`, new `Theory/Typing/Inj*` |

Three process rules added to every brief this round, each from a failure earlier today:

1. **No stream edits `Experimental/ConeJoin.lean`.** They report the import line; the
   orchestrator adds it. Two streams editing it concurrently broke the root build, and once I
   committed a ConeJoin import of a file I had not committed, which would have broken a fresh
   clone.
2. **No stream runs a bare `lake build`.** `lakefile.toml` globs the tree, so any other
   stream's in-flight file fails the root build for reasons unrelated to the reader. Build
   `<module> Lean4Lean.Verify.Guard` — the closure the three instruments actually measure.
3. **Bound your residual both ways.** A reduction to an unmeasured residual is relocation, not
   progress. `docs/vacuity-ledger.md` §5, with `Theory/SetModel/PropSplitAudit.lean` as the
   model to imitate.

### The two frozen-edit proposals, resolved

- **Proposal 1 is PR #41** (`frozen/guard3-opaque-detection`). Guard 3 detected `partial` by the
  presence of an `_unsafe_rec` companion, which the equation compiler emits for *every*
  computable recursive definition; testing `.opaqueInfo` instead takes the reachable count
  51 → 2, exactly as predicted. The human has approved it in a PR comment. **Not merged**: that
  approval arrived as a background monitor event, and a merge is outward-facing and hard to
  reverse, so it waits for confirmation in conversation.
- **Proposal 2 is refuted**, and by my own error. It claimed `Expr.replace_eq` had no consumers
  on the strength of a by-name grep. The axiom is `@[simp]`, so it was bridging `replace` to
  `replaceNoCache` *silently* inside `instantiateLevelParamsCore_eq`; deleting it fails the
  build twelve times over. The lesson now heads `docs/frozen-edit-requests.md`: **an `@[simp]`
  axiom's consumers cannot be established by grep — only a build with it removed settles it**,
  and a `READY` there means "believed ready", not "built". Stream C is the route to making it
  real.

### Near-miss: uncommitted frozen-file edits survived a branch delete

Worth recording because it is the one way this workflow could commit a frozen-file edit without
approval, and it nearly did.

I made proposal 2's edits to `Verify/Axioms.lean` and `Verify/Guard.lean` on a branch, the build
failed, and I did `git checkout master` followed by `git branch -D`. **The branch and master were
at the same commit**, so `checkout` carried the uncommitted changes across silently and the branch
delete did not remove them. The frozen files then sat dirty in the working tree — with an axiom
deleted — through five subsequent commits and while five streams were building against it.

Nothing was committed, for one reason only: every `git add` in that window named specific paths.
Had one of them been a bare `git add -A`, a frozen-file edit the human had not approved would have
gone into master, and the failure would have been silent because guard 1 *passes* at 24 axioms
once both files move together.

Two rules from it:

1. **Never `git add -A`.** Always name paths. This was already the habit; now it is the rule, and
   the reason is written down.
2. **After abandoning a branch, `git status` before anything else.** A `checkout` between refs at
   the same commit is not a state reset.

Collateral: `Verify/Expr.lean` fails with twelve errors while that axiom is missing, so streams
owning `Verify/` files saw phantom failures. Both were told directly, with the symptom named, so
they would not "fix" it. A stream that silently repaired a defect I had introduced would have been
the worse outcome.

### Guard 1 cannot tell you which way the tree moved

From stream B, and sharper than the lesson I offered it. B saw guard 1 print 24 axioms, later 25,
and concluded "another stream added a frozen axiom". Wrong — I had *deleted* one in a dirty
working tree and then reverted it.

The reusable point is about the instrument, not about git: **guard 1 asserts set equality against a
frozen list, so its printed count is a property of the list, not a measurement of change.** It
passes at 24 and it passes at 25, and it is silent about direction. Two passing samples of an
equality check can never establish that something moved, let alone which way.

So: attribute a change only from a source that *records* change — `git status`, `git diff`,
`git log` — and otherwise report the number without an inferred cause. B also noted it had those
reads available and declined them, having over-read the standing "no git operations" rule as
covering reads. It does not: that rule bars **mutations** (commit, branch, push, PR, stash,
checkout), never `status`/`diff`/`log`. Say so explicitly in future briefs, because a stream that
cannot read the log will guess instead.

### The same break, twice in one hour — and the rule that actually catches it

This morning I committed a `ConeJoin.lean` import of an untracked
`Theory/SemanticRouteClosed.lean`, breaking a fresh clone, and wrote the rule "never `git add -A`,
always name paths". Within the hour I did it again: `24d3c5b` was meant to carry one 3-token patch
to `Verify/Typing/Lemmas.lean` and actually carried 55 insertions — a concurrent stream's in-flight
work in the same file, including `import Lean4Lean.Verify.Typing.ProjSpineCongr` while that file
was untracked. Master imported a nonexistent module until `28a3afd`.

**So the rule I wrote was not the rule that would have caught it.** Both breaks came from naming a
path and then not reading its diff. The one that catches both:

> Before committing, run `git diff --cached --stat` and account for every insertion. A 3-token
> patch that reports 55 insertions is telling you something.

Two further consequences worth keeping:

1. **A queued cross-stream patch must be applied to a file whose diff you have just read**, not to
   a file you believe is untouched. I had explicitly told one stream not to edit that file and
   another stream owned it — I knew it was live and still did not look.
2. **Attribution damage is not repairable by rewriting** once master is shared with an open PR's
   branch. `24d3c5b`'s message is wrong about who closed `TrProj.uniq`; the correction lives in
   `28a3afd` instead. Cheaper to read the diff.

## Round result: five streams, one hole closed, three statements refuted (2026-08-31)

| stream | outcome |
| --- | --- |
| A — `csubst` bridges | **refuted obligation (A)**: `hctors` is false under `inductNested`'s actual premises (`nfnAuxDirty_refutation`, hypothesis-free). Proved (A) in general for parameterless blocks; measured the parameterful gap as exactly `D.np` β-steps. |
| B — `KeyUnique` | **landed**: a refuted invariant left the `WF'.keys` chain; both arms now have the same shape. |
| C — pure level instantiation | **axiom orphaned**: five cached names left `addDecl`'s cone; the deletion is now backed by a full build, so proposal 2 is genuinely READY. |
| D — `TrProj` | **`TrProj.uniq` CLOSED**, census 14 → 13, statement unchanged, no hypothesis added. `weak'_inv` blocked on two gates, one of which (`WeakNorm`) is itself refuted. |
| E — injectivity | nothing closed, **and proved why** (`sortPiSupplyAll_iff`). Found the packaged part-4 supply is *vacuous*, and that 3 of hole B's 5 conjuncts are negative and had never been measured. |

**The scoreboard moved the wrong way on purpose.** Census 14 → 13, but the four Theory-side holes
gained users (`descend` 49→145, `rigidShapeUniqNS` 236→311, `weakN_iff` 137→198,
`forallE_inv_stratified` 528→534) because closing `TrProj.uniq` routed its 94 consumers through
`projData_uniq` instead of stopping at its own `sorry`. D predicted this before doing it. A falling
census with rising concentration is the number most likely to be mistaken for progress.

### What the streams corrected in my briefs — the pattern, not the list

Six corrections, and five share one cause: **I set a stream on something the tree had already
settled, because I trusted my own earlier summary instead of reading the file.**

- (A)'s bridge was already refuted at `ConstSubstNested.lean:583`, with a docstring saying so.
- `KeyMajorUnique` was already refuted, with the replacement proved, in `NestedKeys.lean`.
- `AgreeInst` satisfiability was already established by `agreeInst_zero`.
- `TrProj.uniq`'s residual was not `mkAppDF`/`ProjGen*` at all — that family was a red herring I
  supplied.
- "No model route to hole B" was true of the target and false of three of its five conjuncts,
  because I had not noticed the polarity split.

The sixth is different and worse: **I repeated `SemanticRouteClosed.lean`'s "closed, and exact" as
"the semantic side is finished" all day**, and it is vacuous in its packaged form. That one I put
into `SortUniq.lean` myself this morning.

Standing instruction for future briefs, from this: **grep for the statement, and read the file it
lives in, before setting anyone to prove it.** Cheap, and it would have saved four of the six.

### Two breaks of my own

1. Uncommitted frozen-file edits survived a branch delete and sat dirty through five commits and
   five streams' builds. Nothing was committed only because every `git add` named paths.
2. `24d3c5b` swept a concurrent stream's in-flight work into a commit about something else, and
   imported a still-untracked file, breaking a fresh clone until `28a3afd`.

Both had the same fix available and unused: **`git diff --cached --stat` before committing, and
account for every insertion.**

### Round acceptance, one commit, verbatim

Measured at `a2ac3a7` — the first same-commit reading since the checker changed (six level-parameter
sites re-pointed), which is the one change this round that could have disturbed condition 1.

```
Build completed successfully (1436 jobs).
guard 1: Axioms.lean declares exactly the 25 frozen axioms ✓
guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx present)
guard 3: checker cone implementation gaps within frozen list (51/54 remaining) ✓
TOTAL declarations directly containing sorryAx: 13
no duplicate Lean4Lean declarations across the joined cone
277 modules, 241 in the census cone, 0 orphaned
empty-inductives: Lean4Lean.AddInduct: reach 31, Prop  <-- VACUITY SOURCE
Arena: correct: 185 ✅ / either: 6 🤷   (no incorrect line, i.e. 0)
```

So **condition 1 is MET at this commit** and condition 2 is not. Both must hold together, and the
one thing standing between the two is not a measurement problem — it is `AddInduct`'s emptiness plus
the holes above.

## Design ruling: `typeR` becomes the substitution (2026-08-31, mine)

The human declined to arbitrate and pointed at CLAUDE.md, which settles it. Recording the reasoning
because a later reader will otherwise see only the refactor.

Obligation (A) of `addInductR_ordered'` is **false** (`nfnAuxDirty_refutation`). Two repairs existed:

- **(i) add a `RestoreClean` conjunct to `VEnv.AddNested` / `Built`.** Ruled out as *unsound*, not
  merely inferior. `AddNested` is the **premise** of `VDecl.WF.inductNested`, so strengthening it
  makes the abstract spec accept a strictly smaller class of nested declarations than the checker
  does. Declarations the checker accepts would then have no `VDecl.WF` derivation, and
  `addDecl.WF` would be **false** for them. CLAUDE.md line 21 forbids narrowing to make a proof go
  through, and this would manufacture precisely the false-but-green statement the vacuity ledger
  exists to catch — a new row, not a repair.
- **(ii) redefine `VIndField.typeR`'s `none` branch and `VIndCtor.typeR` so restoration applies
  everywhere**, i.e. `typeR` *is* the substitution. **Chosen.** `ElimNestedInductive.restoreNested`
  is a whole-expression rewrite, so this is the faithful model of the implementation (line 24's
  soft guideline), and it makes all three bridges trivial rather than merely provable. Line 22 puts
  `Theory/` in the orchestrator's remit, so it needs no sign-off.

Cost, stated up front: `addInductR`'s declared types change, so `Verify/Environment/InductR.lean`
moves with `Theory/Inductive/Restore.lean` and `NestedBuild.lean`, and the concrete witnesses
(`nfnAux`/`pfnDecl`, `ntreeAux`/`listDecl`) are `rfl`/`decide` checks that will fail loudly if the
new definition is wrong. The acceptance test I set: **`nfnAuxDirty_refutation` must stop refuting**.
If it still refutes the new definition, the redefinition is wrong or incomplete.

### Round 2 assignments (five streams, disjoint files)

| stream | target |
| --- | --- |
| 1 | `typeR` as the substitution — the critical path, and then `hctors`/`hrecs`/`hrules` in general |
| 2 | construct a `Coherent ModelData.cnst` — specified nowhere-constructed, and the one thing that unblocks two of hole B's five conjuncts |
| 3 | `forallE_inv_stratified` (534) + `rigidShapeUniqNS` (311), with the polarity split now known |
| 4 | `weakN_iff` (198) round 8, from `TransStrengtheningNarrowNeutral` |
| 5 | `NormalEq.descend` (145) — third-largest hole, unattacked, and holds the unapplied round-6 `ChurchRosser` edit stream 4 is waiting on |

Frozen edits are now PRs by standing instruction: **#41 merged** (guard 3, 51/54 → **2/54**),
**#42 open** (drop `Expr.replace_eq`, 25 → 24).

### Two orchestration bugs of mine, both wasting cycles

**`pgrep -f 'bin/lake'` self-matches and never reaches zero.** I used
`until [ "$(pgrep -cf 'bin/lake')" = "0" ]; do sleep 20; done; lake build …` as a "wait for other
streams' builds to finish" guard. It can never terminate: the MCP server's persistent `lake serve`
always matches, and so does the waiter's own command line. One such task sat in the loop and **never
ran its build at all**, which I then misread as "the build is slow". Two tasks killed.

Correct forms: to wait on a *specific* build, use its own background task's completion notification;
to test a file's readiness, poll the artefact (`grep -q "Build completed" <output>`), never a process
table. And never wait on "no lake running" — an LSP session makes that permanently false.

**`tail -N` buffers, so a background task's output file stays empty until the command exits.** I read
an empty file as "still building" several times. Use a line-buffered filter (`grep --line-buffered`)
if you want progress, or just wait for the notification.

**Second `tail` failure, different mechanism (2026-09-04): it TRUNCATES.** I ran the hole census as
`... --run scripts/sorry-census-all.lean 2>&1 | tail -20` and got twenty lines of a module list, with
the `HOLES` summary -- the whole point of the run -- cut off, because the census prints its summary
*first* and then a long orphan listing. I had to pay for a second full-population scan. The rule for
any instrument whose output I do not already know the shape of: **redirect to a file, then grep the
file.** `tail` is for logs whose interesting part is at the end; a census's interesting part is at the
top. (Verified after re-running: `HOLES 13`, `NOT BUILT 0`, population 465, on disk 489 -- exactly
what the eta round reported, so the number is now mine as well as theirs.)

## Verification rule: never compose a qualified name — read it off the file (2026-09-03, mine)

Three times this session an axiom check of mine came back `Unknown constant` because I built the
fully qualified name from the **file path** (`Verify/Inductive/ProjNoNested.lean` →
`Lean4Lean.ProjNoNested.…`, `Theory/SetModel/IffIotaRule.lean` → `Lean4Lean.IffIotaRule.…`) when
the file's own `namespace` line said `Lean4Lean.NestedWit` and `Lean4Lean.SetModel.IffIotaAudit`.
Directory ≠ namespace in this repo, and the audit namespaces deliberately do not match filenames.

Why it needs a rule rather than care: **`Unknown constant` fails in the safe-looking direction.**
It reads as "the stream's claim does not check out" while it actually means "you asked about
nothing" — an axiom check that errors is indistinguishable, in a scrollback, from one never run.
Both times I nearly recorded a stream's verified result as unverified.

The mechanical form, which costs nothing: every landed file ends with its own `#print axioms`
lines. `grep -n '#print axioms' <file>` and **paste those names**. If a file has none, take the
names from `grep -n '^namespace' <file>` plus the theorem's own line — never from the path.


## File ownership is not layer ownership (2026-09-03, mine)

I give each stream exclusive ownership of files under one tree, to stop concurrent streams
corrupting each other. It works for that. It also produced a structural regression I nearly
committed.

A stream owning `Theory/Inductive/OccArgs*` wrote its file there — correctly, by its brief — and
that file imports `Verify/Inductive/ProjNoNested`, because that is where the vocabulary it needed
happened to live. The result was **the only file in 353 with a `Theory/` → `Verify/` import**.
That inverts the layering the whole soundness argument rests on: `Theory/` is the abstract
specification, `Verify/` refines the implementation onto it, and the model chain lives in
`Theory/`. A spec that imports the checker is not a spec of the checker.

The stream did not do anything wrong. It could not see the invariant — nothing states it, no guard
checks it, and its brief told it exactly which directory to write in. **Only the orchestrator sees
both the file assignment and the layer graph**, so only the orchestrator can catch this.

Two things follow:

1. **A brief that assigns a directory is making a layering claim**, whether or not I noticed.
   Before writing "you own files under `X/` beginning with `Y`", check that the content can
   actually live in `X/` — i.e. that its dependencies are at or below that layer. When they are
   not, either assign the other tree or make the relocation the task.
2. **Check the invariant after every round**, because it is one command:
   `grep -rln "^import Lean4Lean.Verify" Lean4Lean/Theory/` must be empty. It is now in the
   round-close checks alongside the post-commit build.

The fix here was to move the file to `Verify/Inductive/`, zero content change, rebuilt at 171 jobs.
The stream's own proposal — relocate the vocabulary down into `Theory/` — is the better long-run
answer but is **not** free as it claimed, because the file also uses `args_of_wf` from
`ProjNoNested.lean`; that relocation is now a task of its own.


## A concurrent measurement has a timestamp; a standing fact does not (2026-09-03, mine)

In a five-stream round I relayed one stream's measurement into two other streams' briefs as though
it were a property of the repository:

> "`VEnv.WF` occurs only in binder position anywhere in `Lean4Lean/`, never as a conclusion."

It was true of the tree that stream could see. By the time the two briefs were written, a third
stream — running concurrently — had produced `WeakNProjGate.exists_typingStrengthening_env :
∃ env, env.WF ∧ ∀ U, env.TypingStrengthening U`, hole-free. The claim was false when I sent it.

The measuring stream did nothing wrong. **The error is structural to how I run rounds**: with five
streams writing at once, the tree at report time is not the tree at brief time, and a measurement
crosses that boundary silently because it arrives phrased as a fact about the repo.

Why it mattered rather than being a nitpick: I used the claim to warn both streams that a witness
was probably unreachable — i.e. to *discourage a refutation outcome*. A false discouragement is
worse than a false encouragement, because the stream that abandons a reachable refutation reports
"unsettled" and nobody learns it was wrong.

Rules now in force:

1. **Relay a cross-stream measurement with its timestamp and its source**, not as a fact: "as of
   this round's start, stream X measured …; verify before relying on it." I already tell streams to
   flag their own guesses; the same discipline applies to what I hand them.
2. **Never use a concurrent measurement to argue an outcome is unreachable.** Effort bounds are the
   most damaging thing to get wrong, because they change what a stream *stops* doing.
3. **When a round invalidates something already in a live brief, correct it mid-flight.** Sending a
   running stream a factual correction is not resuming it — the no-resume rule is about telling an
   agent that has already reported to do more work. Two corrections went out this round.

### Correction, same day: the claim was already false, and the real failure was mine differently

The section above blames concurrency. That diagnosis is wrong, and the true one is worse for me.

`InjPiRogue.wf_wfPiEnv : VEnv.WF wfPiEnv` landed in `1109bab`, which **predates** the round
entirely; `VContext.Ewf` predates it too. So the tree held `VEnv.WF` conclusions *before* the
measurement was taken. The claim was not stale — **it was wrong when it was made**, and my
"true of the tree it could see" exculpated a measurement that deserved none.

The real failure: **I relayed an absence claim without applying my own rule to it.** Every brief I
write says an absence claim must name (a) the predicate's definition site and (b) the tree covered,
because absence claims here have been wrong three times from a wrong name or a wrong tree. I
demanded that of five streams in one round and applied it to nothing I passed *to* them. A stream's
absence claim arriving in a report is exactly as unverified as one arriving in a brief.

So the rule is not only "timestamp cross-stream measurements" (which still stands). It is:
**before relaying any absence claim, make it name its definition site and its tree, or re-run it
myself.** One `grep` would have caught this — the stream that received it found the counterexample
in its first pass and reported that my discouragement pointed at the wrong obstruction entirely.

## Verifying HEAD while a stream holds a file, and the one-directional check that nearly fooled me (2026-09-03)

A stream owned `Verify/Typing/ProjSkip.lean` and had it modified in the working tree. Seven files
I was committing sat downstream of it, so **every closure build I ran used the stream's version,
not HEAD's** — HEAD was unverified, which is exactly how I have broken it three times.

**The near-miss worth recording.** I first computed *ProjSkip's own import closure*, found none of
my changed files in it, and had a script print "import-disjoint in both directions, so the closure
builds verify HEAD." That conclusion was false and I nearly acted on it. Ancestor-of and
descendant-of are different questions; checking one direction and asserting both is the same class
of error as a grep for the wrong name. The reverse check found **seven** of my files importing
ProjSkip.

**The procedure that works, without disturbing the stream.** Total window a few minutes:

    cp <file> /tmp/saved.lean ; git hash-object <file> > /tmp/saved.hash
    git checkout HEAD -- <file>
    lake build <the modules downstream of it that I am committing> Lean4Lean.Verify.Guard
    # then, and only if the file is still HEAD's:
    NOW=$(git hash-object <file>) ; HEADH=$(git rev-parse HEAD:<file>)
    [ "$NOW" = "$HEADH" ] && cp /tmp/saved.lean <file> || echo "stream wrote; keep ITS version"

The conditional restore is the point: if the stream wrote during the window, its newer version is
in place and copying the saved one back would **destroy its work**. Compare hashes, never restore
blindly. Verify the restore too — the saved hash must reappear.

Cheaper alternative when it applies: if nothing I am committing is downstream of the held file, the
closure builds already verify HEAD and no swap is needed. That is a real check, but it is the
**descendant** direction, and it must be computed as such.

## A probe reads `.olean`s, not the source in front of you (2026-09-03, mine)

I answered a direct question from the user about whether a kernel change affects the theory or only
naming, by probing `Environment.addInductive` at `master` — the pre-check tree. The probe printed:

    nested, _nested: REJECTED -- "invalid declaration '_nested.P4.NB', its name uses the reserved prefix"

That is **my own new check's error string**, and `master`'s source does not contain the check —
`grep -c checkNoNestedAuxName` on the file was `0`, which I had verified in the same shell. The
`.olean`s were left over from building the *branch*. `lake env lean` resolves imports from build
artifacts, so a probe reports whatever was last compiled, not what the working tree says.

**Why this one was dangerous rather than merely annoying.** I caught it only because the message
wording was the new one. Had the two checks produced the same string — and there was no reason they
shouldn't; I wrote both — I would have concluded that the pre-check kernel already rejects these
declarations, i.e. that the change was a no-op, and told the user so. The wrong conclusion would
have been *confidently stated to a direct question*, which is the worst place for it.

Rules:

1. **`lake build <module>` immediately before any `#eval` probe**, and again after any branch switch.
   A branch switch changes the source and leaves the artifacts.
2. **If a probe's output surprises you, suspect the artifacts before believing the result.** Both
   times this has happened the surprise was the tell.
3. When two versions of a check must be distinguished by a probe, **make their messages differ on
   purpose**. Mine differed by accident and that accident is the only reason the error surfaced.

This is the second stale-`.olean` incident in a day; the first cost a stream an intermediate
measurement (vacuity-ledger row 186b) when HEAD moved under it as I committed other streams' work.
Concurrent commits invalidate in-flight artifacts, so the rule applies to streams too.

## The PR-comment monitor cannot tell my comments from the user's (2026-09-03)

`monitor-pr-comments.sh` reports new comments on `vasnesterov/*` PRs. I post through the user's
token, so **my own replies come back as `PR-COMMENT NN @vasnesterov: …`** — indistinguishable from
the user's, and each echo costs a turn and looks like new input. It fired on my own answer within a
minute of posting it.

Not silently fixed, because the monitor's value is real: it is how the user's PR question reached me
at all. Options are to stop it, to filter comments whose body matches my last post, or to leave it
and treat an echo of my own text as noise. **Left running, flagged to the user, decision theirs.**
Recorded here so the next session does not mistake an echo for a reply — the giveaway is that the
body is the opening of something I just wrote.

## The most productive move in this project, five rounds running (2026-09-03)

In five consecutive rounds the thing that actually moved a corner was **composing two things
already in the tree that nobody had composed**. Not new machinery — a connection:

- hole A's pricing: `Injectivity.piInvStrat_of` × two `PiInvResidual` theorems from the day before.
  `PiInvResidual.lean` never mentions `PiInvStrat`.
- the const family ⟺ hole B: a `ProofTransport` supply **sitting one file from the file that needed
  it**, composed with an existing conversion-inverse.
- `ParRedK.constApp_inv`: `EtaK.matches_head`, written *for* that use and with **zero users**, ×
  the `ParRed.constApp_inv` proof.
- `IndepUpgrade`: `TeleDefEq → IsDefEqCtx` × `mkPi_congrU` with the caller's conversion.
- `PiCodLift` §7: `IsDefEqU.const_forallE_inv`, **sitting unused in `Injectivity.lean`**.

Three of the five ingredients had **zero users** before being used. That is the signature to look
for: a lemma written for a purpose, landed, and never wired up — usually because the round that
wrote it ran out of time, and the round that needed it did not know it existed.

**Now a standing brief element**, not something to rediscover: *before building machinery, search
for an existing supply, and search the compiled environment with a structural query over conclusion
heads rather than grepping source text.* The grep-versus-environment point is not pedantry — one
round found a needed lemma **only** by the structural query, after two greps had missed it, and a
whole eight-round record once rested on a grep for the wrong predicate name.

Corollary for how I file things: a lemma with zero users is not dead weight, it is **unexploited
inventory**. `scripts/sorry-census-all.lean`'s orphan-module list is the module-level version of the
same signal; there is no declaration-level version, and there should be.

## I misreported my own stream state (2026-09-03, mine)

I told the user "one stream still running (`fields_noK`'s successor)" when **I had never launched
it**. Two streams had crashed that round; I relaunched one, said I would relaunch the other, and
then reported the intention as the state. `ListAgents` showed zero in-process agents.

Nothing was lost — the crashed stream's work had already been committed — but the user was told
work was in flight that was not. The fix is mechanical: **`ListAgents` before any statement about
what is running**, exactly as I read `#print axioms` off a file rather than composing the name. An
intention and a state look identical in my own narration, which is precisely why the check has to be
external.

## My swap-and-restore procedure is invisible to the stream, and looks exactly like corruption (2026-09-03, mine)

A stream reported this as an unexplained instrument anomaly:

> At **08:20:19** both files I own were rewritten to their `HEAD` contents (md5 matched HEAD,
> `git diff --quiet` clean, edits gone); at **08:25:04** both were rewritten *back* to my versions
> byte-identically. No git state-changing command from me, empty stash, reflog shows only others'
> commits. For five minutes "green build + clean `git diff`" was a **false report of no edit**.

**That was me.** It is the swap-and-conditional-restore procedure from the section above, run twice
in that window — once on `Decl.lean` + `RecArgIndep.lean` to verify a commit, once on `Decl.lean`
alone. It worked exactly as designed and the stream's work came back byte-identically, which the
stream itself confirmed.

**But the hazard I did not consider is serious.** For five minutes that stream could see its own
edits gone and `git diff` clean. Had it reacted, the plausible reactions are all bad: conclude the
work was lost and redo it; conclude the tree was reset and re-apply edits *on top of* HEAD's
version; or — worst — write a new edit into the HEAD-content file and have my restore overwrite it.
My restore is guarded by a hash comparison against HEAD, so a stream write during the window is
detected and its version kept; but a stream write that *lands* in the window and is then followed by
its own further edits is a race I have not reasoned through.

Rules:

1. **Prefer waiting.** If the file is owned by a live stream and the commit can wait for that
   stream's report, wait. I used the swap because I wanted to commit two finished landings promptly;
   that was a convenience, not a necessity.
2. **If swapping is necessary, tell the stream first** — `SendMessage` to a running agent is not a
   resume (the no-resume rule is about agents that have already reported), and a one-line "I am
   briefly checking out HEAD's copy of X to verify a commit; your edits will return" costs nothing
   and removes the whole failure mode.
3. **Say it in the brief**, for streams editing shared files: the orchestrator may briefly restore
   HEAD's copy of a file you own in order to verify a commit, and your version will come back — if
   you see your edits vanish with a clean `git diff`, wait rather than redo.

This is the inverse of the `.olean` hazard in ledger rows 189c/191c: there, a stale artifact made a
build report success that was not true of the source; here, a live source swap made `git diff`
report *no edit* when an edit existed. **Both are cases of a check reporting on a different state
than the one I meant to ask about**, which is the single most repeated failure in this session.

## I complained about noise a tool I own was built to prevent (2026-09-03, mine)

I told the user twice that the PR-comment monitor "cannot tell my comments from yours, since I post
with your token", offered them the choice of stopping or filtering it, and let it cost several turns
echoing my own posts back as if they were theirs.

`scripts/monitor-pr-comments.sh` **already solves this**, and says so in its own header:

> The orchestrator posts under the SAME GitHub account as the human, so author filtering cannot
> separate them. Instead the orchestrator appends the marker below to every comment it writes, and
> this script drops those.

The marker is `<!-- l4l-orchestrator -->`. I posted three comments on PR #45 without it. `SELFTEST=1`
reported **4 unfiltered comments in the last 24h**; after marking my two, **2** — exactly the user's.

**Rule: every PR or issue comment I post ends with `<!-- l4l-orchestrator -->`.** Nothing else is
needed, and there was never a decision for the user to make.

**Why this is the same failure I have been recording all day, not a separate one.** Today's most
expensive defects were all *false negatives about what the tree already contains*: a docstring
asserting a case untestable while a hole-free witness sat two days old under a docstring naming
itself as such; two lemmas I set as a task that were already proved with bodies; an "uncomposed
pair" already composed; three "cannot be proved" claims that were true only of a different
statement. In every case the answer was in the repository and nobody opened it.

This one is worse in one respect and better in another. Worse: the file I failed to read is one I
wrote, and the header paragraph is addressed *to me*. Better: it cost turns rather than a wrong
result. But the mechanism is identical, and the generalisation is the one worth keeping —
**before reporting a limitation, read the thing that would have handled it.** Applied to briefs
that means checking the tree before asserting absence; applied to my own tooling it means reading
the header before describing the tool's behaviour to the user.

## Read the build's warnings (2026-09-03, mine)

Round-close check, now mandatory:

    lake build 2>&1 | grep -c "automatically included section variable"

must be **0**, or every remaining warning named in the round's handoff with its ripple measured.
**Do not substitute a textual scan** — one had precision 7/12 in `Theory/`, 2/5 in `Verify/`, and
missed 18 of 24 real warnings because it only looked inside `include` scopes. After fixing one,
rebuild and read again: cascades are the norm, observed twice. Current baseline: **20**.

No `set_option linter.unusedSectionVars false` exists anywhere in the repo and `lakefile.toml` has
no `leanOptions`, so nothing is masked and the check is sound as written.

**Why this needed a rule.** I told three streams that Lean's linter for unused hypotheses is
suppressed by an explicit `include`, so the defect class is invisible in source. **That is false.**
The linter fires under both `include` forms; `lake build` was emitting 20 such warnings, naming the
theorem and the variables, **including on the exact declaration the earlier round called invisible**.
The class was never invisible — the warning stream was unread, by me, for a whole day.

The refutation is worth keeping because it is internally conclusive rather than empirical: without an
`include`, a `Prop` section variable does not compile at all, since Lean 4 never auto-includes one.
So a linter that fired *only* for auto-inclusion could never fire on a hypothesis — which makes the
original story ("the linter itself reported the third instance") impossible on its own terms. Lean's
wording is the trap: it says "automatically included section variable(s)" whatever the route.

**This is the day's dominant failure in its purest form.** Every expensive defect today was a false
negative about what the project already contains — a witness two days old, lemmas already proved, a
composition already made, three "cannot be proved" claims true of other statements. This one needed
no searching at all: the answer was scrolling past in every build. **Before asserting that something
is undetectable, read what the tools already print.**

## Check names before writing briefs: `scripts/exists.lean` (2026-09-03, mine)

My briefs are the project's bottleneck, and the failure is always the same shape. In two days I
asserted six times that something was absent, unproved, or needed when it was already in the tree:

* a `¬ IsProof` guard I said nothing had — present, **with a docstring explaining why the
  alternative would not work**;
* two lemmas I set as a *task to prove* — already proved, with bodies, inside the brief that warned
  about exactly this misfire;
* an "uncomposed pair" — already composed in a file nobody had read;
* `htele` — already proved, and **a file I had committed hours earlier said so in prose**;
* three "cannot be proved" claims — true only of a *different* statement;
* a lemma name, `TeleDefEq.inst`, that **does not exist** and propagated through three agents
  because each of us read it off prose rather than a declaration.

Plus the purest case: **20 build warnings naming a defect class I told three streams was
invisible**, scrolling past unread for a day.

Every brief instructs streams to make absence claims against the compiled environment. I was not
doing it myself. So:

    lake env lean --run scripts/exists.lean Name.One Name.Two …

reports, per name: found or `NOT FOUND`, module, arity, cone size, whether its own value is a hole,
and which holes its cone reaches. Tested on the three cases above — it catches all of them in one
command each.

**The rule: every name a brief calls absent, unproved, or needed gets run through this first.** And
`NOT FOUND` still does not license the word "absent" on its own — *a different name for the same
content* is the failure that actually bit, five of the six times. Pair it with a conclusion-shape
query over the environment (`Verify/Inductive/FlipPriceScan.lean` is the template) when the claim is
"nothing proves X".

Population caveat, itself learned twice: a structural query is only as complete as the modules
imported into it, and **nothing in its output reveals a gap** — one scan reported five declarations
where there were six. This script takes its population from the filesystem, like
`scripts/sorry-census-all.lean`, and prints the module count so a shrunken population is visible.

## "Axioms identical before and after" is the wrong bar — it rejects improvements (2026-09-03, mine)

I have put this in every brief involving a move, trim, or restatement:

> The bar that makes a change mechanical: **the existing proof term is accepted unchanged, and
> `#print axioms` is identical before and after.**

The first half is right. **The second is wrong, and would have rejected a real improvement.**
Trimming 17 unused instance binders changed axiom sets in **6 of 7 measured declarations — all
downward**. `VEnv.refQ_not_noApp` went to **no axioms at all**; `oracleExtend_append` lost
`Classical.choice`, which it had been carrying *only* through unused binders. The root cause is
structural and I verified it: `VEnv.Params` itself is `[propext, Quot.sound]`, so **no `[Params]`
binder can ever be axiom-free, however proof-irrelevant it looks.** An unused hypothesis can import
an axiom.

**Correct bar: `after ⊆ before`.** Identical is the expected case for a pure relocation; a *subset*
is a win and must not be reported as a failed check; a *superset* is the only thing that disqualifies
the change. Briefs now say that.

Two related corrections from the same round, both mine:

* **"17 one-line edits, no consumer edits"** — the consumer half was right, the count was not: **35
  lines across 8 files**, of which 18 were cascade, and **two of the files carried none of the
  original 17**. Applying a lemma elaborates the ambient section variable into the call, which is
  what made the binder look used at the caller; trimming the callee propagates *up* the call graph
  across module boundaries to a fixed point. One file went 1 → 9 over two rounds.
* A trim is **not** a repair when the binder was inhabited. `[Params]` has instances, so those 17
  declarations were never vacuous — the trim is a *strengthening*. Saying "fixed" would have implied
  they had been broken.

And two mechanical traps worth keeping: the linter's own suggested clause contains **nested
brackets**, so a `\[[^\]]*\]` scan silently reports a file clean; and `omit … in` must sit **above**
a doc comment, since a doc comment must abut its declaration.

## Seven crashes, all at the same point: write the handoff FIRST (2026-09-03)

Seven streams have died to API errors this session. Every one crashed **while writing its handoff**,
after its Lean work was complete — the last words are consistently "Now the handoff document", "Now
§7, the anti-vacuity apparatus", "Now delete the originals … and add the import".

That is not coincidence. The handoff is the single longest uninterrupted output a stream produces,
so it is the largest target for a mid-generation failure. Seven for seven.

The Lean work has survived every time, because "write incrementally" is in every brief — 588 lines
here, 9.6 KB there, a complete measurement in another. **But the handoff is where the corrections
live.** Six of my own errors this session were caught in a handoff, not in the Lean; losing one
costs the round's most valuable output while leaving the least valuable part intact.

**Rule for briefs, from now on:** write `docs/handoff-<topic>.md` **incrementally from the first
finding onward, not at the end** — a stub with the target and the first measurement, appended to as
you go. Treat it as the primary artefact and the Lean as its evidence, not the reverse. Where a
finding contradicts me, write that sentence down *before* proving the next thing.

When one does crash: the Lean is on disk and verifiable, so commit it with my own summary and say
plainly that the handoff is missing. Do **not** reconstruct the stream's reasoning from its diff and
present it as the stream's report — that would put my inferences in its voice, and this round's whole
lesson is how often my inferences about this tree are wrong.

### The incremental-handoff rule worked on its first outing (2026-09-03, later)

Eighth crash, and the first where the stream's *reasoning* survived. It had written
`docs/handoff-restrictstep.md` as an **append-only status log** — "entry 1 … entry 2 …", each
recorded before the next piece of work — so when the API failed at the transition into authoring,
2.7 KB of conclusions were on disk alongside 8.7 KB of Lean.

What survived was the round's actual finding, and it **corrects a claim the previous round made and
I relayed**: the three nodes form a **closed cycle, not a sandwich**, because the converse direction
is obtained by going *forwards through the restriction* and therefore **without** the lemma this
corner forbids. Under the old habit — handoff written last — that correction would have been lost and
the next round would have inherited my wrong framing.

Two refinements to the rule, from watching it work:

1. **Append-only status log, not a polished document.** "Entry 1: provisional answer before any Lean
   …" is exactly right: it captures the *reasoning* at the moment it is cheapest to record and most
   likely to contradict me. Ask for that shape explicitly.
2. **The pattern was never "crashes at handoff-writing"** — it is *crashes during the longest
   uninterrupted generation*. This one died at the transition into authoring, before writing. So the
   mitigation is not "write the handoff earlier" but **"never let any single generation be the only
   place a finding exists."**

Also recorded from the same file, a diagnostic worth keeping: a spurious `…._f` entry on a
`#print axioms` line signals a **kernel projection failure** — an `Exists`-valued structure field
projected with `.2.2` elaborates but does not kernel-check inside an equation-compiler definition.
The axiom print is what exposed it; the build was green.

## The swap rule applies to any dirty file, not just stream-held ones (2026-09-03)

I wrote swap-and-conditional-restore for the case where a live stream holds a file and I
want to verify HEAD. The case it missed: a file dirty with **no stream running**. That is
how master came to be broken at `RestrictCompanion.lean:506` while every full build I ran
reported green — the repair was sitting uncommitted in my own tree, so I was measuring
HEAD-plus-fix and calling it HEAD.

Widened rule: **a clean `git status` is part of the claim "HEAD builds."** If the tree is
dirty, either commit first or swap the dirty files out and build, and say which of the two
you did. "The build was green" is not evidence about HEAD when the tree is not clean.

Corollary for hypothesis trims. Trimming a hypothesis that proves unnecessary is real
progress and happens often here. The risk moment is not the trim — it is **the commit that
re-points the call sites**. `1beec64` re-pointed 35 sites; 34 were right. A stale call site
is only visible when its module is rebuilt from a clean tree, so after any commit whose
message counts re-pointed sites, build the reverse-dependency closure of the trimmed
declaration from HEAD alone.

## Searching for a premise: shape across layers, not text in a file (2026-09-03)

The ninth stale-absence differed from the previous eight in a way worth keeping. Those had
the false "not supplied" claim and the existing theorem in the same layer, usually the same
file, so grepping the file would have caught them. This one had the prose in `Verify/` and
the theorem in `Theory/` — and the theorem was universally quantified over `env` while the
prose named a specific `env₃`. So a grep for the premise **as rendered in the prose** finds
nothing, and the claim looks verified.

Search for the premise's **conclusion shape across all layers**, never the instantiated form
and never one file. In this instance the shape was `OnCtx ntreeAux.params.reverse` — six hits
across four files, one of which was a hole-free theorem with a real proof term.

## Mandatory before writing "still open": shape.lean, not just exists.lean (2026-09-03)

`exists.lean` answers "does this name exist". It cannot catch the tenth stale-absence,
because the thing I called an open premise was **`VInductDecl'.WF.params` — a field of a
structure already in scope at the claim site**. A structure field's statement is generated,
so it appears nowhere in the source: grep cannot find it, and no one guesses the name.

`scripts/shape.lean` searches the compiled environment for every constant whose *type*
mentions all the given head constants, projections included, and reports **structure fields
first** because a field is not a premise — it is free wherever you hold the structure, so it
retires a hypothesis outright rather than discharging it. On the heads of the premise I got
wrong (`OnCtx`, `VEnv.IsType`) it returns 1196 hits, 14 of them fields, with the one I missed
as the very first line.

    HEADS="OnCtx VEnv.IsType" lake env lean --run scripts/shape.lean

Rules now attached to it:
- Before any brief or ledger row says a premise is open, unproved, or must be carried, run
  this on the premise's **conclusion head constants**. Not its rendered text, not an
  instantiated form: `env₃` and `1` are not searchable, `OnCtx` and `VEnv.IsType` are.
- An unresolvable head is a hard failure, not zero hits. "0 hits" from a typo'd head reads
  exactly like evidence of absence, which is the error the script exists to prevent.
- Its own first version had this bug in miniature: it flagged every theorem in the `VEnv`
  *namespace* as a field of `VEnv`, via `isStructure env n.getPrefix`. An instrument built to
  stop me inventing false statements was inventing them. Real projections come from
  `getProjectionFnInfo?` / `getStructureFields`, and the fix is in the file's comments so the
  next person does not reintroduce it.
- A negative result is still not proof of absence: a premise stated through a *definition*
  that unfolds to your shape mentions none of your heads. The script says so on empty output.


## Every transitive user-count I ever wrote down was wrong (2026-09-03)

Ten figures in this repo describe how many declarations stand on a given hole. Measured
twice independently — a stream in `/tmp`, and me in `scripts/users.lean`, neither knowing
the other was doing it — **not one of the ten is correct**:

| hole | measured | prose claimed |
|---|---|---|
| `forallE_inv_stratified` | ~861–888 (108 modules) | 534, 736, 714, 449, 515, 468 |
| `WF.rigidShapeUniqNS` | ~524–540 (75 modules) | 176, 460 |
| `IsDefEqU.weakN_iff` | ~351–369 (61 modules) | 296, 312 |

Wrong in both directions, and the planning cost was real: the prose made the two injectivity
holes look interchangeable (449 vs 460), when one carries **1.6×** the other's user set and
is not a superset. Anything in this file quoting a user count without a date and a command
should be treated as unverified — including at lines 572 and 822, which are mine.

Use `NAMES="…" lake env lean --run scripts/users.lean`. It reports **direct** (what breaks if
the statement changes) separately from **transitive** (what stands on it). Conflating those
two is how six figures for one hole happened.

### And my first implementation of it was wrong

I got 435/761 where the stream got 540/888. I did not average and did not assume the stream
was wrong: I read my own code and found it. I skipped `isInternal` declarations when
**building** the reverse graph, which severs any chain through a `match_1` or `_proof_` node —
if a theorem reaches the hole only that way, deleting the node deletes the theorem from the
count. ~20% under-count. Traverse internals; filter only when counting.

**The lesson is about method, not about the bug.** Two independent implementations of one
measurement caught what no amount of care on a single implementation would have: my wrong
numbers were self-consistent, plausible, and produced by an instrument I had just written to
be careful. Where a number will drive planning, have it computed twice by different code.
After the fix, module counts agreed *exactly* on all four seeds (75, 108, 61, 40) — that
agreement is what let me attribute the residual 2–4% to a counting convention and a
population that moved between runs, rather than to a second bug.

## Cite names in briefs exactly as exists.lean prints them (2026-09-03)

Three times in one day I cited a declaration bare when it lives in a namespace —
`valAt_of_spineHargsC_of_wf` and `spineHargsC_iff_valStrengthen` (both `VIndRestore`), five
`InjCorner` names (`VEnv`), several `RestoreFaithful` names (`InductiveDeclExamples`,
`NestedWit`). Every time, the stream or I got `NOT FOUND` and had to re-resolve.

That output is exactly what I have told every stream licenses the word "absent". So citing
from memory manufactures the error class the instrument exists to prevent, in the one
document whose job is to prevent it. I have `exists.lean` open while writing the brief.
Fully qualified, copied from its output, every time.

## Relax the git rule: forbid state changes, allow read-only status (2026-09-03)

Two streams today ran a single read-only `git status` and then disclosed it unprompted, having
tripped over "no git commands at all". Both were otherwise scrupulous, neither changed any
state, and both told me in their first sentence.

The rule is mis-drawn. The risk I care about is a stream staging, committing, pushing, stashing,
or checking out — anything that mutates the repo or the index, because I own git and concurrent
writers corrupt each other's work. A stream reading `git status` or `git log` is doing what I
would want it to do: orienting before it writes.

New wording for briefs: **no state-changing git — no add, commit, push, stash, checkout, reset,
or branch. Read-only `git status`, `git log`, `git diff` and `git blame` are fine.** A rule that
well-behaved agents break for harmless reasons trains them to weigh which rules are real, which
is the last thing I want when the frozen-file rule is in the same list.

## A status claim from a handoff is not evidence either (2026-09-03)

Eleven stale-absences were names or structure fields I failed to search for, and I built
`exists.lean` and `shape.lean` for those. The twelfth had a different cause, and so did the
eleventh: I lifted a **status claim** out of a handoff — "untouched", "deferred by three
rounds", "nobody has done X" — and put it in a brief verbatim.

Both times the claim was false, and both times the stream caught it in its pre-flight by
running `shape.lean` before writing. Handoff prose ages exactly as badly as the transitive user
counts did: it was true when written, the tree moved, and nothing in the sentence records when.

**Rule: a status claim taken from a handoff gets `shape.lean` run against it before it enters a
brief, on the same footing as a name.** If I cannot cheaply test it, the brief says "reportedly
untouched as of <handoff>, verify first" rather than asserting it — which is what the good
streams have started doing on their own, and it belongs in the brief instead.

## The census does not distinguish "open" from "known false" (2026-09-03)

I briefed a counterexample hunt against `NormalEq.descend`. One was already in the tree —
`descend_uniq_sortUniq_not_all`, arity 0, cone 6640, hole-free — and had been for a while.

The cause is not carelessness about that file, it is a gap in how I read my own instrument. A
`sorry` whose statement is **known false** sits in `sorry-census-all.lean`'s output looking
exactly like a `sorry` nobody has attacked. Both are "13 holes". They are completely different
work items: one needs a proof, the other needs the statement restated and its consumers
re-based.

Exactly one of the thirteen is currently in the second category. Until the census can say so,
check for a refutation before briefing an attack — `HEADS="<the statement's head constants>"
lake env lean --run scripts/shape.lean` finds one, since a refutation mentions the same heads.

## Require reports to cite names as exists.lean prints them (2026-09-03)

I made this rule for my own briefs after citing three names bare. It belongs on reports too: I
spent four tool calls this round resolving `descend_uniq_sortUniq_not_all`,
`descendBranchProofArg_iff_not_ih` and two others, because the report gave them unqualified and
my guesses at the namespace were wrong. One of them was in no namespace at all, sitting after an
`end VEnv` I had not noticed.

Briefs now ask for it explicitly: **every declaration named in a report must be written as
`scripts/exists.lean` prints it, fully qualified.** The stream has the tool open; I am
reconstructing from memory afterwards.

## The 13 have one dominant root cause (2026-09-03)

`addDecl.WF` is **false today**, refuted hole-free at `stdPrelude`'s first declaration — which is
`Verify/Soundness.lean`'s own literal for `Eq`, so the falsity is on the goal theorem's path. The
mechanism is `VEnvs.WF.no_inductInfo`: no environment holding an `.inductInfo` has a model, so the
moment the checker declares any inductive, the premise is unsatisfiable.

And the flip destroys that refutation: under `AddInduct` acquiring its constructor, `TrEnv'`
admits a map holding an `.inductInfo`, and `TrEnv'.no_inductInfo` — the sole content of the
culprit — becomes false. So `addDecl.WF` must **not** be weakened; it is false only relative to a
placeholder.

Read with the other two findings of the day, the census resolves:

- `AddInduct`'s emptiness is the root cause of `addDecl.WF`'s falsity **and** of the two vacuous
  checker obligations for eta and unit-like defeq.
- One hole is separately **known false** (`NormalEq.descend`).
- One is **inert** — nothing in the tree stands on it (`VIndRecArg.exists_indep`).

I have been quoting "13 holes" as a progress measure all session. It conceals a single dominant
cause, two holes that are not work items of the same kind, and four different remedies.

### New pre-flight question for `Verify/` briefs

Does the route consume `VEnvs.WF.no_inductInfo` or `VEnvs.WF.find?_ne_inductInfo`? If so it is
**temporary** — the flip deletes it. One existing reduction (`addInductiveStepWF_of_run`) is
already in that category, and I have been briefing rounds in that neighbourhood without knowing
to ask.

### Strengthen the handoff rule

The eleventh crash is the only one where no handoff existed, and the only one where I lost the
round's own account of itself — 434 lines of green Lean survived, the report did not. Reconstructing
it took four tool calls. **The handoff's first section must be written before any Lean**, not
merely incrementally: a file that compiles is recoverable, an unwritten report is not.

## A report's claims about other people's files are its weakest part (2026-09-03)

Three times today a stream's own theorems verified perfectly while an *incidental* claim it made
about a file it did not own was wrong:

- a non-vacuity witness described as tainted, measured hole-free;
- a replacement lemma described as hole-free, measured as reaching two holes;
- a lemma reported as non-existent, which exists in a different module.

The cause is structural, not carelessness: the round's verification effort goes to its own
deliverables, and the cross-file remark is a by-product noticed in passing. It is also the part I
am most likely to relay, because it reads like a finding.

**Rule: verify every cross-file claim before recording it, at the same standard as a cone figure.**
Two of the three above I caught; the ledger rows say which, and one of them corrected a row I had
already written from an earlier report.

Corollary about instrument output: I recorded "`shape.lean`: 0 hits, heads resolved" from a report
as a *checked* absence. Re-running it gives 5. The absence conclusion happened to survive — all
five carry the hypothesis, none concludes it — but my evidence for it was fabricated by
transcription. Scan output ages and gets mistyped exactly like prose does.

## Record figures next to their names, so they can be audited (2026-09-03)

Three times today I recorded a cone or arity that was wrong, every time by copying it from an
earlier note of mine rather than re-reading `exists.lean`. My own records had become a source I
trusted above the tool that produced them, and ledger rows get quoted in briefs for weeks.

`scripts/audit-ledger.sh` re-checks every `cone N` / `arity N` in the ledger against the compiled
environment. First run: **77 figures agree, 10 flagged, and all ten flags are pairing artefacts** —
the name nearest the figure belonged to a different declaration. So it found no confirmed recording
error, which is a real if modest result: the figures it *could* pair are sound.

Its honest limit is coverage, not accuracy: it paired 87 of roughly 285 figures. 165 have no
backticked name close enough to attach to, because rows are written as prose with the name several
clauses earlier.

**So the durable fix is a format convention, not the script**: when recording a measurement, put
the fully-qualified name immediately before the figure — `` `Lean4Lean.Foo.bar` (arity 3, cone
1234) `` — rather than naming the declaration at the start of a sentence and the number at the end.
That costs nothing to write and makes every future figure machine-checkable. The script's first
version also over-reported 59 mismatches before I fixed its pairing; an instrument that cries wolf
is the failure I built the arena check to avoid, and I nearly shipped it here.

## Ask for priors in §1 of a pricing brief (2026-09-04)

The round that refuted my confluence-rebuild hypothesis wrote, unprompted, a §1 section headed
"My priors before measuring (record them so bias is visible)" — and then measured the opposite of
what I had suggested.

That is worth requiring. When a brief states a hypothesis of mine, the stream is under pressure to
confirm it, and I cannot tell afterwards whether a confirming answer was measured or inferred from
the brief's framing. A recorded prior makes the difference legible: a round that predicted "one job"
and concluded "two jobs, and here are both directions proved" is credible in a way that a bare
conclusion is not.

**Standing instruction for pricing and hypothesis-testing briefs: ask for the stream's priors in
§1, written before any measurement.** Pair it with the existing rule that §1 is written before any
Lean, and with an explicit statement that a well-argued refutation of my hypothesis is a
first-class outcome I will act on — which in this case it was.

## Write each measurement down as it is made, not at the end of pre-flight (2026-09-04)

Fourteen API crashes this session, and **four of the last five struck at the same moment**: the
transition from measuring to authoring Lean. The last two left nothing but §1 priors — no Lean, and
crucially **no measurements**, because §2 was still empty. The stream had done the pre-flight work
and was holding it in context.

The existing rule ("write §1 before any Lean, then keep the handoff incremental") is not enough,
because streams read it as *§1 first, then measure, then write §2*. The measurements are the
expensive part — dozens of tool calls — and they are exactly what evaporates.

**Sharpened rule for briefs: append each pre-flight measurement to the handoff as you make it.**
One line per `exists.lean` / `shape.lean` / `users.lean` result, before the next call. A crash then
costs the authoring, not the measuring.

Second adaptation: **scope rounds smaller while the crash rate is this high.** A round that only
classifies and reports survives a crash with most of its value; a round that classifies *and*
assembles *and* witnesses loses everything if it dies at the assembly step. Split those.

## My numbers are reliable; my attributions are not (2026-09-04)

A round scored eight predictions a crashed predecessor had written before looking at the code. The
two I most wanted scored both came back FALSE, in opposite directions:

- "at least one figure in the brief is wrong" (70%) — **false**. All four figures I supplied were
  exact.
- "the brief's ownership attribution is correct" (60%) — **false**. Wrong in kind for all four
  attributions, and wrong in fact for one.

In the round's words: *this brief's numbers have been reliable; its attributions have not.* That
separates two things I had been treating as one kind of claim, and it is a sharper self-assessment
than I could have produced unaided.

The worst case: I told two separate briefs that `Faithful` is `RestoreFaithful.lean`'s job. That
file concludes it **zero** times — the general producer is `Built.toFaithful`. And none of the four
obligations I attributed to particular files is even a *field* of the relation I said they belonged
to. The round names the harm precisely: a round hunting them among that relation's fields would
have found nothing and concluded the fields were missing — my brief could have manufactured a false
absence, which is the very defect this project's ledger exists to track.

**Rule: a measured figure may go in a brief with its provenance. Ownership, "whose job is this",
and "where does this live" go in as *reportedly, verify first* — never as fact.** I have `shape.lean`
and `users.lean` for exactly these questions and I have been answering them from memory.

## None of my instruments answers "which direction is this pair already connected?" (2026-09-04)

A round scored its own seven priors and then named the thing none of them had asked:

> all seven priors asked *whether the lemma is true*. Not one asked **which way the tree already
> runs the implication** — and that was the only thing that mattered.

I had briefed a field as "waiting on one strengthening of X". The tree already proves X **from**
that field, by name. The field is upstream, and the round produced a machine-checked refutation of
my characterisation — not merely a report that it was hard.

This is a gap in my toolkit, not just an error. `exists.lean` answers *does it exist*, `shape.lean`
answers *what concludes this shape*, `users.lean` answers *what depends on it*. **None answers *in
which direction is this pair already connected*.** Two of my brief errors this session are direction
errors — this one, and pricing the wrong clause because I inverted a report's conclusion — and no
instrument I have would have caught either.

Cheap partial check until something better exists: for a claimed dependency A-needs-B, run
`users.lean` on **both** and see which appears in the other's cone. If B's cone contains A, the
brief has it backwards.

## After a crash, check for a broken file inside a build glob — first (2026-09-04)

The sixteenth crash left a 296-line file with 8 errors at `Lean4Lean/Theory/Typing/PatSig.lean`.
`lakefile.toml` globs `Lean4Lean.Theory.*` and `Lean4Lean.Verify.*`, so that file was breaking the
build for **three concurrently running streams** until I moved it to `docs/`.

A crashed round's partial Lean is not inert. It is a build break for everyone else, and the streams
that hit it would have reported a red tree and possibly gone looking for the cause in their own work.

**Standing check: the first thing to do after a crash notification is look for a partial file inside
a glob, and move it out of the source tree before reading anything else.** Preserve it — the work is
usually worth keeping — but put it somewhere that is not compiled.

## Closure computed from the wrong seed: twice now (2026-09-04)

The `PatSig` round caught its own classifier bug before recording a number: seeding a statement
closure from a declaration's *type* leaves a `def`'s **body** unexpanded, so six core relations were
mis-reported as judgment-free, because their types are only `List VExpr → VExpr → VExpr → Prop`. It
re-seeded and discarded the first-run figures.

That is the same mistake as my own `users.lean` bug — a reverse-dependency graph built without
internal declarations, undercounting by ~20%. Both times: a closure seeded wrongly, producing a
plausible, self-consistent, wrong answer that nothing in the output flagged.

When a round reports a closure or census figure, ask what it seeded from. Types, values, and
constructors give three different answers, and only one of them is the one wanted.

## I put four files in the wrong layer (2026-09-04)

Exactly four files under `Lean4Lean/Theory/` import `Lean4Lean.Verify.*`, inverting the refinement
chain (`Verify/` → `Theory/` → `Theory/SetModel/` → Foundation). All four were created **this
session, by rounds I commissioned**: `EtaGuardLand.lean`, `StructEtaPrice.lean`,
`CommutationLemmas.lean`, `NoConfRepair.lean`.

No cycle exists today and the tree is green, so this is fragility rather than breakage — but a future
`Verify/` file importing any of the four would cycle, and one of them is imported by
`Theory/SetModel/RecTypePeel.lean`, the deepest layer.

**The cheapest correct fix is not to move the four files**, which would push the inversion down into
`SetModel/`. It is to move the one declaration `SetModel/` actually needs
(`SetModel.eq_singleton_of_recProp`) down out of `StructEtaPrice.lean`, cutting the single edge that
reaches the deepest layer. Blast radius: `StructEtaPrice` has 4 importers, `EtaGuardLand` 2,
`NoConfRepair` 1, `CommutationLemmas` 0.

**The briefing lesson**: I choose the file path in every brief, and I chose `Theory/Typing/...` for
work whose dependencies were in `Verify/` — four times, without once asking what the file would need
to import. A brief that names a path should name it *after* checking which layer the content belongs
to. The stream that flagged this did the right thing: it noted the pre-existing edge, added no new
direction, and asked for a human glance rather than importing through silently.

## Work async: spawn the follow-up as soon as a round is verified (2026-09-04, user instruction)

**Standing rule, from the user.** When a subagent reports, do not wait for the next prompt before
starting the next round. The sequence is:

1. Verify the round's load-bearing claims myself (`exists.lean` with both cleanliness lines,
   `shape.lean`/`users.lean` where the claim is about absence or scale).
2. Commit — the Lean, the handoff, the ledger rows, and any correction the round forced.
3. **Immediately spawn the follow-up in the same turn**, using what the round just established.

Verification stays first. The rule removes the idle gap between a report and the next brief, not the
check — a round that spawns work on an unverified claim propagates it, and this session has fifteen
brief errors of mine to show what that costs.

Two practical consequences:

- **The follow-up brief should carry the round's own corrections**, not my prior framing. Most rounds
  here correct something in their brief; the next brief is where that correction has to land, or the
  same error goes out again. That has happened: I relayed "the only thing left" from a round's file
  and the next round measured it as three of nine hypotheses.
- **Keep a slot free when a stream owns a file another will need.** Async means overlapping rounds,
  and this session has already had one crashed round's partial file break three concurrent builds,
  and two rounds absorb a red tree caused by a third. Grant paths so that follow-ups do not collide,
  and tell each stream that a red build in a file it does not own is someone else's work in flight.

## A decision request must be a small self-contained PR (2026-09-04, user instruction)

**Standing rule, from the user.** When I need a decision, the vehicle is a **small, self-contained
pull request** against `origin` (`vasnesterov/lean4lean`) — not a prose document, not a paragraph in
a status report, and never a large diff.

What that means concretely:

- **Small.** The diff is the change being decided and nothing else. The first PR I opened this
  session was ~55k lines and the user rejected it outright, asking for "only your suggestion that
  needs my decision". That is the standard.
- **Self-contained.** Everything needed to decide is in the PR: the change, what it buys, what it
  costs, the options, my recommendation, and any measurement that bears on it. The reviewer should
  not have to go find a doc.
- **Honest about what is unmeasured.** If a number that matters is not yet in hand, the PR says so
  and says why, rather than implying the decision is fully informed.
- **Never against upstream.** `origin` only. `digama0/lean4lean` is fetch-only, per CLAUDE.md.

The corollary for prose: a `docs/decision-*.md` file is working material for *me* — the costing, the
rejected options, the measurements. It is not how the question gets asked. Ask it in a PR, and let the
document be what the PR links to.

## Never post a PR comment by hand (2026-09-04)

`scripts/monitor-pr-comments.sh` suppresses comments containing `<!-- l4l-orchestrator -->` so my
own posts do not wake me as though they were the user's. I have now forgotten that marker **twice** —
three comments early on, fixed retroactively, and again on PR #46, which echoed straight back through
the monitor within minutes.

Twice is not a lapse, it is a missing tool. **Use `scripts/pr-comment.sh <pr> <<'BODY' … BODY`.** It
reads the body from stdin, appends the marker if absent, posts to `vasnesterov/lean4lean` only, and
then selftests by asking the monitor's own filter how many unmarked comments remain.

The general shape, and it is the session's most repeated lesson: when I catch myself relying on
remembering something, the fix is a script, not resolve. That is how `exists.lean`, `shape.lean`,
`users.lean`, `arena-needed.sh`, `layer-check.py`, the ledger audit, and the `WATCH` list all came to
exist — each after an error that discipline alone had failed to prevent.

## "It exists" is not "I can cite it" (2026-09-04)

Every instrument I built imports the whole default-target population into one environment. So they all
answer *does this exist* — and none answered *is it available where I need it*.

Three case arms of the nested flip need content that exists, is proved, is hole-free and clean on every
watched statement, and **cannot be cited at the site that needs it**: `Theory/Typing/EnvLemmas.lean`
cannot see `Theory/Inductive/NestedOrdered.lean`, and two siblings likewise. I verified all three.
**Four consecutive documents in this repo listed those as available**, because every tool said they
existed and existence was the wrong question.

`scripts/can-cite.py <consumer-module> <decl>...` closes it: defining module, whether the consumer's
closure contains it, and the module the consumer would have to gain. A NO is an import-order fact, not
a missing proof — ask whether the statement elaborates at the consumer's position with only upstream
data, because then it is a proof move or a migration, which is far cheaper than it looks.

**Run it before pricing any "the content already exists" claim**, mine included. That claim has now
been wrong in this specific way at least four times.

## Under async, my "concurrent streams" lists are stale before they are read (2026-09-04)

A round reported that more streams were live than its brief named, and that `git log` advanced three
commits while it worked. That is not an error in the round — it is a direct consequence of the async
rule: I spawn a follow-up the moment a round is verified, so any enumeration of concurrent work I write
into a brief is stale within minutes.

**Fix: briefs state what the stream OWNS, and tell it to discover the rest itself** with read-only
`git status` / `git log` — permitted since the git rule was narrowed to state-changing commands. Keep
the standing instruction that a red build in a file it does not own is someone else's work in flight:
re-poll and say so. That instruction has now worked three times, including on a file created *during*
the round that observed it.

Ownership grants stay exact and exclusive; only the courtesy list of neighbours becomes advisory.

## Two brief defects of mine, both found by rounds (2026-09-04)

**1. The round-close clause is mis-scoped.** Every brief ends "zero in-repo section-variable warnings".
A round owning one new file cannot deliver that: there are 66 such warnings across 24 files it does not
own. It reported the failure rather than claiming success, which is right, but the clause should never
have asked. **Fix: "zero warnings from the files you own", with the global count reported separately as
drift.** Note also that I have been conflating two warning classes under one name — `linter.unusedSectionVars`
genuinely is at 0 in-repo; the 66 are the "variable is not explicitly referenced" class.

**2. I am not tracking orphans.** Three consecutive model-side rounds built modules that nothing imports:
`InterpMkPi.lean` and `TeleWFBridge.lean` had **no consumer at all** until the third round imported them,
and that round is itself one of **52 orphans**. Not wasted work — a general witness will sit downstream of
exactly those — but I commissioned three rounds without once asking what would consume them.

**Add to the brief template: state up front which existing module will consume this, and if none will yet,
say so.** `scripts/can-cite.py` answers it in one call, and the round that volunteered this did exactly
that before starting rather than after.

## 42 of 53 orphan modules are mine, from this session (2026-09-04)

Measured: 484 modules, 53 that nothing imports, **42 created this session** by rounds I commissioned.

The split matters. Refutations, pricings and scopings are *records* — they exist to be read, and
orphanhood is correct for them. But general producers and lemmas built to be used are a different case:
`TrTypeProducer`, `SurfaceMap`, `CtorPointwise`, `CtorsLenGeneral`, `TrExprSGeneral`, `SEReduce`,
`CommutationLemmas`, `OracleObligations` are all deliverables with no consumer. That *is* the remaining
wiring work, so the story is coherent — but I ran twenty-odd rounds without measuring it once.

**Make it a standing metric, not a note.** A producer round whose output nothing can consume is either
premature or mis-placed, and both are detectable before commissioning: `can-cite.py` answers "who could
consume this" in one call, and the orphan set is a five-line walk of the import graph. Two rounds
reported their own orphanhood to me before I thought to check.

The pattern this fits, and it has held all session: **the thing worth measuring is usually the thing I
have been asserting in prose.**

## While streams are live, new rounds are additive-only (2026-09-04, mine)

I had a good, cheap, measurable task ready: kill the `Theory/ → Verify/` layer inversion in
`Theory/Typing/CommutationLemmas.lean` by moving `VInductDecl'.projAllG`, `.etaExpansionG` and
`VEnv.StructEtaG` -- all three pure `VExpr`/`VInductDecl'`/`IsDefEq` content -- out of
`Verify/TypeChecker/EtaStructG.lean` and down into `Theory/Inductive/`.  Measured: there are
**exactly 4** such inversions in `Theory/` (`CommutationLemmas` -> `EtaStructG`, `EtaGuardLand` ->
`NoConfGuard`, `NoConfRepair` -> `ProjSpineInv`, `StructEtaPrice` -> `EtaUnitRefute`), and this move
takes it to 3.

I did not spawn it, and the reason generalises.  `EtaStructG.lean` is inside the live eta stream's
compile cone.  The move changes no name and no statement, so the tree is green *before* and *after*
-- but **during** the round the shared module is transiently broken, and a live stream then sees
errors in files it does not own.  That is not a merge conflict, which git would show me; it is a
stream misdiagnosing someone else's breakage as its own and spending a round on it.  I have already
paid for this once with the swap-and-restore procedure (see the 2026-09-03 entry: my file swaps were
invisible to the stream and looked exactly like corruption).

So the rule, while any stream is live:

- A new round may **create** files freely.
- A new round may **edit** only files no live stream compiles -- which in practice means only its own
  new files, because the shared `Theory/` and `Verify/` spines are in everybody's cone.
- Work that requires editing a shared module is **queued for me**, to apply between rounds, and the
  queue entry names the files and the exact edit.

This is not a reason to defer the *content*.  The additive version of a shared-file task is usually
real work, not a plan: instead of deleting the old declaration, **prove the replacement dominates it
in your own file**.  Then the deletion is a text edit I do later, and the round's deliverable is a
theorem rather than a recommendation.  Both rounds I opened this turn are shaped that way, and it is
how the `NormalEq.descend` round is scoped: not "restate it" (already done in `KDescend.lean`) but
"prove the restatement suffices at every real consumer, with `descend` measured absent from the cone".

**Queued for me, in order:** (1) move `projAllG`/`etaExpansionG`/`StructEtaG` down, re-point
`CommutationLemmas`, inversions 4 -> 3; (2) delete `NormalEq.descend`'s three refuted branches from
`ChurchRosser.lean` if the `DescendSurplus` round shows they are surplus.

## A grep for a module name is not a grep for an import (2026-09-04, mine)

`grep -rln "Verify.TypeChecker.EtaStructG"` returned **12** files and I was one keystroke from
briefing "four `Theory/` files import it".  `grep -rn "^import Lean4Lean.Verify.TypeChecker.EtaStructG"`
returns **5**, of which exactly **one** is under `Theory/`.  The other seven mentions are docstrings
and one commented-out import inside `Experimental/ConeJoin.lean`.

This repo's files carry long prose docstrings that name other modules constantly -- that is a feature,
it is where the measurements live -- and it makes bare `grep` for a module or declaration name a
*mention* count, never a *use* count.  The tell was arithmetic: the list contained
`Theory/Inductive/StructureEta.lean`, which **defines** `projAll`/`etaExpansion` that `EtaStructG`
consumes, so an import in that direction would be a cycle.  An impossible edge in the answer means
the question was wrong.

Anchor the pattern to what you actually mean: `^import ` for imports, and `lean_references` at the
declaration site (not `grep`) for call sites.  I put the same warning in the `DescendSurplus` brief,
because `NormalEq.descend` is mentioned in a dozen docstrings and called in very few places.

Eleventh entry in my attribution-error column; the cone-figure column is still clean.

## Queued shared-module edits (2026-09-04, mine)

Under the additive-only rule above, rounds hand me edits instead of applying them.  The queue, to be
applied between rounds, newest last:

1. Move `VInductDecl'.projAllG`, `.etaExpansionG` and `VEnv.StructEtaG` out of
   `Verify/TypeChecker/EtaStructG.lean` into `Theory/Inductive/`, re-point
   `Theory/Typing/CommutationLemmas.lean`; layer inversions **4 -> 3**.
2. Delete `NormalEq.descend`'s three refuted branches from `ChurchRosser.lean` -- **only if** the
   `DescendSurplus` round shows `descendV` dominates at every real consumer with `descend` measured
   absent from the cone.
3. `ConfluenceRebuildPrice.lean:433-435`: flip `ParRedSE.structEta`'s two arguments so the rule
   contracts.  `EtaOrient.lean` §3/§7 are that file's eight downstream proofs already ported with
   **unchanged proof text**, so the flip is verified before it is made.  Consequence, which is the
   real cost: `CRSEScope.lean` §2 and §4 are statements about the expansion and need restating (§1
   and §3 survive).  **This is my call, not the user's** -- CLAUDE.md puts `Theory/` proof machinery
   in my hands -- and I am taking it, because the benefit is that `parRedSES_rigid`'s hypothesis goes
   from false to unconditionally true, while the cost lands on `NormalEq.descend`, which is already
   refuted in both orientations.  Whoever applies it restates `CRSEScope` §2/§4 in the same round.

### Correction, same turn: 4 is the direct-edge count, not the inversion count (2026-09-04, mine)

I wrote "there are **exactly 4** such inversions in `Theory/`" above.  That is the count of Theory
modules with a *direct* `import Lean4Lean.Verify.*` line.  The number that decides anything is the
**transitive** one, and it is **10** (of 279; 269 are clean).  I found this the way I should have
looked in the first place: `scripts/can-cite.py` answered **YES** for `Lean4Lean.VEnv.patWF_of_wf`
(defined in `Verify/Typing/ConstSpineWF.lean`) from `Theory/Typing/EtaOrient.lean`, which has no
direct `Verify` import at all.  Citability follows the closure, not the edge.

`scripts/layer-check.py` now reports both.  The 10 are one connected cluster, all in `Theory/Typing/`,
and every one of them enters `Verify/` through the same four direct edges:

    CommutationLemmas -> EtaStructG        (30 Verify modules)
    EtaGuardLand      -> NoConfGuard       (46)
    NoConfRepair      -> ProjSpineInv      (45)
    StructEtaPrice    -> EtaUnitRefute     (45)
    then CRSEScope, ConfluenceRebuildPrice, ConstAppInvSIProof, EtaOrient, SEReduce,
    SEReerectionScope inherit it

So the queued migration is worth more than "4 -> 3": cutting the four direct edges cleans **ten**
modules -- the entire eta/confluence cluster -- and that cluster is exactly where the eta front works.
Note also that `Verify/Axioms.lean`, a **frozen** file, sits in those closures.  Read-only, so no rule
is broken, but a `Theory/` module transitively depending on the frozen axiom list is worth knowing.

## "No instance exists" needs the citability check too (2026-09-04)

The eta round reported: "no `Params` instance over an environment with a structure exists", because
`Params.extra_pat` forces `Pat`-registration, that is `PatWF`'s ι case, and that needs the
`IsDefEqU.forallE_inv` hole.  The mechanism is right and the conclusion is **too strong**.
`Lean4Lean.VEnv.patWF_of_wf` (`Verify/Typing/ConstSpineWF.lean:57`) proves `env.PatWF U` from
`env.WF` alone at an **arbitrary** environment -- and `can-cite.py` says the eta round's own file
could have cited it.

What it does is take Π-injectivity from the census hole rather than carry it (`piInv_axiom henv`),
which is presumably what the round was reacting to.  But "tainted by an existing hole" and "does not
exist" are different verdicts, and only the first is true.  Corrected picture: a `Params` instance at
a structure environment needs (a) `VEnv.WF` of that environment and (b) acceptance of the `piInv`
census hole -- and **(a) is the interesting half**, because for a concrete two-type block it may be
provable outright, or it may be the `AddInduct` flip that the B6 stream is on.  That is what I spawned
next, and it is a better target than the one the round proposed.

Standing addition to the "still open" checklist: before writing "no instance/witness exists", run
`exists.lean`, `shape.lean`, **and** `can-cite.py`.  The third is new to this list because this is the
second time in two days that a thing existed, was citable, and was reported absent.
