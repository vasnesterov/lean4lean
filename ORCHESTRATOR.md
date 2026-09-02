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
`git stash push -u && lake build; git stash pop` — that is how the second breakage was diagnosed,
and it takes one command.

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
