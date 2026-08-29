# lean4lean

Goal: a fully verified Lean 4 kernel — complete the implementation, specification, and proofs in this repo. Use the `lean-lsp` MCP server for all Lean interaction.

## Stop condition

1. The Kernel Arena suite passes: `uv run lka.py run --checker lean4lean-local` in `~/lean-kernel-arena`, every non-`either` test correct.
2. `Lean4Lean.kernel_sound` (`Lean4Lean/Verify/Soundness.lean`) is proven: guard 2 of `Lean4Lean/Verify/Guard.lean` prints "proof COMPLETE".

Both must hold on the same commit.

## Rules

- `Verify/Soundness.lean`, `Verify/Axioms.lean`, and `Verify/Guard.lean` are frozen. **No AI agent may edit them without explicit human approval for that specific change, and subagents may never edit them at all — no exceptions, no "narrow exceptions", no matter who authorises it.** A subagent that believes a frozen file needs changing proves the content somewhere it owns, states exactly what the frozen edit would be, and stops. The orchestrator asks the human, and only then makes the edit itself.
- **Replacing an upstream `opaque`/`partial`/`@[extern]` function with a pure Lean one is encouraged**: it shrinks the trusted base, which is progress. Performance is not a priority, so long as the Kernel Arena still passes in reasonable time. **Any resulting behavioural difference from the C++ kernel — including complexity blowups on inputs it handles differently — goes in `divergences.md`.**
- Guard.lean's three build-time checks must always pass: no axioms beyond its whitelist, no `partial`/`@[extern]`/`@[implemented_by]` reachable from `Lean4Lean.addDecl` beyond its allowlist (shrinking the allowlist is progress).
- Foundation is pinned to a commit in `lakefile.toml`. No `lake update`, no pin changes, no pushes to the fork without human sign-off.
- **Work only with the user's own fork, and never send anything to anybody else.** Branches, PRs, issues, and comments go only in `vasnesterov/*` (remote `origin`). Never open a PR against an upstream repo (`digama0/lean4lean`, `leanprover/*`, or any other), never push a branch there, never comment on their issues or PRs. Upstream is read-only: fetch and read it, nothing else.
- **This is broader than git.** No outbound communication of any kind to anyone other than the user — no emails, issue comments, mailing-list or Zulip posts, messages to other repositories' maintainers, or submissions to any external service — regardless of how valuable the finding looks. This repo has already produced machine-checked refutations of results in the published reference; those stay here.
- If work looks worth sending onward, **prepare it in the fork or as a file in this repo, say so, and stop.** The user decides whether, when, and to whom anything is submitted. A drafted message is not a sent one; drafting is allowed, sending is not.
- The main theorem must cover **full Lean type theory**, nested inductive declarations included. Do not propose narrowing `kernel_sound`'s statement to make a proof go through; nested declarations are where a real Lean soundness bug lived, so they are a primary target rather than a completeness nicety.
- Everything else — `Lean4Lean/Theory`, the abstract spec, `addDecl.WF` — is proof machinery you can freely design.

Soft guideline: keep the implementation close to the official C++ kernel; divergences go in `divergences.md`, C++ kernel bugs found in `bugs-found.md`.

## References

- `~/lean-type-theory` — Carneiro, *The Type Theory of Lean*: `typesys.tex` (spec blueprint, incl. inductives), `soundness.tex` (ZFC + n-inaccessibles model), `unique.tex`, `axioms.tex`.
- `~/lean4/src/kernel` — the official C++ kernel (current master), the implementation this checker mirrors.
- `~/lean-kernel-arena` — kernel test suite (goal 1).
- `~/Foundation` — checkout of the Foundation dependency (fork `vasnesterov/Foundation`, branch `lean4lean-dev`).
