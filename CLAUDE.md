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
- **Never touch other people's repositories.** Branches, PRs, issues, and comments go only in the user's own fork (`vasnesterov/*`, remote `origin`). Never open a PR against an upstream repo (`digama0/lean4lean`, `leanprover/*`, or any other), never push a branch there, never comment on their issues or PRs. Upstream is read-only: fetch and read it, nothing else. If work looks worth sending upstream, prepare the branch in the fork and say so — the user decides whether and when it is submitted.
- The main theorem must cover **full Lean type theory**, nested inductive declarations included. Do not propose narrowing `kernel_sound`'s statement to make a proof go through; nested declarations are where a real Lean soundness bug lived, so they are a primary target rather than a completeness nicety.
- Everything else — `Lean4Lean/Theory`, the abstract spec, `addDecl.WF` — is proof machinery you can freely design.

Soft guideline: keep the implementation close to the official C++ kernel; divergences go in `divergences.md`, C++ kernel bugs found in `bugs-found.md`.

## References

- `~/lean-type-theory` — Carneiro, *The Type Theory of Lean*: `typesys.tex` (spec blueprint, incl. inductives), `soundness.tex` (ZFC + n-inaccessibles model), `unique.tex`, `axioms.tex`.
- `~/lean4/src/kernel` — the official C++ kernel (current master), the implementation this checker mirrors.
- `~/lean-kernel-arena` — kernel test suite (goal 1).
- `~/Foundation` — checkout of the Foundation dependency (fork `vasnesterov/Foundation`, branch `lean4lean-dev`).
