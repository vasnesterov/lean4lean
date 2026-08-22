# lean4lean

Goal: a fully verified Lean 4 kernel — complete the implementation, specification, and proofs in this repo. Use the `lean-lsp` MCP server for all Lean interaction.

## Stop condition

1. The Kernel Arena suite passes: `uv run lka.py run --checker lean4lean-local` in `~/lean-kernel-arena`, every non-`either` test correct.
2. `Lean4Lean.kernel_sound` (`Lean4Lean/Verify/Soundness.lean`) is proven: guard 2 of `Lean4Lean/Verify/Guard.lean` prints "proof COMPLETE".

Both must hold on the same commit.

## Rules

- `Verify/Soundness.lean`, `Verify/Axioms.lean`, and `Verify/Guard.lean` are frozen; changing them requires human sign-off.
- Guard.lean's three build-time checks must always pass: no axioms beyond its whitelist, no `partial`/`@[extern]`/`@[implemented_by]` reachable from `Lean4Lean.addDecl` beyond its allowlist (shrinking the allowlist is progress).
- Foundation is pinned to a commit in `lakefile.toml`. No `lake update`, no pin changes, no pushes to the fork without human sign-off.
- Everything else — `Lean4Lean/Theory`, the abstract spec, `addDecl.WF` — is proof machinery you can freely design.

Soft guideline: keep the implementation close to the official C++ kernel; divergences go in `divergences.md`, C++ kernel bugs found in `bugs-found.md`.

## References

- `~/lean-type-theory` — Carneiro, *The Type Theory of Lean*: `typesys.tex` (spec blueprint, incl. inductives), `soundness.tex` (ZFC + n-inaccessibles model), `unique.tex`, `axioms.tex`.
- `~/lean4/src/kernel` — the official C++ kernel (current master), the implementation this checker mirrors.
- `~/lean-kernel-arena` — kernel test suite (goal 1).
- `~/Foundation` — checkout of the Foundation dependency (fork `vasnesterov/Foundation`, branch `lean4lean-dev`).
