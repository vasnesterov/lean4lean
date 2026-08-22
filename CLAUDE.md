# lean4lean

Goal: a fully verified Lean 4 kernel — complete the implementation, specification, and proofs in this repo. Use the `lean-lsp` MCP server for all Lean interaction.

## Stop condition

1. The Kernel Arena suite passes: `uv run lka.py run --checker lean4lean-local` in `~/lean-kernel-arena`, every non-`either` test correct.
2. **Soundness of the Lean kernel**: `Lean4Lean.kernel_sound` (`Lean4Lean/Verify/Soundness.lean`) is proven — if the executable checker accepts the standard prelude plus axiom-free declarations and certifies a safe proof of `∀ p : Prop, p`, then ZFC + {≥ n inaccessibles | n ∈ ω} is inconsistent. No `sorry` in its proof cone; axioms at most `propext`/`Classical.choice`/`Quot.sound` plus the 32 axioms `Lean4Lean/Verify/Axioms.lean` declares as of commit `20e2d14` — that file is frozen: adding or changing an axiom anywhere requires human sign-off. Its statement (everything `Soundness.lean` defines, and the Foundation side it imports) must remain unchanged; the file's build-time adequacy `#eval` checks must keep passing. Everything else — `Lean4Lean/Theory`, the abstract spec, `addDecl.WF` — is proof machinery the swarm may freely design.

Soft guideline (not a hard rule): keep the implementation close to the official C++ kernel (`~/lean4/src/kernel`, pinned at the toolchain version) — divergences belong in `divergences.md`, and faithful mirroring is how this project finds bugs in the C++ kernel (see `bugs-found.md`).

## References

- `~/lean-type-theory` — Carneiro, *The Type Theory of Lean*: `typesys.tex` (spec blueprint, incl. inductives), `soundness.tex` (ZFC + n-inaccessibles model), `unique.tex`, `axioms.tex`.
- `~/lean4/src/kernel` — the official C++ kernel (current master), the implementation this checker mirrors.
- `~/lean-kernel-arena` — kernel test suite (goal 1).
- `~/Foundation` — checkout of the Foundation dependency (fork `vasnesterov/Foundation`, branch `lean4lean-dev`).
