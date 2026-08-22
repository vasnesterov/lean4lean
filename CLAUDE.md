# lean4lean

Goal: a fully verified Lean 4 kernel — complete the implementation, specification, and proofs in this repo. Use the `lean-lsp` MCP server for all Lean interaction.

## Stop condition

1. The Kernel Arena suite passes: `uv run lka.py run --checker lean4lean-local` in `~/lean-kernel-arena`, every non-`either` test correct.
2. `Lean4Lean.leanTT_equiconsistent_zfc_omega_inaccessibles` (`Lean4Lean/Theory/Equiconsistency.lean`) is proven — no `sorry` in its cone, axioms at most `propext`/`Classical.choice`/`Quot.sound` plus `Lean4Lean/Verify/Axioms.lean` — with its statement unchanged. Filling the statement's `sorry`-backed definitions (`VInductDecl.WF`, `VEnv.addInduct`, `AddInduct`, `TrProj`) is required, but needs human review; any other statement-layer change is forbidden.

## References

- `~/lean-type-theory` — Carneiro, *The Type Theory of Lean*: `typesys.tex` (spec blueprint, incl. inductives), `soundness.tex` (ZFC + n-inaccessibles model), `unique.tex`, `axioms.tex`.
- `~/lean-kernel-arena` — kernel test suite (goal 1).
- `~/Foundation` — checkout of the Foundation dependency (fork `vasnesterov/Foundation`, branch `lean4lean-dev`).
