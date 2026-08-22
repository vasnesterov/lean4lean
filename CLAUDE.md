# lean4lean — project goal and rules for AI agents

## Minimal goal (stop condition)

The project is finished when BOTH hold:

1. **The Kernel Arena test suite passes** (`~/lean-kernel-arena`, checker
   `lean4lean-local`): every non-`either` test correct. Run with
   `uv run lka.py run --checker lean4lean-local` from the arena directory.
2. **The main theorem is proven, with its statement unchanged**:
   `Lean4Lean.leanTT_equiconsistent_zfc_omega_inaccessibles` in
   `Lean4Lean/Theory/Equiconsistency.lean`:

   ```
   Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 ↔ leanTTConsistent
   ```

   "Proven" means: no `sorry` anywhere in its proof's dependency cone, and
   `#print axioms` reports at most `propext`, `Classical.choice`, `Quot.sound`
   plus the declared upstream-opaque axioms of `Lean4Lean/Verify/Axioms.lean`.
   "Statement unchanged" covers the whole statement layer: the theorem's type
   and every definition it transitively depends on — including
   `Lean4Lean/Theory/Consistency.lean` (`leanTTConsistent`, `leanPrelude`,
   `falseProp`, `VEnv.LeanWF`) and Foundation's
   `FirstOrder/SetTheory/InaccessibleCardinal.lean` (`𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`,
   `IsInaccessible.dfn`, `Axiom.atLeastInaccessibles`).

   Exception: the statement currently depends on two `sorry`-backed
   definitions that MUST be filled in (this is completing the statement, not
   changing it): `VInductDecl.WF` and `VEnv.addInduct`
   (`Lean4Lean/Theory/Inductive.lean`), plus the related empty `AddInduct`
   relation and `TrProj` on the Verify side. Filling these requires human
   review before proofs may rely on them.

## Anti-cheating rules (hard constraints for every agent)

- Never weaken, vacuize, or otherwise alter statement-layer definitions to
  make proofs easier. Any statement-layer edit requires explicit human sign-off.
- Never add `axiom`s, `native_decide`, or new `@[implemented_by]`/`unsafe`
  escape hatches. `sorry` is allowed only as an explicit open-goal marker in
  proof layers, never inside definitions.
- Audit after substantive changes: walk the statement's dependency cone
  (types + definition values + inductive constructor types) and verify no
  `sorryAx` and no non-whitelisted axioms enter the cone of the *statement*.
- Do not change `lean-toolchain`, and do not repin dependencies, without
  human sign-off.
- Interact only with the user's forks (`vasnesterov/lean4lean`,
  `vasnesterov/Foundation` branch `lean4lean-dev`); never push elsewhere.

## How to interact with Lean

**Use the `lean-lsp` MCP server (lean-lsp-mcp) for all Lean interaction**:
`lean_diagnostic_messages` for errors, `lean_goal` for proof states,
`lean_hover_info`/`lean_local_search` before guessing lemma names,
`lean_multi_attempt` to try tactics, `lean_run_code` for scratch checks and
audits, `lean_build` to rebuild + restart the LSP after new imports.
Prefer these over raw `lake build` iterations; fall back to `lake` in Bash
only for whole-project builds or work in other checkouts (e.g. Foundation).

`lake`/`lean` come from elan (`export PATH="$HOME/.elan/bin:$PATH"`).

## Layout facts agents need

- `Lean4Lean/` (not `Theory`/`Verify` subtrees): the executable checker.
  `Lean4Lean/Theory/`: the abstract type theory ("Lean TT").
  `Lean4Lean/Verify/`: proof that the checker implements the theory; its
  top theorem is `addDecl.WF` (`Lean4Lean/Verify/Environment.lean`).
- The Foundation dependency (first-order logic, ZFC) is the user's fork,
  branch `lean4lean-dev`, wired in `lakefile.toml`. Its module
  `Foundation/Vorspiel/Arithmetic.lean` is still broken on this toolchain
  (out of our import closure; fix welcome but low priority).
- Proof-layer `sorry`s to discharge live in `Lean4Lean/Verify/**` (run
  `grep -rn "sorry" Lean4Lean --include="*.lean" | grep -v Experimental`),
  in `Lean4Lean/Theory/Typing/Injectivity.lean`, and ultimately the two
  model constructions behind the main theorem.
- `Lean4Lean/Experimental/` is scratch space; it is not part of the goal.
