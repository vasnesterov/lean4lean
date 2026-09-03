# Handoff: constructing `AddInduct`'s constructor at a parameterised nested block

**Owner file:** `Lean4Lean/Verify/Inductive/FlipConstruct.lean` (new, mine).
**Written incrementally, starting 2026-09-03 16:00 UTC.**  Nothing below is read off a
docstring unless it says so; measurements carry the instrument that produced them.

This file is written as the work proceeds, on purpose: eight predecessor streams died while
writing their handoff at the end.

## 0. What the target is

`AddInduct` (`Lean4Lean/Verify/Environment/Basic.lean:149`) is

    inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl')
        (m₂ : ConstMap) (env₂ : VEnv) : Prop
      -- TODO

i.e. **an inductive with no constructors**, hence uninhabited, hence `TrEnv'.induct`
(`Basic.lean:628`) can never fire and every environment containing an inductive is outside
`TrEnv`.  "The flip" is giving it a constructor.

Verified by `scripts/exists.lean` (2026-09-03 16:05 UTC): `Lean4Lean.AddInduct` FOUND, module
`Lean4Lean.Verify.Environment.Basic`, arity 5, cone 276, no `sorryAx`.  (The cone of an empty
inductive is type-constants only and says nothing about satisfiability — the script prints that
caveat itself.)

## 1. Section (a): the clause-by-clause re-measurement — IN PROGRESS
