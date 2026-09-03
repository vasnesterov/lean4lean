> **RESOLVED 2026-09-01 — option (a) landed as PR #45, approved by the repository owner.**
> This file is kept for the costing of the rejected options, which is still the record of *why*
> option (c) does not close. The open question that remains is a **different, wider** one:
> whether to extend the check from inductives to every declaration. That is costed separately in
> [`decision-nested-prefix-all-decls.md`](decision-nested-prefix-all-decls.md) and is the one
> still awaiting a decision.

# Decision: the `_nested` prefix is not an environment invariant

**Status: open, needs a human call.** Nothing has been changed. This file exists so the decision
arrives costed rather than as a bare question.

*Written 2026-09-03 by the orchestrator, from reading and grepping the tree. Where I proved
nothing myself, I say so.*

## The measurement (not mine — `NestedRestore.lean` §8.2, and I re-read it)

`ownName`/`ownCtor` say a declaration's *own* type and constructor names do not carry the kernel's
reserved `_nested` prefix. **Nothing checks this, in either kernel.**

- lean4lean: `checkNoNestedAux` (`Lean4Lean/Inductive/Add.lean:920-925`) scans each constructor's
  **type** for a `_nested`-prefixed `.const`/`.proj`. Its `n : Name` argument is used only in the
  error message.
- C++: `check_no_nested_aux` (`src/kernel/inductive.cpp:1219-1233`) is the same scan, called on
  each type's **type** and each constructor's **type**. Its `name const & n` is likewise only
  formatted into the message. There is no name-level test against `*g_nested` anywhere in
  `src/kernel`.
- Elaboration does not catch it: `Lean.isReservedName` is a registry, and nothing in the Lean 4
  tree registers `_nested`.

So `inductive _nested.Foo` is accepted by both kernels **when the prefixed name occurs in no
constructor type of the block**.

**That qualifier was missing from the first three versions of this file, and it matters.** Measured
on 2026-09-03 by probing `Environment.addInductive` directly at the pre-check tree: the existing
*type* scan already rejects the natural cases, because a constructor's type normally mentions the
inductive itself.

    nested block, member `_nested.NB`          -> ALREADY REJECTED ("...'_nested.NB.mk', it uses the reserved prefix")
    plain  block, member `_nested.PB`          -> ALREADY REJECTED, same reason
    inductive _nested.Zzz : Type, no ctors     -> ACCEPTED, stored
    inductive TB | _nested.TB.mk : TB          -> ACCEPTED, both stored

So the class a name check newly rejects is exactly the last two shapes: **a `_nested`-prefixed name
that appears in no constructor type.** Everything else is already caught.

**This is not claimed to be an exploit.** No witness was constructed, and two mitigations may close
every path: `mkUniqueName`/`mk_unique_name` skip names the environment already holds, and the
renamed recursors end in `rec_k`, never `rec`. What is certain is narrower: **the prefix is not an
invariant of the environment, so it cannot be used as a name barrier without the check** — and
`ownName`/`ownCtor` therefore stay hypotheses, with three consumers.

## What I checked myself this round

**Where the two fields are actually used** — six sites, in two shapes:

| shape | sites | what it needs |
| --- | --- | --- |
| `List.lookup … = none` via `recRenames_dom` / `ctorRenames_dom` | `NestedRestore.lean:432`, `:438`, `:532`, `:549` | only that the declared name is **not in the renaming table's domain** — a *distinctness* fact |
| `¬ IsNestedName ‹declared name›` as the **conclusion** | `:516` (`resTy`), and the `resRec` branch decision | the prefix fact itself |

**This is what kills option (c).** I had guessed the corner could avoid the prefix-as-barrier route
entirely, the way `ProjNoNested.lean` did for a neighbouring obligation, and that
`fresh_of_addIndTypes` (`Theory/Inductive/NestedFresh.lean:59`) was the template — it derives
"not already in the environment" from *the step's own success*, costing the caller nothing.

That template works for the four lookup-miss sites. It **cannot** work for `resTy`: there the
prefix fact is the conclusion, and at exactly the inputs in question — a user writing
`inductive _nested.Foo` — **the conclusion is false**. No derivation repairs a false statement.

**Caveat, stated because it changes who should trust this:** I established this by reading the six
sites, not by attempting the proof. A stream given the corner might weaken `resTy`'s *consumer*
rather than `resTy`, which I have not priced and which is the one route that could revive (c).

## The related witness already in the tree

`NestedOccData.lean:980-991` constructs a block whose member 0 is constructor-less and carries
exactly the name `mkUniqueName` would invent. Because it has no constructors, its name appears in
no constructor *type*, so `checkNoNestedAux` — which scans types only — never sees it; `run` then
invents the same name for the companion and `r.types` carries it twice.

The outcome is a **rejection**: `constant has already been declared`, and **the C++ kernel rejects
it the same way for the same reason.** So the duplicate-constant check catches that particular
collision. What the witness settles is the proof-side question — `RestoreData.ownName` is what
excludes the state, and nothing in the implementation does.

## Does this affect the theory, or only naming? (measured 2026-09-03)

**Only naming.** The delta class above is *defined* by the prefixed name not occurring in any type
in the block -- which is precisely the condition under which the existing type scan stays silent.
So renaming such a declaration changes **no type**: in the constructor-less case there are no
constructor types, and in the `_nested.TB.mk` case the constructor's type is `TB`, untouched by
renaming the constructor. The stored environment differs in one label and nothing else, so any
development using `_nested.Zzz` can be rewritten with `Zzz` and is then accepted, giving an
isomorphic environment. Provable propositions, up to renaming of constants, are unchanged.

**This was worth checking rather than assuming, because the kernel is NOT renaming-invariant in
general.** `Environment.primitives` (`Environment/Basic.lean:34`) keys special reduction on names,
and `checkName` throws `unexpected use of primitive name` for any name in it -- so a declaration
named `Nat.gcd` genuinely must satisfy the recognizer, and there the name *does* change what is
accepted. That list is `Bool`/`Nat`/`String.ofList`/`Char.ofNat` plus the `Nat` arithmetic
operations, every entry a fixed literal, and **no `_nested`-prefixed name is in it or could be.**
The other name-keyed path, `isNonRecStructure` (which gates the eta rule), dispatches on a
declaration's *shape*, not its name.

**Consequence for the decision.** This weakens the case for the check as a *safety* argument and
leaves it intact as a *proof* argument. No theory is excluded, so nothing of value is lost -- but by
the same token nothing unsound is being blocked. The reason to take it is unchanged and is the one
in the next section: the prefix cannot serve as a barrier without it.

## The options, as they now stand

**(a) Add the check.** Two lines beside the existing `checkNoNestedAux` calls at
`Lean4Lean/Inductive/Add.lean:930-935`:

    checkNoNestedAuxName indType.name
    checkNoNestedAuxName ctor.name

with `checkNoNestedAuxName n := if (`_nested).isPrefixOf n then throw … else pure ()`.

Cost: a **behavioural divergence** — lean4lean would reject declarations the C++ kernel accepts, so
it goes in `divergences.md`. Risk to goal 1 is low but non-zero and must be measured, not assumed:
any arena test declaring a `_nested`-prefixed name would flip. Benefit: `ownName`/`ownCtor` become
theorems and three consumers unblock.

**(b) Leave the hypotheses undischarged.** Costs nothing today; the corner's results stay
conditional on an environment property nothing establishes, which is precisely the shape
`docs/vacuity-ledger.md` §0 exists to flag. Not vacuous — the hypotheses are satisfied by every
well-behaved input — but not discharged either.

**(c) Avoid the prefix-as-barrier route.** **Available for four of the six sites, blocked at
`resTy` for the reason above.** Only a redesign of `resTy`'s consumer could revive it, unpriced.

## Recommendation

I withdraw the preference for (c) I stated earlier today: I had not priced it, and now that I have,
it does not close. Between (a) and (b) I lean to **(a)**, because the soundness argument should not
rest on an unstated property of user input, and a divergence that *rejects more* is the safe
direction for a checker — but (a) changes observable kernel behaviour, so it is the user's call and
not mine.

Whichever way it goes, `divergences.md` should record the **measurement** either way: that neither
kernel checks this is worth writing down even if we choose to match the C++ behaviour.
