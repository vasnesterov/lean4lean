# Handoff: a general nested producer for `Lean4Lean.TrIndDeclN`

Owner file: `Lean4Lean/Verify/Inductive/TrIndDeclNProducer.lean` (new, this round).
Round opened: 2026-09-03T23:21:13Z UTC, at commit `4fe770c`.

## §1 — Priors, recorded BEFORE any measurement

This section is written before I have opened a single Lean file or run a single script, so that
the difference between what I expected and what is there is visible. Nothing below is a
measurement; everything below may turn out wrong, and where it does I will say so explicitly in
§2 rather than quietly overwriting it.

### 1.1 What the brief told me (all of it unverified)

- The only things concluding a whole `TrIndDeclN` are `Lean4Lean.NestedWit.trIndDeclN_wit`
  (a concrete witness) and the non-nested `Lean4Lean.TrIndDecl.toN`; there is no general nested
  producer of the relation as a whole.
- The `trSpine` field is no longer an obstacle. Two independent general sufficient conditions:
  - level route: `Lean4Lean.VIndRestore.trSpine_of_resultSortInhab` (arity 21, cone 3345) and
    `Lean4Lean.trIndDeclN_of_succLevel` (arity 20, cone 3348);
  - head-member route: `Lean4Lean.VIndRestore.spineHargsN_of_head_indexFree` (arity 15,
    cone 3378) and `Lean4Lean.trIndDeclN_of_head_indexFree` (arity 20, cone 3380) — reportedly
    carrying no level condition and no environment condition.
- Ownership claim to check, not repeat: `Built` / `FreshIn` / `tyLvls`-WF are `RestoreData`
  business; `Faithful` is `Verify/Inductive/RestoreFaithful.lean`'s.
- Census target: 13 holes, NOT BUILT 0; three guards passing; zero in-repo section-variable
  warnings.
- The brief warns me that fifteen of its own figures this session were wrong, including an
  inverted conclusion and a cone priced at the wrong environment twice. So every arity and cone
  number above is to be re-measured, and I expect at least one of them to be off.

### 1.2 My priors on the field checklist (part (a))

I have not read the structure. I expect `TrIndDeclN` to be a structure (or a structure-like
bundle) with somewhere between **5 and 9 fields**, and I expect them to fall roughly into:

1. a *shape/arity* field relating the declaration's parameter count and universe count to the
   translated `VInductDecl` — I expect this to be **already general**, discharged by `rfl`-style
   or arithmetic reasoning, because it carries no semantic content;
2. a *type translation* field for the inductive types themselves — I expect **general modulo a
   named lemma**, most likely something already in `InductR.lean`;
3. a *constructor translation* field — same, but I expect this one to be the fiddliest of the
   "general modulo" group, because constructors are where nesting actually bites;
4. `trSpine` — **already general**, via the two routes named above. I expect the head-member
   route to be the one I actually use, precisely because the brief says it carries no level and
   no environment condition, which makes it cheaper to satisfy in the arity-0 witness of part (d);
5. `Built` — **open**, and genuinely `RestoreData`'s;
6. `FreshIn` — **open**, `RestoreData`'s;
7. `tyLvls`-WF (or similarly named level-well-formedness) — **open**, `RestoreData`'s;
8. `Faithful` — **open**, `RestoreFaithful.lean`'s.

**Prior on the count of open fields: 4** (items 5-8), i.e. exactly the four the brief names.
I put maybe 55% on that being right. The two ways I expect to be wrong, in order of likelihood:

- (most likely) **one of the four "open" fields is already discharged in general** somewhere I
  will only find with `shape.lean`, because that is the failure mode `shape.lean`'s own docstring
  says has bitten ten times, and the brief itself admits to sending a round at work already done.
  If I had to bet on which, I would bet on `tyLvls`-WF, since level well-formedness tends to be
  syntactic and therefore cheap.
- (next) **there is a field the brief does not mention at all** — I would guess something about
  the nested occurrence map / the restore witness being a *pre*-condition rather than derived.
  A structure with a nesting story usually carries a datum plus a coherence law, and the brief
  names only laws.

### 1.3 My priors on the assembly (part (b))

I expect the assembled theorem to have, beyond the open-field hypotheses, an irreducible core of
"input" hypotheses that are not open questions at all but simply the data: the source declaration,
the target `VInductDecl`, and whichever of the two `trSpine` routes I pick. So I predict an arity
in the **low-to-mid twenties**, comparable to `trIndDeclN_of_head_indexFree`'s reported 20, and
a cone within a few hundred of 3380. I do **not** expect the assembly itself to be hard; the risk
in this round is (d), not (b).

### 1.4 My priors on vacuity (part (d))

This is where I expect to lose time. The brief is explicit that a producer whose hypotheses are
jointly unsatisfiable is worthless, and demands an arity-0 existentially-closed witness at
`Lean4Lean.InductiveDeclExamples.ntreeAux` (`Theory/Inductive/NestedHead.lean:624`, `uvars = 1`,
`params = [.sort (.succ (.param 0))]`), reached through general theorems rather than
block-specific lemmas.

Priors:
- I expect `ntreeAux` to satisfy the **head-member** route (`indexFree`), because a
  `params = [.sort (.succ (.param 0))]` block whose parameter is a sort is exactly the shape with
  no indices. If instead I find `ntreeAux` has indices, the head-member route dies for the
  witness and I fall back to the level route, whose `resultSortInhab` premise the
  `.succ (.param 0)` parameter looks tailor-made to supply.
- I expect the four open fields to be **satisfiable for `ntreeAux` only by borrowing from
  `NestedWit.trIndDeclN_wit`**, i.e. the existing concrete witness. That would be
  block-specific, which the brief forbids as the *route*. So I expect the honest outcome here is
  a witness that is arity-0 and existentially closed but whose open-field components come from
  the concrete witness, and I will label that clearly as "satisfiable, but not yet via general
  theorems" rather than claim the stronger thing. If I can get the general route, I will; I put
  only 35% on it.
- Degeneracy trap I have been warned about: `nfnAux` (`uvars = 0`, `params = []`). I will assert
  the witness's `uvars` and `params` numerically in the file so that it cannot silently become
  `nfnAux`.

### 1.5 Predictions I am committing to, so they can be scored

| # | Prediction | Confidence |
|---|---|---|
| P1 | `TrIndDeclN` is a structure with 5-9 fields | 70% |
| P2 | Exactly 4 fields are open | 55% |
| P3 | At least one brief-supplied arity or cone number is wrong | 70% |
| P4 | `trSpine` is genuinely general (both routes real, neither a hole) | 80% |
| P5 | `ntreeAux` satisfies the head-member (`indexFree`) route | 60% |
| P6 | The arity-0 witness needs the concrete `trIndDeclN_wit` for at least one open field | 65% |
| P7 | Ownership attribution in the brief is correct for all four open fields | 60% |
| P8 | Census stays at 13 / NOT BUILT 0 (my file adds no hole) | 85% |

§2 onward is written after measurement.
