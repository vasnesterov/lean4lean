# Handoff: `ElimNestedInductive.Result.RestoreData` in general — `Built`, `FreshIn`, `tyLvls`-WF

**Owner files:** `Lean4Lean/Verify/Inductive/RestoreDataGeneral.lean` (new, mine) and this file.
Everything else in the tree is read-only for this round.

## §1 Written before any Lean — the brief as received, and my priors

Written at the top of the round, before opening a single Lean file, per standing rule (twelve API
crashes this session; only the rounds that wrote §1 first were reconstructible).

### §1.1 What the brief asserts (all of it to be re-verified, none of it to be taken on trust)

The brief hands me a status table for the fields of `RestoreData`, plus three claims about the
work. I record it verbatim as *claims*, so that if I refute one the refutation is visible:

| # | claim as given | to check by |
|---|---|---|
| C1 | `auxRec` is **removable** — derivable from the gate condition alone via `Lean4Lean.NoNestedDeclNames.auxRecName` (`Verify/Inductive/RestoreFaithful.lean`) | read the statement; check it really has only gate premises |
| C2 | `ownName`, `ownCtor` are **discharged** from the gate: `…Result.ownName_of_gate`, `.ownCtor_of_gate` | `exists.lean` + statement read |
| C3 | `head` is **reduced only**, via `Lean4Lean.presentedHead_clean_of_declared`, residual = a fact about `aux2nested`'s *values* | read the residual hypothesis |
| C4 | the flip now needs `Built`, `FreshIn`, `tyLvls`-WF **in general** | the flip's own call sites (`users.lean`) |
| C5 | `Lean4Lean.VIndRestore.csubstTy_freshIn` (`Theory/Inductive/TeleMove2.lean`) already proves the `FreshIn` fact **from type-staging success alone**; a previous round used this as a reason not to build a second route | read it; check the premise really is only staging |
| C6 | no `_nested`-prefixed constant reaches a real environment, yet `Lean4Lean.VEnv.NoNestedN` is *not* an environment-wide invariant (`axiom _nested.zzz` still accepted, `#eval`-checked in `RestoreFaithful.lean`) | read the `#eval`; re-run it |

### §1.2 My priors, recorded before measuring

Stated now so my bias is on the record. I will mark each ✔/✘ in §5 after measurement.

1. **`FreshIn` is already general (C5 true).** Prior: **likely, ~75%.** The brief says a previous
   round found and *relied* on it, and freshness of a substitution's introduced variables is
   exactly the kind of fact that falls out of staging bookkeeping without needing the block. Risk:
   `csubstTy_freshIn` may be about the *type* telescope's freshness only, and `RestoreData.FreshIn`
   may quantify over the *constructor* telescopes too — in which case it is "general modulo one
   named lemma", not general. I will look for an arity/shape mismatch first.
2. **`Built` is the hard one, and is open or nearly so.** Prior: **~65% open.** `Built` smells
   like "the auxiliary block actually got constructed by `ElimNestedInductive`", i.e. a fact about
   the *producer*, not about staging. Producer facts in this tree have historically needed a
   `TrIndDeclN`-shaped bridge, and there is a concurrent stream on
   `TrIndDeclNProducer.lean` — which is itself evidence that `Built` is where the open work is,
   and also a collision risk I must stay clear of.
3. **`tyLvls`-WF is general modulo a named lemma.** Prior: **~60%.** Level well-formedness has been
   discharged generically elsewhere in this tree (the `uvars`/`VLevel.WF` machinery is mature), so
   I expect the content to be a `List.Forall`-style lift over an already-proved single-level fact,
   with the only real work being the *stated* form matching what the flip consumes.
4. **The `head` residual is discharged by the gate, not by the wider check.** Prior: **~55%**, and
   this is my least confident prior. Reasoning: C6 says `NoNestedN` is *not* an environment
   invariant, so any route that needs an environment-wide "nothing is `_nested`" fact is dead
   without the wider check in `docs/decision-nested-prefix-all-decls.md`. But the residual is
   about `aux2nested`'s *values* — the map the producer builds — which is a property of a *local
   datum*, and local data are exactly what the gate constrains. So I expect gate-dischargeable.
   Counter-prior worth ~35%: the residual is about names *in the range* of `aux2nested` being
   absent from the environment, which the gate cannot see, and then the wider check is needed.
5. **Something in my assignment is already done.** Prior: **~70% that at least one of the three
   classifications comes back "already general, here is where".** Two rounds today found their
   work already present; the brief itself flags C5 as a candidate. I will run `shape.lean` before
   writing any proof, and I expect that to be the single highest-value action of the round.
6. **The arity-0 witness at `ntreeAux` will cost a larger cone than a block-specific route.**
   Prior: **~85%.** A predecessor already accepted a larger cone deliberately for the same reason
   and the brief endorses it, so I will not treat cone growth as a defect provided the route is
   through general theorems.
7. **Vacuity risk is real.** Prior: `nfnAux` is degenerate; my worry is a *different* degeneracy —
   that the general statements I prove are instantiable at `ntreeAux` only because a hypothesis is
   satisfied trivially (e.g. an empty nested-occurrence list). I will check that the witness
   exercises a **non-empty** `aux2nested` and a **non-empty** nested occurrence set.

### §1.3 Figures I am explicitly not trusting

Per the brief: fifteen brief-level errors this session, including assigning already-done work and
pricing a residue at the wrong environment twice. So: every cone number, every "hole-free", every
file:line in §1.1 gets re-measured with `scripts/exists.lean` / `scripts/shape.lean` /
`scripts/users.lean` before it appears in a later section as fact. `WATCHED IN CONE` reported
alongside `sorryAx` for every claim, since a clean `sorryAx` line does not clear the watch list.

## §2 Pre-flight measurements

(filled in below as they are taken)
