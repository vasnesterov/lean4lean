# Handoff — the `Verify/TypeChecker` + `Verify/Typing` stream

Scope of ownership for this stream: `Lean4Lean/Verify/TypeChecker/*`, `Lean4Lean/Verify/Typing/*`,
`Lean4Lean/Verify/EqSafety.lean`, `Lean4Lean/Verify/QuotConsts.lean`, and new files under
`Lean4Lean/Verify/`.

Everything below is separated into **machine-checked** (a Lean declaration compiles, or an
axiom listing was produced) and **read off source** (a claim from reading code and docstrings,
not compiled).

---

## 0. Corrections to the brief I was given

Two of the brief's facts are wrong; both are machine-checked corrections.

| brief said | actually |
|---|---|
| `InferType.lean` has 3 `sorry`s | it has **1** (`inferProj.WF`, line 433 before my edits) |
| `EqSafety.lean` has 1 `sorry` | it has **0** — the file is already `sorry`-free |
| owned total 7 `sorry`s | owned total was **8** (`Typing/Lemmas.lean` carries 4, which the brief did not list) |

`grep -n '\bsorry\b'` over the six owned files, excluding docstring occurrences, is the check;
`lake build` reports `declaration uses sorry` at exactly the lines below.

**§4 of the brief's question about `EqSafety.lean` therefore has a short answer: there is no
remaining `sorry` in that file to be suspicious of.** Its `checkEqType.WF_quotReady` is a
*premise-carrying theorem*, not a `sorry`, and its own docstring already records that the
premise was later discharged outright by `checkEqType.WF_quotReady_closed`
(`Verify/InductFlip.lean`). I re-read all four sections: §1–§3 are proved outright, §4 is
proved from `htr`, and nothing in the file is vacuous. No correction needed.

---

## 1. Inventory (state at the start of this session)

| # | site | what it is | genuine content? | needs unique typing? |
|---|---|---|---|---|
| 1 | `TypeChecker/IsDefEq.lean:229` `tryEtaStructCore.WF` | structure-eta defeq | yes — needs a `structEta` rule the abstract spec lacks | no |
| 2 | `TypeChecker/IsDefEq.lean:522` `isDefEqUnitLike.WF` | zero-field structure eta | yes — same rule, twice, plus a kernel→abstract `IsStructure` bridge | no |
| 3 | `TypeChecker/InferType.lean:433` `inferProj.WF` | `inferProj`'s postcondition | yes, and **false once the branch is live** (`bugs-found.md` item 10) | no |
| 4 | `TypeChecker/WHNF.lean:64` `quotReduceRec.WF` | quotient ι-reduction | yes — const-application injectivity | no |
| 5 | `Typing/Lemmas.lean:712` `TrProj.weak'_inv` | inverse of `TrProj.weak'` | yes — *rigidity* + strengthening | via `IsDefEqU.weakN_iff` |
| 6 | `Typing/Lemmas.lean:727` `TrProj.defeqDFC` | transport across a defeq context | **plumbing — now closed** | yes (`uniqU`), see §3 |
| 7 | `Typing/Lemmas.lean:1344` (inside `TrProj.wf`) | unused-field level obligation | **refuted**, see §4 | no |
| 8 | `Typing/Lemmas.lean:1393` `TrProj.uniq` | functionality of `TrProj` | yes — injectivity **and** ledger G4 | no |

Items 1, 2 and 3 are the standing ruling's "do not close vacuously" set. I did not touch them.
Their `*_never_true` / `*_always_throws` siblings still compile, so the markers are intact.

---

## 2. Re-test against the newly-reachable `Theory/` machinery — result: **no change**

Measured, not assumed:

* `Verify/Typing/Lemmas.lean` already imports `Theory.Typing.UniqueTyping` and
  `Theory.Inductive.StructureClosed`. **The import wall was never what separated these
  `sorry`s from their machinery**: `IsDefEqU.weakN_iff`, `IsType.weakN_iff`,
  `IsDefEq.uniqU`, `Ctx.LiftN.one` were all already in scope. What blocks them is that those
  lemmas are themselves `sorry`.
* `Theory/Typing/ParamsBuild.lean` builds `Params` from `VEnv.WF` + one residual `PatWF`, and
  its own §"What the instance unlocks" says in the source: `church_rosser_of_patWF` is
  "**Not `sorry`-free**: it inherits `sorryAx` from `NormalEq.descend` and
  `IsDefEqU.forallE_inv_stratified`". So the wall coming down moved the blocker from
  *"nothing instantiates `Params`"* to *"`ChurchRosser.lean` has 11 `sorry`s and
  `Injectivity.lean` has 13"*. That is real progress upstream, but it unlocks **none** of my
  eight.
* `Theory/Typing/Injectivity.lean` (13 `sorry`s) is importable from `Verify/Typing/Lemmas.lean`
  with no cycle (it imports only `EnvLemmas`, `Strong`, `DeclRules`). I did not add the import,
  because after §3 no owned `sorry` is one `const_app_inv` away — see §5.

**Machine-checked:** `lake build Lean4Lean.Verify.Typing.Lemmas` succeeds and the `sorry`
warnings are exactly the ones listed.

---

## 3. Closed: `TrProj.defeqDFC` — and its "blocked on injectivity" diagnosis was wrong

`Verify/Typing/Lemmas.lean`, previously:

> **Blocked**, and not on effort. Together with `TrProj.uniq` this needs `TrProj` to be
> *functional*: … i.e. **injectivity of a constant application**. … design ledger group I,
> gated on I1 … and I13.

**That is false.** `TrProj.defeqDFC`'s conclusion is `∃ e'', TrProj env U Γ₂ s i e₂ e''` — an
**existential**. Nothing has to be recovered: the witness reuses the `D`, `T`, `C`, `us`, `ps`,
`ιs` the input derivation already chose. This is precisely the observation
`Verify/Typing/DefEqCtx.lean` already makes for `TrProj.defeqDFC_target`; it simply was never
carried across to the sibling in `Lemmas.lean`.

The proof is eleven lines and moves two things:

1. the judgements, across `hΓ` — `HasType.defeqDFC` and an inlined `VEnv.HasArgs` transport
   (inlined rather than reusing `VEnv.HasArgs.defeqDFC`, because `DefEqCtx.lean` imports
   `Lemmas.lean`, not the other way round, and a third global copy of that name would risk the
   `PatternRules`/`Verify` collision that `docs/handoff-collisions.md` just cleared);
2. the *subject*, `e₁ ⇝ e₂`, via `IsDefEqU.of_l` + `IsDefEq.hasType`.

**Machine-checked cost, and it is not free.** `#print axioms Lean4Lean.TrProj.defeqDFC` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`. The `sorryAx` enters through step 2:
`IsDefEqU.of_l`'s cone contains `IsDefEq.uniqU` (checked directly —
`IsDefEqU.of_l` and `IsDefEq.uniqU` both report `sorryAx`, while `IsDefEq.defeqDFC`,
`HasType.defeqDFC`, `IsDefEqU.defeqDFC` and `IsDefEqCtx.symm` report only `[propext, Quot.sound]`).

So this lemma is a **`uniqU` consumer, at a constant-application type, not at a Π**. It cannot
be routed through `VEnv.HasType.piUniq`. `docs/handoff-uniqu-removal.md`'s result — "`Verify/`
needs unique typing only at Π, through one lemma with two call sites" — survives **only
because `TrProj.defeqDFC` has no consumers**: `grep` over the tree finds it named in docstrings
and nowhere else. Anyone who starts consuming it adds a non-Π unique-typing site. That is
recorded in the new docstring at the theorem.

Net effect: **owned `sorry` count 8 → 7**; `Typing/Lemmas.lean` 4 → 3. The trade is honest —
an unproved statement became a proved one whose dependency (unique typing) is strictly weaker
and already tracked than the dependency it was claimed to have (const-application injectivity,
which is gated on `Params` *and* on unique typing).

---

## 4. Refuted, with a machine-checked witness: `TrProj.wf`'s open subgoal

New file, sorry-free: **`Lean4Lean/Verify/Typing/ProjLevelWitness.lean`**.

The `sorry` inside `TrProj.wf` carries this inline comment:

> Closing this is one `Ctx.LiftN.one` strengthening step per unused field.

The goal at that position (read out of the LSP, not guessed) is

```
hLE : D.isLE = false
h   : ∀ k, k ≤ i → (k = i ∨ C.FieldUsed D 0 k) → VLevel.inst us (C.fields.getD k default).lvl ≈ VLevel.zero
hlt : k < i
hu  : ¬C.FieldUsed D 0 k
⊢ VLevel.inst us (C.fields.getD k default).lvl ≈ VLevel.inst us VLevel.zero
```

— a **level equivalence**. Strengthening produces typing judgements; it cannot produce this.
And the subgoal is not merely unproved: it is **false**, at the very witness `TrProj.wf`'s own
docstring constructs.

`barDecl` is `structure Bar : Prop where (n : Prop) (h : ∀ p : Prop, p)`, in `VInductDecl'`
form. (The docstring's `Bar` uses `Nat` for field 0; `Prop` is substituted only because the
empty environment has no `Nat` — all the refutation needs is a field whose recorded level is
not `≈ .zero`.) Field 0 has `lvl = .succ .zero` and is unused by the rest of the telescope;
field 1 has `lvl = .imax (.succ .zero) .zero ≈ .zero`, so F17's obligation at `k = i = 1` is
discharged and says nothing at `k = 0`.

Machine-checked in that file:

* `barDecl_WF : barDecl.WF .empty` — a full `VInductDecl'.WF` witness with two fields;
* `barEnv_IsStructure : barEnv.IsStructure ``Bar barDecl barType barCtor`;
* `barDecl_not_LECond : ¬ barDecl.LECond` — so `isLE = false` is **forced**, not merely
  permitted, and tightening the `isLE` claim to an iff would not rescue the subgoal;
* `bar_not_fieldUsed : ¬ barCtor.FieldUsed barDecl 0 0`;
* **`barRefutes`** — *every* hypothesis of the goal state above, satisfied simultaneously
  (`HS`, `hΓ`, `he`, `h3`, `h4`, `h5`, `h7`, `hpsA`, `hιsA`, `hi`, `hLE`, `h`, `hlt`, `hu`),
  together with the negated conclusion.

`#print axioms Lean4Lean.barRefutes` → `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

**What this does and does not say.** It does *not* refute `TrProj.wf`. It refutes the subgoal
the current proof reduces it to — i.e. the `hlv` premise of `projTerm_hasType` cannot be
established, so the route through `projTerm_hasType` is dead as written and no amount of
strengthening machinery revives it. The reformulation the `TrProj.wf` docstring describes (the
peel loop, processing outermost-first and stripping unused binders) is the only route left, and
*that* is where the `Ctx.LiftN 1 0 Δ (dom :: Δ)` instances the comment mentions actually appear
— one per unused field, in the reformulated proof, not in the present goal.

Note also: `barDecl` is a second complete `VInductDecl'.WF` witness for the tree (after
`fooDecl` in `Theory/Inductive/DeclExamples.lean`) and the first with **two** fields, so it
exercises `VIndCtor.WF.fields` at a non-zero index and `VIndField.WF.hasType` at a `forallE`.
It is reusable for any other question about unused/used fields.

---

## 5. Still open — with the exact failing step, and three fact-label corrections

`Theory/Typing/Injectivity.lean`'s module docstring already partitions constant-application
facts into **(A) disjointness** (`const_forallE_inv`, `const_sort_inv` — this is ledger I13),
**(B) injectivity** (`const_app_inv`), and **(C) rigidity** (deliberately *unstated*, because a
faithful formulation mentions weak-head reduction, which lives downstream in
`HeadReduction.lean`). Three of my sites had the wrong label. I corrected the docstrings in the
files I own; the ones in files I do not own are listed at the end for the orchestrator.

### 5.1 `TrProj.weak'_inv` (`Typing/Lemmas.lean:712`)

Failing step, precisely: from `HasType Γ' (e.lift' l) B` with `B.Skips`, `HasType.skips` +
strengthening gives `HasType Γ e B₀` where `B = B₀.liftN n k`; `uniqU` gives
`B₀.liftN n k ≡ (.const S us).mkApp (ps ++ ιs)`. **The step that does not exist** is concluding
that `B₀` is itself an application of `S`. That is not `const_app_inv` — that fact requires
*both* sides to be constant applications, and here only one is. It is fact **(C)**, rigidity,
which `Injectivity.lean` names `TrProj.weak'_inv` as the sole consumer of and deliberately does
not state.

Two smaller sub-gaps on the same route, unchanged and worth not rediscovering: `HasType.skips`
is stated for `Ctx.LiftN` while this lemma is over `Ctx.Lift'`; and `IsDefEqU.weakN_iff`'s
forward direction is `sorry` (`Theory/Typing/UniqueTyping.lean:172`).

The old docstring's "gated on I1 and I13" was wrong on the fact **and** wrong on the sibling
(`TrProj.defeqDFC` is now proved). Corrected in place.

### 5.2 `TrProj.uniq` (`Typing/Lemmas.lean:1393`)

Genuinely blocked, and on **two** things, not one:

1. **(B) `IsDefEqU.const_app_inv`** — `sorry` in `Injectivity.lean`, plus its two side
   conditions (`RuleFreeHead env S`, which is ledger **M2** and needs `VEnv.Sig`; and `IsType`
   on the application, which is free here because the fact is used at the *type* of a term).
2. **Ledger G4, `IsStructure` uniqueness** — `env.IsStructure S D T C → env.IsStructure S D' T' C' → D = D' ∧ T = T' ∧ C = C'`.
   `VEnv.IsStructure`'s own docstring says this is "**Deliberately absent**". Note that **no
   statement of it exists anywhere in the tree**, which by `Injectivity.lean`'s own standard
   ("a missing statement is worse than an open one") is the worse of the two situations. If
   someone wants a cheap contribution, writing `VEnv.IsStructure.unique` down — even as a
   `sorry` — is it.

Unlike `defeqDFC`, the existential trick does **not** apply: both targets `e₁'`, `e₂'` are
*given*, so their `us`/`ps`/`ιs` cannot be chosen. I checked this specifically; the two lemmas
looked identical in the docstrings and are not.

### 5.3 `quotReduceRec.WF` (`TypeChecker/WHNF.lean:64`)

Blocked, diagnosis substantially confirmed, one label corrected: the needed fact is **(B)
`const_app_inv`**, not I13/`const_forallE_inv` as the docstring said. (`Injectivity.lean`'s
module docstring already lists this branch under (B) — the two files disagreed.) The residual
is therefore *two* open statements: `const_app_inv` itself, and `RuleFreeHead env ``Quot``
(true — `Quot` heads no rule, `quotDefEq`'s head is `Quot.lift` — but derivable from `VEnv.WF`
only via ledger M2 / `VEnv.Sig`). Corrected in place.

The existential trick does not apply here either: the postcondition is `c.TrExpr e₁ e'` with
`e'` **fixed** as the translation of the input, so the reduct's target cannot be chosen. Read
off source, not compiled.

### 5.4 The three do-not-close statements

`tryEtaStructCore.WF`, `isDefEqUnitLike.WF`, `inferProj.WF` — untouched, per the standing
ruling. Nothing in this session's work makes any of them honestly provable; they need a
`structEta` constructor the abstract spec does not have, and `inferProj.WF` is additionally
*false* once the branch is live (`bugs-found.md` item 10). The nine `not_*Info` /
`*_never_true` / `*_always_throws` markers all still compile.

---

## 6. Non-vacuity audit of everything claimed above

Applying the stated test — *can the residual's quantifiers be instantiated so its premises
degenerate into the target's?*

* `TrProj.defeqDFC` — not a reduction, an outright proof. Fired at a non-degenerate input: its
  proof does real transport work on `hty`, `hargs` and `hιargs`, and the `sorryAx` in its cone
  is a genuine dependency (unique typing), not a hidden vacuity. Note that it is *not* vacuous
  in the `AddInduct` sense either: `barEnv_IsStructure` (§4) shows `TrProj`'s `IsStructure`
  premise is inhabited, so `TrProj` derivations exist at the abstract level even though no
  *kernel* term reaches one yet.
* `barRefutes` — the strongest available form: not "this does not follow", but "here are all
  the hypotheses and the negated conclusion", closed, `sorryAx`-free. No quantifier in it is
  left free to degenerate.
* §5's three entries are **not** stated as reductions and nothing is claimed proved from them.
  Where I name a residual I say whether the statement exists in the tree (5.2's item 1, 5.3)
  or does not (5.2's item 2, 5.1).

One claim in this document is *read off source and not compiled*: 5.3's "the existential trick
does not apply because `e'` is fixed". Everything else in §3–§5 is either a compiled Lean
declaration or an `#print axioms` output.

---

## 7. Pick up first

1. **`TrProj.wf`'s reformulation.** §4 kills the current route outright, so this is now the
   only live one, and `ProjLevelWitness.lean` gives a concrete two-field structure to test it
   against at every step. The residual after reformulation is `i` instances of
   `Ctx.LiftN 1 0 Δ (dom :: Δ)` — a *strictly smaller* ask than `IsDefEqU.weakN_iff`, and
   `NormalEq.weakN_inv_DFC` (`Theory/Typing/ChurchRosser.lean:311`) is the lemma that delivers
   it most directly.
2. **Write down `VEnv.IsStructure.unique` (ledger G4)**, even as a `sorry`. It is the only
   residual in this stream with *no statement at all*, and `TrProj.uniq` needs it independently
   of everything the injectivity stream is doing.
3. **Do not** re-attempt the `Params`-unlocks-`TrProj` route (§2), and do not re-attempt
   `const_app_inv` for `TrProj.defeqDFC` (§3) or `IsDefEq.uniq` for `TrProj.uniq` (already
   recorded as rejected in its docstring, and confirmed).

## 8. For the orchestrator — corrections in files this stream does not own

Not edited; reported.

* `Theory/Typing/Injectivity.lean`, module docstring, fact (B)'s consumer list names
  "`TrProj.uniq` / `TrProj.defeqDFC` (`Verify/Typing/Lemmas.lean`)". **`TrProj.defeqDFC` no
  longer needs (B); it is proved.** The list should drop it.
* `Verify/Typing/DefEqCtx.lean` (owned, but the statement is about a neighbour): its docstring
  says of `TrProj.defeqDFC_target` that a target-preserving statement "never needs
  `TrProj.uniq`. **Nothing here is injectivity-blocked.**" That is right, and §3 shows the same
  argument covers the *subject*-moving sibling too, at the price of one `uniqU` appeal.
