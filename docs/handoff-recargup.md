# `VIndRecArg.exists_indep` — the statement repaired in `Decl.lean`, and the halves re-proved against it

Stream of 2026-09-03.  Files touched: `Lean4Lean/Theory/Inductive/Decl.lean` (the hole's own
file, granted for this task), `Lean4Lean/Theory/Inductive/RecArgIndep.lean`, and this file.
`Verify/Soundness.lean`, `Verify/Axioms.lean`, `Verify/Guard.lean` **not touched, not opened for
writing, not `touch`ed**.

Verdict in one line: **the edit was made, in a form the brief did not anticipate; the tree is
green apart from another stream's work-in-progress file; the census still reads 13; and all
three previously-closed halves are re-proved against the strictly stronger conclusion —
sorry-free, and *without* the `SortUniq` charge the previous round expected them to pay.**
Two of the previous round's recommendations were **refuted as literally stated**, both by
layering, and the repair had to be re-expressed.

---

## 0. Measurements (mine, this session, all after a rebuild)

| quantity | value | how |
| --- | --- | --- |
| tree at start | `lake build` green, **1555 jobs**, commit `3f76a53` | full build |
| holes at start | **13** | `lake env lean --run scripts/sorry-census-all.lean` |
| holes at finish | **13**, `VIndRecArg.exists_indep` among them | same |
| `exists_indep` transitive users, before edit | **1**, and it is `VIndRecArg.indepGoal_of_exists_indep` (this file's faithfulness check) | my own reverse-BFS over **all 372 built modules**, both census passes |
| `exists_indep` transitive users, after edit | **1**, same declaration | same probe re-run |
| `exists_indep` direct deps | 39 → **52** (the statement's vocabulary grew) | same probe |
| guards at finish | `24 ✓` / `whitelist ✓ INCOMPLETE` / `2-2 ✓` | `lake build` |
| `RecArgIndep.lean` | 598 → **826 lines**, 68 jobs, green | `lake build Lean4Lean.Theory.Inductive.RecArgIndep` |
| `Decl.lean` | 1014 → **1086 lines**, 31 jobs, green, one `sorry` | `lake build Lean4Lean.Theory.Inductive.Decl` |

**Tree state at finish: `lake build` green, 1558 jobs, exit 0**, guards
`24 ✓ / whitelist ✓ INCOMPLETE / 2-2 ✓`, census `375 built / 0 unbuilt / 13 holes`.  The +3 job
count over baseline is three new modules from concurrent streams
(`Theory/Typing/PatKHead.lean`, `Theory/Typing/ShapeVar.lean`,
`Verify/TypeChecker/EtaUnitRefute.lean`), **not** my new import: the census population went
372 → 375 over the same interval.  For about ten minutes mid-round the full build *did* fail, in
`Verify/TypeChecker/EtaUnitRefute.lean` only — the `EtaUnit*` stream's untracked
work-in-progress, `Unknown identifier VEnv.WF` plus nine follow-ons — and that stream fixed it;
during that window `lake build Lean4Lean.Theory.Inductive.Decl
Lean4Lean.Theory.Inductive.RecArgIndep Lean4Lean.Verify.Guard` was green in 1184 jobs.  Two
concurrent commits (`eaf78b4`, `14e9c8d`) landed under me, so the green tree includes their
work, not only mine.

**Instrument anomaly, and it is not one of the recorded ones.**  At **08:20:19** both files I
own were rewritten to their `HEAD` contents — `md5sum` matched `HEAD`, `git diff --quiet`
returned clean, and my edits were gone — and at **08:25:04** both were rewritten *back* to my
versions, byte-identical.  No `git` state-changing command was run by me, `git stash list` is
empty, and the reflog shows only the orchestrator's `ORCHESTRATOR.md` commit.  Whatever did it
had my content to restore, so it is a sync/snapshot mechanism rather than a `git checkout`.
Consequences for anyone measuring this tree: **`md5sum` a source file immediately before and
after the build you are quoting**, because a green build plus a clean `git diff` was, for about
five minutes, a *false* report of "no edit made".  Backups of both final files are at
`/tmp/recargup/*.mine` with hashes `50b7dba4…` (Decl) and `89b72f20…` (RecArgIndep).

---

## 1. Where the previous round was wrong, and where the brief was

Both errors are **layering**, and both were invisible from inside `RecArgIndep.lean`, which sits
*downstream* of `Decl.lean`.

1. **"Add `VEnv.WF env`" is impossible at that site.**  `VEnv.WF` is defined in
   `Theory/Typing/Env.lean:136`, and `Theory/Typing/Env.lean` transitively **imports
   `Theory/Inductive/Decl.lean`** (measured: its 21-module import closure contains it).  So
   naming `VEnv.WF` in `Decl.lean` is an import cycle.  `Decl.lean`'s own closure is nine
   modules and contains no `VEnv.WF`.  What is available at that layer, and is what I used, is
   **`VEnv.Ordered`** (`Theory/Typing/Lemmas.lean:253`), which `Decl.lean` already uses at
   line 1067.
2. **"Change the conclusion to `IndepUpgrade`" is impossible for the same reason.**
   `VEnv.TeleDefEq` is an `inductive` in `Theory/Typing/ConstSubstNested.lean:148`, whose
   42-module closure **also contains `Decl.lean`**.  So *no* form of the repair that names
   `TeleDefEq` can be stated at the hole, and moving `TeleDefEq` upstream would mean editing
   `ConstSubstNested.lean`, which this stream does not own.

**What I did instead** — and this is the substantive design decision of the round.  `TeleDefEq`
was only ever used for two things, and both are expressible in `Decl.lean`'s own vocabulary:

* `VEnv.IsDefEqCtx env D.uvars Γ (ξ.reverse ++ Γ) (ξ'.reverse ++ Γ)` — `IsDefEqCtx` is in
  `Theory/Typing/Lemmas.lean:294`, which `Decl.lean` imports.  This is what `defeqDFC` moves the
  three context-relative `pos` clauses along, and it is what `RecArgIndep.teleDefEq_isDefEqCtx`
  (last round's composition) was *producing*.
* `env.IsDefEqType D.uvars Γ (r.canonType D i) (r'.canonType D i)` — the telescope congruence,
  which is what `mkPi_congrU` was producing.

So the hole's conclusion is now **the original six conjuncts verbatim, plus those two**.  Three
consequences, each machine-checked below: it is a *strict superset* of the old conclusion (so
the strengthening costs a consumer nothing, and needs **no `SortUniq`** to recover the old
form — unlike `indepGoal_of_indepUpgrade`, which does); the degenerate witness still satisfies
it for free; and the consumer is proved over it directly.

**A third alternative I rejected, with the reason**: state the entrywise relation index-wise
(`∀ k, ξ[k]? = some A → ξ'[k]? = some B → ∃ u, IsDefEq ((ξ.take k).reverse ++ Γ) A B (.sort u)`).
That is *stronger* than `TeleDefEq` — it has no analogue of `TeleDefEq.rfl`, which deliberately
carries no typing — and it would therefore have **broken the three degenerate halves**, which is
exactly the failure mode the brief told me to check for.  Same objection kills stating the
conclusion with `IsDefEqCtx` *alone* and no `hOn` hypothesis: `IsDefEqCtx.refl`
(`Lemmas.lean:316`) needs `OnCtx`, so reflexivity is not free.  Which is why `hOn` is a
hypothesis — see §2.

## 2. The new statement (`Decl.lean`, the `sorry` is at line 645)

```
theorem VIndRecArg.exists_indep {env₀ env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (henv₀ : VEnv.Ordered env₀)
    (henv : VEnv.Ordered env)
    (hstage : env₀.addIndTypes D = some env)
    (hlen : pre.length = i)
    (hΓ : Γ = (pre.map (·.type)).reverse ++ D.params.reverse)
    (hpre : ∀ (i' : Nat) (F' : VIndField), pre[i']? = some F' →
      F'.WF env D (pre.take i') (((pre.take i').map (·.type)).reverse ++ D.params.reverse) i')
    (hty : env.HasType D.uvars Γ F.type (.sort F.lvl))
    (hbind : ∀ B ∈ r.binders, D.NoBlock B)
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i)) :
    ∃ r' : VIndRecArg,
      r'.idx = r.idx ∧ r'.args = r.args ∧ r'.binders.length = r.binders.length ∧
      (∀ B ∈ r'.binders, D.NoBlock B) ∧
      env.IsDefEqType D.uvars Γ F.type (r'.canonType D i) ∧
      r'.BindersIndep pre i ∧
      VEnv.IsDefEqCtx env D.uvars Γ (r.binders.reverse ++ Γ) (r'.binders.reverse ++ Γ) ∧
      env.IsDefEqType D.uvars Γ (r.canonType D i) (r'.canonType D i) := by
  sorry
```

**The `sorry` is still a `sorry`.**  It was not closed, not weakened, and not converted into a
hypothesis; the census still names it, and this file's faithfulness check still applies it.

**Where every hypothesis comes from at the real call site** (`VIndCtor.WF.fields` /
`VInductDecl'.WF.ctors`, `Decl.lean:635`, which reads `∀ env₁, env.addIndTypes D = some env₁ → …
C.WF env₁ D j T`):

| hypothesis | availability |
| --- | --- |
| `hstage` | *is* `WF.ctors`'s own binder, with `env₀ :=` the pre-block environment |
| `henv₀` | the ambient `Ordered env₀` any `addInduct_WF`-shaped proof carries |
| `henv` | **[analysis, not proved]** available there; it is *not* derivable from `henv₀ + hstage` alone — that step needs `VIndType.WF` for the block, which is not a hypothesis here, which is why both are listed |
| `hpre` | mirrors `VIndCtor.WF.fields` with `pre := C.fields.take i`, so it is the **induction hypothesis** of the induction on the field index that `WF.fields` has to be proved by anyway |
| `hOn`, `hbind`, `hdefeq`, `hty` | conjuncts of `pos`'s `some` branch and of `VIndField.WF.hasType` — the caller holds them *before* it calls, since it must prove `pos` at the original `r` and then transport |

## 3. The real test: the three closed halves against the **stronger** conclusion

This is what the brief flagged as most likely to fail, because last round's witnesses are `r`
itself.  **They all re-prove, and at no new cost.**

| theorem (`RecArgIndep.lean`) | axioms | what the two new conjuncts cost |
| --- | --- | --- |
| `VIndRecArg.exists_indep_of_pre_norec` | `[propext, Quot.sound]` | nothing |
| `VIndRecArg.exists_indep_of_binders_nil` | `[propext, Quot.sound]` | nothing |
| `VIndRecArg.exists_indep_of_i_zero` | `[propext, Quot.sound]` | nothing |
| `VIndRecArg.indepGoal_of_bindersIndep` | `[propext]` | nothing |

The mechanism, and it is two three-line lemmas in the new §0:

* `RecArgIndep.isDefEqCtx_refl_suffix` (`[propext]`) — `IsDefEqCtx` is reflexive over an
  **arbitrary base** given `OnCtx` of the extension; the tree only had `IsDefEqCtx.refl` at base
  `[]`.  Applied at `Δ := r.binders.reverse`, this is the new `IsDefEqCtx` conjunct at `r' = r`,
  and its input is exactly the hole's `hOn`.
* `RecArgIndep.isDefEqType_refl_r` (`[propext]`) — the right side of an `IsDefEqType` is
  `IsDefEqType` to itself **at the same recorded sort** (`⟨u, h.symm.trans h⟩`), so this is
  where the previous round's expected `SortUniq` charge does *not* appear.  A `trans` would have
  needed it; a reflexivity at a fixed sort does not.

The three halves each gained `hOn` (and the statement's other new hypotheses, all unused in
these proofs and named `_`-prefixed), so they remain textual drop-ins for the hole.
`Quot.sound` appears in three of them only because the *statement* now mentions `VIndField.WF`
and `addIndTypes`; no `sorryAx`, checked by `#print axioms`.

**Degeneracy, stated separately as the ledger asks.**  *Inhabitation*: the repaired conclusion
is inhabited on the `BindersIndep`-already-holds regime, free.  *Degeneracy*: the witness there
is `r` itself, so **nothing moves**, and `RecArgIndep.lean` §7.1 says so in the file.  Those are
two different facts and neither implies the other.  *Hole-freeness*: separately, the four
theorems above carry no `sorryAx`.

## 4. The consumer is proved over the hole's actual conclusion — and it is `SortUniq`-free

`RecArgIndep.posSome_transport_of_indepGoal` (`[propext, Quot.sound]`): from
`VIndField.PosSome env D Γ i F r` (last round's machine-checked transcription of `pos`'s `some`
branch) and the hole's conclusion, it produces `r'` with **`PosSome` at `r'`** and
`r'.BindersIndep pre i`.  That is the substitution the obligation exists for, over the statement
that is actually in `Decl.lean` — not over `IndepUpgrade`, and not by projection.

**Measured, not assumed, and it corrects my own first draft**: this theorem takes **no
`SortUniq`** hypothesis.  I wrote it with one, and the unused-variable linter rejected it.  The
reason is structural: keeping the original `IsDefEqType Γ F.type (r'.canonType D i)` conjunct
*alongside* the new telescope congruence means the consumer never composes two conversions.  So
the round's net effect on the sort-uniqueness charge is:

* the charge is **still real**, and still where last round found it — `IsDefEqType` has no
  `trans` in the tree and `isDefEqType_trans_of_sortUniq` is where it is paid;
* it now sits **entirely on whoever discharges the `sorry`** (they must hand over both
  conversions), and **none of it on whoever uses it**.  Last round's `indepGoal_of_indepUpgrade`
  still pays it, because `IndepUpgrade` carries only the telescope side.

## 5. The added hypotheses are non-vacuous *and* they exclude the old candidate counterexample

Last round exhibited `raiEnv` — a `VEnv.WF` environment satisfying all five of the old
hypotheses where `r` is not a witness (`rai_hyps`, `not_bindersIndep_raiRec1`) — and argued the
missing hypothesis was freshness.  Three new theorems settle what the added hypotheses do
(`RecArgIndep.lean` §7.3b), and the middle one is the one I did not expect:

| theorem | axioms | says |
| --- | --- | --- |
| `RecArgIndep.rai_staged` + `ordered_raiEnv0` + `ordered_raiEnv` | `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]` | the `henv₀ + hstage` pair is **inhabited**: `VEnv.empty.addIndTypes raiD = some raiEnv0` over `Ordered`.  The hypothesis does not empty the statement |
| `RecArgIndep.raiEnvP_add` | `[propext, Quot.sound]` | **`hstage` alone is not enough.**  `addIndTypes` is pure data (`addConst` never type-checks anything), so the junk environment `raiEnvP` — which declares `raiP : raiI → Sort 1` while `raiI` is *undeclared* — stages `raiD` into `raiEnv`.  Had I added only the freshness/staging hypothesis the previous round recommended, §7.2's witness would have survived it |
| `RecArgIndep.rai_not_staged` | `[propext, Quot.sound]` | **with `Ordered env₀` the witness is excluded**: no ordered environment stages `raiD` into `raiEnv`, because staging would leave `raiP` declared while `raiI` is not, and `Ordered.constsInC` (`Theory/SetModel/Consts.lean:152`) says a declared type mentions only declared constants |
| `RecArgIndep.rai_junk_not_ordered` | `[propext, Quot.sound]` | the same fact read the other way |

So `henv₀` is the load-bearing half of the pair, and `rai_hyps` is now a *record of why the
hypothesis was added* rather than a live candidate counterexample.  Its docstring was corrected
accordingly (it used to claim "all five hypotheses of `exists_indep`", which is no longer the
hypothesis list).

**Still [analysis, not proved]**: that no *other* candidate counterexample survives the new
hypotheses.  Excluding one witness is not proving the statement.

## 6. What the docstring now says, and the corrections folded into it

`Decl.lean`'s docstring was rewritten (+72 lines net for the whole hole block).  It now records, in the file rather than
only in a handoff: what the two new conjuncts are for and which three `pos` clauses need them;
that `VEnv.WF` is unavailable at that layer and why; that `henv₀` is what makes `hstage` bite,
citing `rai_not_staged`; that `hpre` makes the obligation an induction on the field index; the
**second price** (sort uniqueness) and that it is charged to the prover and not the consumer;
and — flagged as a correction — that its own previous "sits under a redex, e.g.
`(fun _ : T => Nat) r`" justification is **wrong twice over** (`raiRedex_not_noBlock`: that shape
is not an admissible binder, since `hbind` is syntactic; `raiB_betaHead`: `P a` is a block-free,
well-typed, non-redex counter-shape).  Both citations are to theorems that already existed;
what is new is that the docstring no longer asserts the refuted claim.

## 7. Pick up first

1. **Nothing else in the tree needs to change for this edit.**  The user count is 1 and it is
   the faithfulness check.  If a future round wires `exists_indep` into `addInduct_WF`, the
   hypothesis-availability table in §2 is the thing to test — and `hpre` is the one that forces
   the surrounding proof to be an induction on the field index.
2. **The `TeleDefEq` home is the one real piece of debt this round created.**  There are now two
   near-equivalent ways to say "these two telescopes are entrywise defeq" in play:
   `VEnv.TeleDefEq` (downstream, with the free `rfl`) and the `IsDefEqCtx` + congruence pair
   (upstream, at the hole).  §6.3 and §6.2b bridge them, so nothing is broken, but the clean fix
   is to **move the `VEnv.TeleDefEq` inductive from `Theory/Typing/ConstSubstNested.lean` into
   `Theory/Typing/Lemmas.lean`** (next to `IsDefEqCtx`, which is its only consumer at this
   layer) and then state the hole's conclusion with it.  That needs ownership of
   `ConstSubstNested.lean`, which this stream did not have.  It would be a pure move: the
   inductive's own dependencies are `VEnv.IsDefEq` and `List VExpr` only.
3. **`Theory/Inductive/NestedBuild.lean` now has `VNestedOcc.bindersIndep`** (`[propext,
   Quot.sound]`, a concurrent stream's), which discharges `BindersIndep` *directly* for nested
   companion fields.  I did not measure whether it makes the `∃ r'` form unnecessary on that
   regime, but it is the first producer of the clause outside `DeclExamples`, and last round's
   §8.5 ("the honest reformulation may be `BindersIndep` outright") is the question it bears on.
   **[guess]**, flagged as one: it may cover exactly the regime this hole was invented for.
4. **Do not re-price this hole as "blocked on `forallE_inv` and `SortUniq`" without §4's
   refinement.**  The `SortUniq` half is now provably a *prover-side* charge only.
5. The instrument note in §0 (files reverted and restored by something outside this session) is
   worth a ledger row of its own: for five minutes, "green build + clean `git diff`" was a false
   report of *no edit*, which is the exact inverse of the `.olean` hazard in rows 189c/191c.
