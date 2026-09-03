# Handoff: the two projection-existence holes — an exact residual, and `TrProj` is inhabited

Round of **2026-09-03**.  Scope: `Lean4Lean.TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean:902`)
and `Lean4Lean.TypeChecker.Inner.inferProj.WF` (`Verify/TypeChecker/InferType.lean:468`).
Owned files: `Lean4Lean/Verify/Typing/ProjExistClose.lean` (new) and this document.  Everything
below is **[measured]** (a command run in this tree, this round) or **[read off source]**.

## 0. Bottom line

* **Neither `sorry` is closed.**  Census stays 13.  No file outside the two I own was edited.
* **The brief's target 1 *is* `TrProj.weak'_inv`.**  `Lemmas.lean:904` — the line the brief gives
  as "the projection-translation existence obligation" — is the body of the theorem at `:902`,
  which is `TrProj.weak'_inv`.  So the brief's separate question "check whether either target
  depends on `TrProj.weak'_inv`" answers itself for target 1 (identity) and is **no** for
  target 2 (§4).  **[measured]**
* **`TrProj.weak'_inv` now has a *hole-free* and **two-directional** reduction.**
  `VEnv.ProjDataStrengthen` is **equivalent** (`VEnv.projStrengthen_iff`) to the `sorry`'s
  statement, and `TrProj.weak'_inv_of_projDataStrengthen` has the `sorry`'s type at cone **717,
  no `sorryAx`** — against the previously best route `TrProj.weak'_inv_of_typing_head`
  (cone 3716, holes `{forallE_inv_stratified, rigidShapeUniqNS}`) and
  `_of_strengthen` (cone 3698, holes `{weakN_iff, forallE_inv_stratified,
  rigidShapeUniqNS}`).  `docs/handoff-trproj-weakinv.md` §5.3 recorded "an exact
  (two-directional) split — not achieved"; that gap is now closed at this shape.  **[measured]**
* **`TrProj` is inhabited, today, at a `VEnv.WF` environment, with no hypotheses.**
  `prjEnv_trProj`.  This makes the parenthetical in `inferProj.WF`'s docstring — "*vacuously
  true today (`TrProj` has no inhabitants until the keystone lands)*" — **false as stated**; the
  vacuity of `inferProj.WF` itself is unaffected (it rests on `TrEnv.not_inductInfo`, §5).
  `TrProj.weak'_inv`'s premises are therefore satisfiable, and so is its conclusion, at the same
  instance (`trProj_weak'_inv_fires`).  **[measured]**
* **`scripts/users.lean` has a measurement bug that under-reports exactly the checker-side
  holes**, `inferProj.WF` among them: it reads 0/0 where the truth is 1/70.  One-line fix in §2.
  **[measured]**
* **Neither statement is refuted, and I do not believe either is false** — §6 says why the
  counterexample hunt fails, and where the one non-classical opening is.

## 1. What each hole claims, and its users — re-measured today

`Lemmas.lean:902` (the brief's ":904" is this theorem's body line):

```lean
theorem TrProj.weak'_inv (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.Lift' l Γ Γ') (H : TrProj env U Γ' s i (e.lift' l) e') :
    ∃ e'', TrProj env U Γ s i e e'' := sorry
```

`InferType.lean:468`:

```lean
theorem inferProj.WF (he : c.TrExprS e e') (hty : c.TrExprS ety ety') (hasty : c.HasType e' ty') :
    (inferProj st i e ety).WF c s fun ty _ => ∃ e'' ty'', c.TrTyping (.proj st i e) ty e'' ty'' := sorry
```

**Users, 2026-09-03 17:04 UTC**, population 421 built modules / 25819 non-internal declarations:

| hole | DIRECT | TRANSITIVE | note |
|---|---|---|---|
| `TrProj.weak'_inv` | **1** (`TrExprS.weakFV'_inv`) | **90** | matches `docs/handoff-trproj-weakinv.md` |
| `inferProj.WF` | **1** (`inferType'.WF._unary`, internal) | **70** | `scripts/users.lean` reports **0/0** — see §2 |
| `TrProj` (the relation) | 264 | 682 | context |

### 1.1 The one-direct-user question the brief puts first

`TrProj.weak'_inv` has exactly one direct user, and its call site is the `proj` case of
`TrExprS.weakFV'_inv` (`Lemmas.lean:2081–2088`).  **Proving a special case there does not retire
the hole**, and the reason is already on the record but worth restating with the extra thing I
checked:

* The call site's lift is a `VLCtx.FVLift'`, so the inserted entries are *free variables* with
  `.vlam` types.  Nothing in `VLCtx.FVLift'`/`VLCtx.WF` makes those types **inhabited**, and
  inhabitation is the only property that would help — `ProjWeakInv.lean`'s
  `constAppTypeStrengthen_inhab` closes the residual outright over inhabited lifts, at every
  depth.  So the special case *is* the general case.  **[read off source]**
* The extra data the call site does have — a `TrExprS` for the subterm in the smaller context,
  hence `VExpr.WF env U Γ e` — was checked by an earlier round and is worth nothing:
  `VExpr.WF.weak'_iff` already yields it (`Lemmas.lean:770`, Update 3).  I re-read that argument
  and agree; it is not re-derived here.
* `inferProj.WF`'s single direct user is the internal companion of `inferType'.WF`, i.e. the
  checker's main recursion, and it consumes the conclusion in full (`hF h` at
  `InferType.lean:579`).  No special case is available: the postcondition is what
  `inferType'.WF` must hand on.

## 2. An instrument bug: `scripts/users.lean` under-reports the checker-side holes

`users.lean` seeds its reverse-reachability BFS from the **internal-filtered** direct set:

```lean
let direct := (rev.getD target #[]).filter (fun n => !n.isInternal)   -- line 117
…
let mut frontier := direct                                            -- line 120
```

Its own comment says "*Traverse everything; filter only when COUNTING*" — and it does keep
internals in the graph, but the *seed* is filtered, so a declaration whose only direct user is an
internal name scores **0 direct, 0 transitive**.  That is exactly the shape of every theorem
consumed through a well-founded-recursion companion.  Measured with the one-line patch
(`frontier := rev.getD target #[]`), 2026-09-03 17:04 UTC:

| name | `users.lean` today | corrected | raw direct user |
|---|---|---|---|
| `TypeChecker.Inner.inferProj.WF` | 0 / 0 | **0 / 70** | `inferType'.WF._unary` |
| `TypeChecker.Inner.inferType'.WF` | 0 / 0 | **0 / 69** | `Methods.withFuel.WF._f` |
| `TrProj.weak'_inv` | 1 / 90 | 1 / 90 | (unaffected) |

The 70 in `scripts/sorry-census.lean` is right; `users.lean` is wrong, and it is wrong precisely
at the checker cone — the part of the tree `kernel_sound` runs through.  **Exact edit (I do not
own this file, so I did not make it):** in `scripts/users.lean`, replace line 120

```lean
    let mut frontier := direct
```

with

```lean
    let mut frontier := rev.getD target #[]
```

`direct` stays as it is (it is the printed DIRECT figure, which should exclude internals).

## 3. `TrProj.weak'_inv`: an exact, hole-free reduction  **[measured]**

`Lean4Lean/Verify/Typing/ProjExistClose.lean` §1.  Two definitions and four theorems:

* `VEnv.ProjStrengthen env U` — the `sorry`'s statement, ∀-quantified at fixed `env`, `U`.
* `VEnv.ProjDataStrengthen env U` — **the residual**: every hypothesis is a field of `TrProj.mk`
  read at `Γ'`, every conclusion the same field read at `Γ`, with the block `(D,T,C)` and the
  levels `us` existentially quantified in the conclusion.
* `VEnv.projStrengthen_iff : env.ProjStrengthen U ↔ env.ProjDataStrengthen U`.
* `TrProj.weak'_inv_of_projDataStrengthen` — the `sorry`'s type verbatim, from the residual.

| theorem | cone | holes |
|---|---|---|
| `TrProj.weak'_inv_of_projDataStrengthen` (new) | **717** | **∅** |
| `VEnv.projStrengthen_iff` (new) | 714 | **∅** |
| `TrProj.weak'_inv_of_typing_head` (previous best) | 3716 | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `TrProj.weak'_inv_of_strengthen` | 3698 | + `weakN_iff` |
| `VEnv.ConstAppTypeStrengthen.projDataStrengthen` (new, §3 of the file) | 3702 | all three (inherited, on purpose) |

Three things this settles that were open in `docs/handoff-trproj-weakinv.md`:

1. **The split is now exact.**  §5.3 there recorded "an exact (two-directional) split — not
   achieved", with the caveat that the split's hypotheses "may be *jointly stronger* than the
   residual".  At this shape the question is closed: `ProjDataStrengthen` is **equivalent** to the
   hole, so nothing was conceded and nothing can be recovered by weakening the residual further.
2. **The reduction itself is free.**  Every previous route paid `forallE_inv_stratified` +
   `rigidShapeUniqNS` (and often `weakN_iff`) *inside the reduction*, because it discarded the two
   `HasArgs` fields and re-derived them with `VEnv.HasArgs.of_mkApp`.  Keeping them in the residual
   removes that cost: cone 3716 → **717**, holes 2 → **0**.  So the three holes in the old figures
   were **an artefact of the residual's shape**, not part of `weak'_inv`'s content.
3. **Block uniqueness (ledger G4) is irrelevant to this hole, in both directions.**  The `→`
   direction of the `iff` *fails* if the residual fixes `(D,T,C)`, because the `TrProj` the hole
   returns may certify a different block at the same name; and the `←` direction never needs
   uniqueness.  So `weak'_inv` neither needs nor supplies G4.  (Contrast `TrProj.uniq`, which
   does need it.)

**What did *not* change.**  `ProjDataStrengthen` is still the strengthening of a `HasType` at a
structure head, i.e. the same mathematical content `docs/handoff-trproj-weakinv.md` §3 analyses,
and its route status is unchanged: rigidity (gate = refuted `WeakNorm`), confluence (refuted
`NormalEq.descend`), or inhabitation (fails at every consistent environment).  §3 of the file
proves `ConstAppTypeStrengthen → ProjDataStrengthen` at `VEnv.WF env`, so every bound already
proved for the old residual bounds the new one; I claim no progress on the residual itself.

## 4. Dependency between the two holes, and on `TrProj.weak'_inv`

* **Target 1 *is* `TrProj.weak'_inv`.**  Nothing to check.
* **`inferProj.WF` does not depend on it.**  Its own forward cone's only hole is itself, and the
  one-line proof's cone is hole-free (§5).  Re-verified today.  **[measured]**
* Conversely `weak'_inv` does not depend on `inferProj.WF`.  The two holes are independent, and
  they are in **opposite states**: one is hard with a now-exact residual, the other is provable in
  one line and held open on purpose.

## 5. `inferProj.WF`: prior round's verdict re-verified independently  **[measured]**

Compiled in scratch (`/tmp/pjscratch/InferProjCheck.lean`, against this tree, today):

* `inferProj_always_throws hty` has `inferProj.WF`'s type exactly; axioms
  `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**.
* The same term proves the statement with an arbitrary extra hypothesis `(R : Prop) (_hR : R)`
  **without using it**, so no reduction of this hole can carry information.

Both facts are `docs/handoff-inferproj.md` §1 and §3, and both hold in this tree today.  I did
**not** land either (a landed second copy of the statement, proved, would invite deleting the
census row — that document's §2 argument, which I did not override), and I did not close the
`sorry`.  Recommendation unchanged: leave it open until `bugs-found.md` item 10 is decided.

**One correction to that document, from §6 below.**  Its vacuity discussion, and the `sorry`'s own
docstring, justify the vacuity partly with "`TrProj` has no inhabitants until the keystone lands".
That is **false** — see §6 — though the vacuity itself survives, since it rests on
`TrEnv.not_inductInfo`, a statement about a *translated* environment's constant map.

## 6. `TrProj` is inhabited — the parenthetical is false  **[measured]**

`ProjExistClose.lean` §2.  `prjDecl` is `structure Prj : Type where fld : Prop`:

```lean
def prjDecl : VInductDecl' where
  uvars := 0; params := []; lvl := .succ .zero
  types := [{ name := `Prj, type := .sort (.succ .zero), indices := [],
              ctors := [{ name := `Prj.mk, params := [],
                          fields := [{ type := .sort .zero, lvl := .succ .zero, recArg := none }],
                          args := [] }] }]
  isLE := true
```

| declaration | what it gives | cone | holes |
|---|---|---|---|
| `prjDecl_WF` | `prjDecl.WF .empty` | 1835 | ∅ |
| `prjEnv_eq` | `∃ e, VEnv.empty.addInduct' prjDecl = some e`, by `rfl` | — | ∅ |
| `prjEnv_WF` | **`VEnv.WF prjEnv`**, no hypotheses | 1921 | ∅ |
| `prjEnv_isStructure` | `prjEnv.IsStructure \`Prj prjDecl prjTy prjCtor` | 1923 | ∅ |
| **`prjEnv_trProj`** | **`TrProj prjEnv 0 [.const \`Prj []] \`Prj 0 (.bvar 0) (…projTerm…)`** | 1954 | ∅ |
| `prjEnv_trProj_lifted` | the same across a depth-one lift, via `TrProj.weak'` | 4352 | ∅ |
| `trProj_weak'_inv_fires` | **all four hypotheses of the `sorry` *and* its conclusion, at one instance** | 4358 | ∅ |
| `projDataStrengthen_fires` | §1's residual's hypotheses, satisfiable | 2042 | ∅ |

**Why nobody had one.**  `fooDecl` (`Theory/Inductive/DeclExamples.lean`) is the tree's only
pre-existing structure-shaped `VInductDecl'.WF` witness, and `TrProj` genuinely has **no**
derivation there: F17 (`TrProj.mk`'s last field) asks for `D.isLE = true` *or* every involved
field's level `≈ .zero`, and `fooDecl` has `isLE := false` with its one field at
`lvl = .succ .zero`.  The other three WF witnesses (`accDecl`, `mutDecl`, `wDecl`) fail
`IsStructure` on `noRec` or `types`.  One change fixes it: make the block `Type`-valued
(`lvl := .succ .zero`), which puts `LECond`'s **first** disjunct (`D.lvl.IsNeverZero`) in reach and
makes `isLE := true` legal.  `prjDecl_WF` is `fooDecl_WF`'s proof with that one clause redone.

**Scope, so this is not over-read.**

* The inserted binder in `trProj_weak'_inv_fires` is `Prop`, which is **inhabited**, so the
  instance lies inside the region `constAppTypeStrengthen_inhab` already proves outright.  It
  witnesses satisfiability and **nothing** about the obstruction, which `ProjInhab.lean` §1 pins to
  `env.Consistent`.  An uninhabited binder over `prjEnv` would need `prjEnv.Consistent`, unproved
  here and everywhere.
* `inferProj.WF`'s vacuity is untouched (§5).  What is refuted is the *reason* given for it.
* Both `IsStructure` fields `inferProj` fails to check (`types`, `noRec` — `bugs-found.md` item 10)
  are **satisfied** by `prjDecl`; that is why the witness exists, and it says nothing about item 10.

## 7. True, false, or reduced — the honest verdict

* **`TrProj.weak'_inv`: not refuted, and I do not think it is false.**  The counterexample hunt the
  brief asks for comes down to: is there a term `e`, a lift, and a structure head `S` with
  `Γ' ⊢ e.lift' l : S`-app derivable but no `S`-app type for `e` in `Γ`?  Every context-*dependent*
  rule in `VEnv.IsDefEq` is proof irrelevance, and to apply it in `Γ'` to two `x`-free proofs of
  `p` you need `p` inhabited in `Γ'` by `x`-free terms, which pushes the question back to `Γ`.  The
  three named structural attacks (proof-irrelevance through the stripped variable, the
  `Sort`-valued binder, and a `False`-like binder with an eliminator) all fail at that step, and the
  standing analysis (`ProjInhab.lean` §1) already shows the *residual* is a theorem at every
  environment with no uninhabited types.  So: **reduced, exactly (§3), not refuted.**  Anyone who
  wants to refute it should attack `VEnv.ProjDataStrengthen` directly — it is now equivalent, so a
  counterexample to it *is* a counterexample to the hole.
* **`inferProj.WF`: true today, unconditionally and cheaply (§5), and unrefutable today** — its
  post-flip falsity has no witness inside the tree, exactly as `docs/handoff-inferproj.md` §5 says.
* **Neither is vacuous** in the sense the brief means: `weak'_inv`'s premises fire (§6);
  `inferProj.WF`'s premises fire too (`he`/`hty`/`hasty` are ordinary translations) but its
  *branch* does not, which is the vacuity that matters and which is not mine to close.
* **`RecM.WF` circularity, respected.**  Nothing here constructs a `Methods.WF`; the one scratch
  check of `inferProj.WF` (§5) takes `inferProj_always_throws`, which takes none.

## 8. C++ comparison (`~/lean4/src/kernel/type_checker.cpp`) — no new divergence

I read `infer_proj` (:247), `reduce_proj` (:444), `reduce_proj_core` (:420), `is_prop` (:388) and
the two `reduce_proj_core` call sites in `is_def_eq` (:1093), against `Lean4Lean/TypeChecker.lean`'s
`inferProj` (:233), `reduceProjCore` (:351), `reduceProj` (:363) and `lazyDeltaProjReduction`
(:816).  Two differences found; **both are already in `divergences.md`**, which I checked before
writing this:

1. `reduceProjCore` does not take the structure name and so cannot make C++'s
   `mk_val.get_induct() != sname` refusal — `divergences.md` entry 15 (with
   `leanprover/lean4#14631`, `#14632`).  I did not find a counterexample to the standing
   justification there ("comparison and reduction only ever see projections that have been through
   type inference"): a projection can only be reduced when it is the *head* of a term being
   whnf'd, and every entry point infers the enclosing term's type first.
2. `maybePropType := !(← getSortLevel type).isNeverZero` versus C++'s
   `is_prop_type = normalizes_to_zero(...)`: lean4lean checks the field-is-a-proof condition
   whenever the structure's universe is *possibly* zero, C++ only when it *is* — so lean4lean is
   **stricter** on a structure declared at `Sort u` — `divergences.md` entry 14, which even names
   the witness `inductive T.{u} : Sort u where mk : Bool → T`.

**One observation worth adding to the projection stream** (not a divergence, and I did not edit
either file): the **spec side agrees with lean4lean's stricter choice, not with C++'s**.
`TrProj.mk`'s F17 demands `D.isLE = true ∨ (involved fields' levels ≈ .zero)`, and for a block at
`Sort u` neither `LECond` disjunct is available, so `isLE = true` is unavailable and F17 forces the
field-is-a-proof condition — exactly what `inferProj` checks and `infer_proj` does not.  So any
future move to close entry 14 *toward* C++ would require widening F17, and entry 14's own analysis
says C++'s choice is sound only because its level algebra rejects the true inequality
`imax 1 u ≤ u`.  Lean's non-`Prop` structures are unaffected in practice: the elaborator emits
`Sort (max (max 1 u) v)`, whose `isNeverZero` is `true` (checked today).

## 9. The exact edits

**(a) `scripts/users.lean:120` — the instrument fix.**  Given verbatim in §2.  Not mine; not made.

**(b) `Lean4Lean/Experimental/ConeJoin.lean` — one import, so the instruments stop being blind.**
`scripts/sorry-census.lean` and `scripts/dup-names.lean` measure that file's closure, and
`ProjExistClose.lean` is a leaf outside it (its own header comment says "Add every new leaf here").
The edit:

```lean
import Lean4Lean.Verify.Typing.ProjExistClose  -- 2026-09-03: weak'_inv's residual made EXACT (iff) and hole-free; first TrProj inhabitant
```

Measured effect if added: **no census row moves** (the module contains no `sorry`), and the only
user-count change is `weakN_iff` / `forallE_inv_stratified` / `rigidShapeUniqNS` **+1 each**, from
the single deliberately-tainted declaration `VEnv.ConstAppTypeStrengthen.projDataStrengthen`.
Duplicate names: none — each of the 29 new identifiers occurs in no other `.lean` file (checked by
grep over the tree, since `dup-names.lean` cannot see the module until this import lands).

**(c) `Verify/Typing/Lemmas.lean:902` — no edit closes the hole, and I propose none.**  What I
would propose is a docstring paragraph, and it is the following text (the `sorry` and its statement
unchanged):

> **Update 9 (2026-09-03): the residual is now *exact*, and the reduction is free.**
> `Verify/Typing/ProjExistClose.lean` §1 defines `VEnv.ProjDataStrengthen` — this statement's ten
> `TrProj.mk` fields, read at `Γ'` in the hypothesis and at `Γ` in the conclusion, with the block
> and the levels existentially quantified — and proves `VEnv.projStrengthen_iff`, an **`iff`** with
> this statement.  `TrProj.weak'_inv_of_projDataStrengthen` has this theorem's type at cone **717
> with no hole at all**, against 3716/`{forallE_inv_stratified, rigidShapeUniqNS}` for
> `weak'_inv_of_typing_head` and 3698/three for `_of_strengthen`.  So the holes those figures
> carried came from the residual's *shape* — `ConstAppTypeStrengthen` drops the two `HasArgs`
> fields and `VEnv.HasArgs.of_mkApp` re-derives them — not from this lemma's content.  Two
> consequences: `docs/handoff-trproj-weakinv.md` §5.3's "may be jointly stronger than the residual"
> is settled (it is not, at this shape), and ledger **G4 is irrelevant here in both directions** —
> the `→` direction of the `iff` *fails* if the residual fixes `(D,T,C)`, and the `←` direction
> never needs uniqueness.  `VEnv.ConstAppTypeStrengthen.projDataStrengthen` (same file, §3) orders
> the two residuals, so every bound already proved for the old one bounds the new one.  The
> premises are also now known to be satisfiable outright: `trProj_weak'_inv_fires` (§2 there) fires
> all four hypotheses *and* the conclusion at `prjEnv`, a `VEnv.WF` environment declaring
> `structure Prj : Type where fld : Prop`.

**(d) `Verify/TypeChecker/InferType.lean:468` — the one-line close, re-verified but NOT recommended.**

```lean
theorem inferProj.WF
    (he : c.TrExprS e e') (hty : c.TrExprS ety ety') (hasty : c.HasType e' ty') :
    (inferProj st i e ety).WF c s fun ty _ =>
      ∃ e'' ty'', c.TrTyping (.proj st i e) ty e'' ty'' :=
  inferProj_always_throws hty
```

(`he` and `hasty` become unused-variable warnings; prefix them with `_` to keep the file warning
free.)  Compiles, axioms `[propext, Classical.choice, Quot.sound]`.  `docs/handoff-inferproj.md`
§2's argument against making it stands and I did not override it.  **Additionally**, the same
document's justification needs the correction in §5/§6 above: the "`TrProj` has no inhabitants"
clause in the `sorry`'s docstring at `:425` is false as of today, and the same parenthetical should
be corrected wherever it is repeated.  That is a docstring edit in a file I do not own, so I am
stating it and stopping.

## 10. What I would pick up first, and what I could not do

1. **Attack `VEnv.ProjDataStrengthen` directly, not `weak'_inv`.**  It is now *equivalent*, so a
   proof or a counterexample transfers with one lemma application and no holes.  A counterexample
   is the higher-value outcome and the search space is small: by §7 the only context-dependent
   defeq rule is proof irrelevance.
2. **Do not re-derive the `HasArgs` fields.**  Every route that re-derives them pays
   `rigidShapeUniqNS` and `forallE_inv_stratified` for nothing; §3 shows the reduction is free if
   the residual keeps them.  This applies to `TrProj.uniq` and `TrProj.defeqDFC`'s shape too, which
   I did not check — worth one measurement.
3. **`prjEnv` is now a live `VEnv.WF` environment with a structure in it.**  Every projection-side
   statement that has been "witnessed only conditionally on the keystone" (`TrProjWideWitness.lean`,
   `TrProjWideTransportWitness.lean`, `ProjGenTermWitness.lean` — all conditional on
   `VEnv.WF declEnv`) can now be fired *unconditionally* at `prjEnv` instead, in the one-type
   single-field case.  That is the cheapest anti-vacuity upgrade available in this corner and I did
   not take it (out of scope: those files are not mine).
4. **What I could not do, precisely.**  (i) I could not exhibit an *uninhabited* binder over
   `prjEnv` — that needs `prjEnv.Consistent`, which no lemma in the tree provides for any
   environment, so the firing witness stays inside the already-proved inhabited region.  (ii) I did
   not run the Kernel Arena: no implementation file was touched, so goal 1 cannot have moved.
   (iii) I did not test the two `divergences.md` entries of §8 executably (that needs a hand-built
   universe-polymorphic block plus a C++-versus-lean4lean run); both are already recorded with
   witnesses, so I read rather than re-ran them.

## 11. Relay

* **Files changed: two, both mine** — `Lean4Lean/Verify/Typing/ProjExistClose.lean` (new, 29
  declarations, zero warnings) and this document.  `Verify/Typing/Lemmas.lean`,
  `Verify/TypeChecker/InferType.lean`, `divergences.md`, `bugs-found.md`,
  `docs/vacuity-ledger.md`, `Experimental/ConeJoin.lean` and all three frozen files were **not**
  touched.  No git command was run.
* `lake build`: **Build completed successfully (1611 jobs)**, exit 0.
* `scripts/sorry-census.lean`: **TOTAL 13**, with `inferProj.WF [70]` and `TrProj.weak'_inv [90]`
  unchanged.
* Every new declaration is hole-free except the one that is meant not to be
  (`VEnv.ConstAppTypeStrengthen.projDataStrengthen`, §3), and no new `sorry` was written.
* Axiom bar: `after ⊆ before` — the new declarations use only `propext`, `Classical.choice`,
  `Quot.sound` (plus the inherited `sorryAx` in that one), and no `Lean4Lean.*` frozen axiom.
