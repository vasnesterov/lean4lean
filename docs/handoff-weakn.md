# Handoff: strengthening — `IsDefEqU.weakN_iff`

**Target:** the forward (strengthening) direction of `Lean4Lean.VEnv.IsDefEqU.weakN_iff`,
`Theory/Typing/UniqueTyping.lean:174`.  **Still open. Not proved, not refuted.**

Marks, kept strictly separate throughout:
**[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced here;
**[read]** = read off source; **[analysis]** = neither.

Three rounds are recorded.  §A is **this** round (the "refute it" round).  §0–§3 are the
previous round (verdict, reference finding, first positive instance, one killed attack).
§4–§9 are the round before that, and stand unchanged.

---

# §S. The set-model round — the circularity claim is refuted

*(This section is newer than §A.  §A's `A.1` is corrected here; everything else in
§A stands.)*

## S.0 Verdict

**`weakN_iff` is still not decided.**  No counterexample, no proof.
*"No witness is not evidence of truth."*

What this round settles is the **instrument** question the brief asked:

> is there a `PropSplit` — or a soundness route that does not go through
> `PropSplit.Stable` — whose construction does not consume the hole?

**Yes.**  `Lean4Lean/Theory/SetModel/PropSplitUp.lean` — new, **46** source
declarations, all `sorry`-free **[machine-checked]** — builds one.  §A.1's
claim, *"the model route is circular; a `⊬` obtained from it would be
conditional on the hole"*, is **false as stated**: the dependence belongs to
`propSplitOf`'s choice of predicate, not to `PropSplit`, `PropSplit.Stable`, or
`soundAbove`.

The corrected statement: the model's soundness route consumes
`PropUniq`, `PropTypeAgree`, and **substitution descent**
(`InstDescendUp`) — and **not** `TypingStrengthening` / `SortDescend` /
`weakN_iff`.

It does **not** follow that the model can now refute the hole.  A `⊬` from
`sound` is conditional on `InstDescendUp`, which is open.  What changed is that
the condition is no longer *the statement being refuted*, which is the only
thing that made the earlier route viciously circular.

## S.1 The construction, in one line

Replace `propSplitOf`'s predicate

```
IsPropAt ls Γ A := ∃ u, u.WF nv ∧ Γ ⊢ A : .sort u ∧ u.eval ls = 0
```

by its **closure under lifts**

```
IsPropUp ls Γ A := ∃ (l : Lift) Γ' u, Ctx.Lift' l Γ Γ' ∧ u.WF nv ∧
                     Γ' ⊢ A.lift' l : .sort u ∧ u.eval ls = 0
```

("`A` is a proposition *somewhere above* `Γ`"), and likewise for proofs.

Why it works, and it is worth stating because it generalises:

* `prop_sound`/`proof_sound` carry a **typing premise**; `Stable` is quantified
  over **raw syntax**.  Typing transports *forward* along a lift
  (`HasType.weak'`), so the sound-ness fields survive the closure unchanged —
  `PropUniq` / `PropTypeAgree` at the far context is all it takes.
* `Stable`'s **descent** directions become *prepending a lift step*
  (`Ctx.Lift'.comp`, already in the tree) — free.
* `Stable`'s **ascent** directions become a **pushout of two lifts out of a
  common context** — pure syntax, no typing, built here (§1 of the file).

## S.2 What is machine-checked

`Lean4Lean/Theory/SetModel/PropSplitUp.lean`, imports `SetModel/StableAudit`
only.  Nothing imports it yet; it is built through the `Lean4Lean.Theory.*` glob.

| name | statement |
|---|---|
| `Lift.pushOutL`, `.pushOutR`, `Lift.pushOut_comp` | the pushout of two `Lift`s, and that the square commutes |
| `Ctx.Lift'.pushOut` | …and that it is realised by contexts: two lifts out of one context have a join |
| `VEnv.IsPropUp`, `.IsProofUp` | the lift-closed predicates |
| `VEnv.isPropUp_iff`, `.isProofUp_iff` | **`prop_sound`/`proof_sound`, from `PropUniq` / `PropTypeAgree` alone** |
| `VEnv.isPropUp_lift'`, `.isProofUp_lift'`, `.isPropUp_liftN`, `.isProofUp_liftN` | **the two `lift` fields of `Stable`, both directions, no strengthening** |
| `VExpr.lift_r_liftN_one`, `VExpr.lift'_inst_consN` | the `consN` generalisation of `lift'_inst_hi`, via the tree's `Subst` calculus |
| `Ctx.InstN.pushLift'` | **the substitution/lift square**, with the term identity under `j` binders |
| `VEnv.isPropUp_instN_up`, `.isProofUp_instN_up` | **the ascent halves of the two `inst` fields, free** |
| `VEnv.InstDescendUp` | **the residual**: the two *descent* halves, and nothing else |
| `SetModel.propSplitUp` | the `PropSplit`, from `Ordered` + `PropUniq` + `PropTypeAgree` |
| `SetModel.propSplitUp_stable` | **the headline**: `Stable`, from `Ordered` + `InstDescendUp` |
| `SetModel.exists_stable_propSplitUp`, `…_of_agree` | the existence forms, the second matching `StableAudit.exists_stable_propSplit` hypothesis-for-hypothesis |
| `SetModel.isPropAt_le_isPropUp` | `propSplitOf`'s predicate refines the new one (the empty lift) |
| `SetModel.isPropUp_iff_isPropAt`, `.isProofUp_iff_isProofAt` | **…and the two agree on every well-typed input** |
| `VEnv.propUpCollapse_iff`, `.proofUpCollapse_iff` | **the exact price**: "`IsPropUp` is the canonical predicate" **↔** `PropDescend.sort_lift` (resp. `proof_lift`) |
| `SetModel.sort_lift_of_isPropUp_collapse` | the same as a one-way negative control, with no auxiliaries |
| `VEnv.instDescendUp_of_propDescend` | **no regression**: `PropDescend` still discharges the residual |
| `SetModel.allProp_hasType`, `.isPropUp_falseProp`, `.not_isPropUp_sort` | non-vacuity, both branches (`∀ p : Prop, p` is a proposition; `Prop` is not) |

Axioms **[measured]**: no `sorryAx` anywhere.  `propUpCollapse_iff`,
`proofUpCollapse_iff`, `instDescendUp_of_propDescend`,
`sort_lift_of_isPropUp_collapse` are `[propext]`; `lift'_inst_consN`,
`Ctx.InstN.pushLift'`, `isPropUp_iff`, `isProofUp_iff`, `isPropUp_instN_up`,
`isProofUp_instN_up`, `isPropUp_falseProp`, `not_isPropUp_sort` are
`[propext, Quot.sound]`; the rest — including `propSplitUp_stable` — are
`[propext, Classical.choice, Quot.sound]` (the choice is `Classical.propDecidable`
for `decProp`/`decProof`, exactly as in `propSplitOf`).

## S.3 The negative control, and why §3 is not the trivial direction backwards

`IsPropUp` is **implied by** the canonical predicate, so the reduction would be
empty if the converse were free.  It is not:
`propUpCollapse_iff` **[machine-checked]** proves

> `∀ ls Γ A, IsPropUp ls Γ A → ∃ u, Γ ⊢ A : .sort u ∧ u.eval ls = 0`
> **↔** `PropDescend.sort_lift`

— i.e. collapsing the new predicate back to the old one is *exactly* the field
`StableAudit.sort_lift_of_strengthening` derives from the hole.  So the trade is
exact and in the right direction: the strengthening statement has been moved out
of a hypothesis of soundness and into a claim nobody needs.

`isPropUp_iff_isPropAt` **[machine-checked]** localises the difference: the two
predicates agree at every `A` that has a sort at `Γ`.  They can differ only on
syntax with no sort at `Γ` — which is precisely the region `Stable` quantifies
over (raw syntax) and `prop_sound` does not (typing premise).  **That asymmetry
is the whole source of the freedom, and it is a general observation about the
`PropSplit` interface, not about this predicate.**

## S.4 What is left, and why it is a different statement

`InstDescendUp` — two fields:

```
Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → Γ₀ ⊢ e₀ : A₀ →
  IsPropUp  ls Γ (B.inst e₀ k) → IsPropUp  ls Γ₁ B
Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → Γ₀ ⊢ e₀ : A₀ →
  IsProofUp ls Γ (e.inst e₀ k) → IsProofUp ls Γ₁ e
```

These are `PropDescend.sort_inst` / `proof_inst` transported to the lift-closed
predicate — *substitution* descent, not context descent.  `StableAudit.lean`'s
own note records that its candidate refutation of `sort_inst` is blocked on
`IsDefEqU.sort_forallE_inv` (`Theory/Typing/Injectivity.lean`), **not** on
strengthening [read].  A structural scan confirms the separation is real: across
the whole `SetModel/` cone, **exactly 3** declaration/target pairs mention any
strengthening statement, and all 3 are the two `StableAudit` lemmas this file
makes unnecessary **[measured; script at
`<scratchpad>/setmodel-circ/scan.lean`]**:

```
StableAudit :: proof_lift_of_strengthening -> VEnv.TypingStrengthening
StableAudit :: sort_lift_of_strengthening  -> VEnv.TypingStrengthening
StableAudit :: sort_lift_of_strengthening  -> VEnv.SortDescend
```

(direct references in a declaration's type or value; targets scanned:
`TypingStrengthening`, `SortDescend`, `IsDefEqU.weakN_iff`,
`StrengtheningTarget`, `Strengthening`, `PiDescend`, `sorryAx`.)

## S.5 Why no further closure removes the residual **[analysis]**

The natural next move — also close the predicate under *substitution* moves, so
that the `inst` descent becomes "prepend a step" too — **does not work**, and the
reason is sharp enough to record so nobody re-derives it.

Write the closure as reachability along typing-preserving moves.  Then, for every
move: **descent** (P at the target ⟹ P at the source) is free, and **ascent**
needs the move to commute past the moves already in the closure.

* lift/lift and lift/inst commute — that is §1 and §4 of the file, both
  machine-checked.
* **inst/inst does not.**  Two substitutions of the *same* variable by *different*
  terms have no common continuation: from `(Γ₁, B)` with `Γ₁ = [Prop]`,
  `B = .bvar 0`, substituting `p₁` and `p₂` lands on `([], p₁)` and `([], p₂)`,
  and both terms are closed, so every further move fixes them.

So closing under `inst` buys the `inst` descent and loses the `inst` ascent; there
is no closure making all four free while `prop_sound` survives (`prop_sound`
forces every move to be typing-preserving *forward*, which is what makes descent
the free direction).  The lift-only closure is the optimum of this family.

The concrete candidate counterexample to the `inst` ascent is
`StableAudit.lean`'s own witness shape (`B = (bvar 0) falseProp falseProp`,
`e₀ = fun p => p` versus `e₀ = fun p => falseProp`), and **it is blocked on the
same `sort_forallE_inv`** — so even the failure of `inst`-closure cannot be
machine-checked here.  Everything on the substitution side of this file's story
runs into that one statement.

## S.6 Measurements and corrections

* `scripts/sorry-census.lean`: **TOTAL 19** at the end of the round
  **[measured]** — unchanged, as it must be.
* **Correction to §A.7 and to the briefs**: `IsDefEqU.weakN_iff` now reports
  **124** transitive users, not 111 **[measured, this round]**.
* `scripts/dup-names.lean`, default run: **no duplicates** **[measured]**.  A
  dedicated run adding `Theory.SetModel.PropSplitUp` to that closure: **no
  duplicates** **[measured]** — the new file introduces none, and unlike
  `StableAudit` it *does* import into the joined cone.
* `lake build Lean4Lean.Theory.SetModel.PropSplitUp`: green **[measured]**.
* **`docs/model-interface.md`'s standing label is now stale in a second way.**
  `StableAudit.lean` corrected it from "`PropTypeAgree` alone" to
  "`PropTypeAgree ∧ PropDescend`".  With `propSplitUp` the honest label is
  **`PropTypeAgree ∧ PropUniq ∧ InstDescendUp`**, and no part of it is a
  strengthening statement.  Not edited here (not this stream's file).

## S.7 What the next attempt should do

1. **`InstDescendUp` is the whole model-side residual now.**  Price it the way
   `PropDescend` was priced.  Its two fields are substitution descent; the
   `StableAudit` note says refuting `sort_inst` needs `sort_forallE_inv`.  So the
   first question is whether `sort_forallE_inv` is reachable — it is one of the
   three `sorryAx`-carrying non-derivability statements §A.2 counted.
2. **Do not re-derive the pushout or the substitution square.**  Both are in
   `PropSplitUp.lean`, `sorry`-free, and are pure syntax; they will be reusable
   for anything else that needs to move a lift past a lift or a substitution in
   this tree.
3. **The `Stable`-vs-`prop_sound` asymmetry generalises.**  Any interface field
   quantified over raw syntax next to a field guarded by typing can be traded the
   same way: weaken the predicate on junk until the raw-syntax field becomes a
   syntactic commutation.  This is the second time in this tree that a "junk
   input" gap was the *resource* rather than the defect (the first was
   `LevelAssignUnsat`, where it was the defect).
4. On the hole itself, §A.6 still stands: attack `StrengtheningCanonUninhab`, and
   note that a model-side `⊬` is now conditional on `InstDescendUp` rather than
   on the hole — which makes it a *usable* instrument for the first time, if
   `InstDescendUp` can be discharged.

---

# §A. The refutation round

## A.0 Verdict

**Not refuted, and the brief's route to a refutation is blocked — by a fact already in the
tree.**  No counterexample was found and none was expected to be findable by the assigned
route.  *"No witness is not evidence of truth."*  What this round adds is one machine-checked
**narrowing** of the statement and two **corrections**.

## A.1 Correction 1 — the set model cannot refute this, *as the tree stands*. It is circular.

The brief said: *"a set model is exactly the instrument for that … Right tool from the
refutation side."*  That is wrong in this tree, and the proof that it is wrong was committed
the night before, in a file this stream owns.

`Theory/SetModel/StableAudit.lean` **[machine-checked, `sorry`-free]**:

* `soundAbove` / `sound` (`SetModel/SoundInduction.lean`) — the only route from a derivation
  to a set-theoretic fact — take a `PropSplit` **together with `PropSplit.Stable`** [read].
* `propSplitOf` is the tree's only `PropSplit` construction, and
  `propSplitOf_stable_iff` proves `Stable ↔ PropDescend` for it — an *equivalence*, so this
  is not a proof artefact **[machine-checked]**.
* `sort_lift_of_strengthening` and `proof_lift_of_strengthening`
  (`StableAudit.lean:260,276`) derive `PropDescend`'s two `lift` fields **from**
  `TypingStrengthening` + `SortDescend` (+ `PropUniq`/`PropTypeAgree`) — i.e. **from the
  hole** **[machine-checked]**.

So the model's soundness theorem is conditional on (a form of) the statement to be refuted.
A `Γ ⊬ e₁ ≡ e₂` obtained from it would be conditional on the hole, and a conditional
`⊬` cannot refute its own condition.  **The model route is circular here.**

It is not circular *in principle*: `StableAudit.lean`'s own table names the other route,
`LevelAssign.toPropSplit`, whose `Stable` is a syntactic commutation (`Commutes`,
`toPropSplit_stable`, three lines) — but that route pays in `sort_inv` + `SortUniq`, i.e.
unique typing, which is `sorryAx` and has no instance.  **Both routes into the model are
blocked by open statements.**  Anyone told "use the model" should be told this first.

## A.2 Correction 2 — the tree has no context-sensitive `⊬` instrument, and cannot have one cheaply

A refutation needs `Γ ⊬ e₁ ≡ e₂` at the **smaller** context while `Γ' ⊢ e₁ᵏ ≡ e₂ᵏ` at the
larger.  A structural scan of both cones for statements whose conclusion is `False` or
`¬ …` over `IsDefEq`/`IsDefEqU`/`HasType`/`IsType`/`VExpr.WF` finds **31**
**[measured; script kept at `<scratchpad>/weakn-refute/negscan.lean`]**.  Reading them:

* three carry `sorryAx` (`IsDefEqU.sort_forallE_inv`, `const_sort_inv`, `const_forallE_inv`);
* the substantive unconditional ones — `propLoopEnv2_A_ne_B`, `propLoopEnv2_A_ne_sort`,
  `propLoopEnv2_A_ne_forallE`, `barEnv_bar_ne_ctorApp`, `isType_lam_false`,
  `constApp_sort_false`, `constApp_forallE_false`, `const_sort_inv_of_patWF`,
  `const_forallE_inv_of_patWF` — are all **head-shape disjointness** facts (a const
  application is not a sort / not a Π; a λ is not a type; two distinct constants are not
  convertible);
* the rest (`KEta`, `KCanonical`, `HeadRedStuck`, `DescendRefute`) are non-applicability of a
  *statement* at a witness, not non-derivability of a conversion.

**Head-shape predicates are lift-stable**: `(.sort u).liftN n k = .sort u`,
`(.const c ls).liftN n k = .const c ls`, and `liftN` preserves the `app`/`lam`/`forallE`
head.  So every one of these instruments, applied at `Γ`, applies verbatim at `Γ'` to the
lifted terms — it kills **both** sides of the `iff` and separates nothing.  **[analysis, on
lift-stability which is immediate from `VExpr.liftN`'s definition; measured, on the census]**

That is the sharp reason the search fails: an instrument that could refute strengthening
would have to distinguish two contexts, and *being able to distinguish two contexts is the
negation of the theorem*.  Every mechanism is a fixed point of itself (§1, previous round,
now with a second confirmation).

## A.3 What was actually delivered: the context class collapses to one closed entry per level

`Theory/Typing/StrengthenCanon.lean` — **new, 26 source declarations, all `sorry`-free**
**[machine-checked]**.

`Strengthen.lean` §11 reduces the hole to stripping **one** entry (`Strengthening1`); §12
narrows to entries that are **uninhabited**.  This file narrows the *entry itself*:

```lean
def bigFalse (u : VLevel) : VExpr := .forallE (.sort u) (.bvar 0)   -- ∀ (α : Sort u), α
```

| name | statement |
|---|---|
| `Ctx.Ins X k Γ Γ' Γ₀` | a `Ctx.LiftN 1 k` that remembers **which** entry was inserted and **where it is typed** |
| `Ctx.Ins.liftN`, `.instN`, `Ctx.LiftN.exists_ins` | it is a `LiftN`, it is invertible by substitution, and every `LiftN 1 k` is one |
| `Ctx.Ins.entry_typed`, `.onCtx` | the entry is a type in its own prefix; inserting a type preserves `OnCtx` |
| `Ctx.Ins.canon` | **the commuting square**: an insertion of `X` at depth `k` factors as "insert `Y` at `k`, then insert `X.lift` at `k`" |
| `bigFalse_liftN`, `bigFalse_closed` | the canonical entry is **closed** — it no longer depends on the prefix |
| `bigFalse_zero`, `bigFalse_param_zero` | `bigFalse .zero = falseProp`, `bigFalse (.param 0) = univType` (both `rfl`) |
| `bigFalse_isType` | it is a type, in every environment and context |
| `hasType_bigFalse_app` | **why it is the strongest entry at level `u`**: `x : bigFalse u` at the head of the context gives `Γ ⊢ .app (.bvar 0) A.lift : A.lift` for every `A : Sort u` below it |
| `canon_swap` | **the swap**, extracted: an arbitrary one-entry stripping becomes a `bigFalse u` stripping over the *same* `Γ`, `e1`, `e2`, `k` |
| `StrengtheningCanon` | the target restricted to entries `bigFalse u` |
| `StrengtheningCanon.strengthening1` | **the reduction** |
| `StrengtheningCanon.iff_strengthening1`, `.iff_target` | it loses nothing: `StrengtheningCanon ↔ Strengthening1 ↔ StrengtheningTarget` |
| `StrengtheningCanonUninhab` | the target restricted to entries `bigFalse u` that are **also uninhabited** — §12's restriction and this one **compose** |
| `StrengtheningCanonUninhab.strengthening1`, `.iff_strengthening1` | and the composite still loses nothing |
| `strengtheningCanon_premises`, `ins_sort_not_bigFalse` | non-vacuity, and the **negative control** |

**The argument, in three moves, none of which assumes the hole.**  Given an arbitrary
one-entry stripping with entry `A : Sort u`:

1. **weaken** — insert `bigFalse u` immediately *below* the `A` entry (`Ctx.Ins.canon`
   builds the square; `IsDefEqU.weakN` does the work);
2. **substitute** — `A` is now inhabited by `.app (.bvar 0) A`, so
   `IsDefEqU.strengthen_of_instN` (`Strengthen.lean` §1, the **proved** half) strips it;
3. what remains is the same conversion over the context with `bigFalse u` in place of `A`.

Axioms **[measured]**: `StrengtheningCanon.strengthening1`, `.iff_strengthening1`,
`canon_swap`, `hasType_bigFalse_app`, `Ctx.Ins.canon` are `[propext, Quot.sound]`;
`.iff_target` and the two `StrengtheningCanonUninhab` results are
`[propext, Classical.choice, Quot.sound]` (the choice is the classical case split on
inhabitedness, plus what `Strengthen.lean`'s closure already carries);
`Strengthening1.canon`, `Strengthening1.canonUninhab`, `bigFalse_isType`, `Ctx.Ins.instN`,
`Ctx.LiftN.exists_ins`, `strengtheningCanon_premises` are `[propext]`;
`ins_sort_not_bigFalse` depends on **no** axioms.

**The crispest form the hole now has** (`StrengtheningCanonUninhab.iff_strengthening1`
chained with `Strengthening1.iff_target`): *adding the hypothesis `∀ (α : Sort u), α` to a
well-formed context, at a level and position where it has no inhabitant, is conservative for
conversion.*  One closed hypothesis per level, and nothing else.

**Why it does not collapse to a single level.**  `x : bigFalse u` inhabits `bigFalse v` only
when `u ≈ .imax (.succ v) v`, so level `w+2`'s entry implies level `w+1`'s and nothing
implies level `0`'s but itself.  A single entry covering all levels would have to quantify
over `VLevel`, which is not a term of `VExpr` — the same obstruction the previous round hit
(`§2` below: "a universe parameter is required"). **[analysis]**

**What it buys, stated exactly.**  Before: the stripped entry was an arbitrary type in an
arbitrary prefix.  After: it is **one closed term per level**, `∀ (α : Sort u), α`, whose
`u = .zero` member is `falseProp`.  Both sides gain:

* a proof attempt handles one context shape per level, and the entry is closed, so the
  induction no longer has to track how the entry depends on the context below it;
* a refutation attempt has one concrete target — `∀ (α : Sort u), α :: Γ` — instead of an
  arbitrary well-formed context with an arbitrary uninhabited entry.

**The negative control** (working rule 5): `Strengthening1 → StrengtheningCanon` is the
trivial direction, so the reduction has content only if the canonical entries are a *proper*
subclass.  `ins_sort_not_bigFalse` **[machine-checked]** exhibits a well-formed one-entry
stripping whose entry (`.sort .zero`) is `bigFalse u` for no `u`.  And the reduction cannot
be vacuous, because `iff_target` makes it *equivalent* to the hole: if it were provable the
hole would be closed.

## A.4 A trap this round hit, and a live collision it found

* **Auto-bound implicit, again.**  `theorem bigFalse_zero : bigFalse .zero = falseProp := rfl`
  compiled its `falseProp` as a fresh implicit variable — `Theory.Consistency` was not in the
  import closure — and failed with a *unification* error, not an "unknown identifier".  The
  fix is the import plus the qualified name.  This is shape 5 of `ORCHESTRATOR.md`'s list,
  met in the wild in a one-line `rfl` **[measured]**.

* **`Lean4Lean.VEnv.PropTypeAgree` is declared twice, with two different statements, and the
  pair is live — and one consequence is that `Theory/SetModel/` is outside the reach of both
  standing measuring scripts** **[measured]**:
  `Theory/Typing/UniqueTypingN.lean:620` (`env U n`, indexed, about `HasTypeN`) and
  `Theory/SetModel/PropSplitAudit.lean:119` (`env nv`, about level evaluations).
  Importing `UniqueTypingN` and `StableAudit` in one file fails with
  *"environment already contains 'Lean4Lean.VEnv.PropTypeAgree'"*.
  **The default `scripts/dup-names.lean` run does not catch it**: `Experimental.ConeJoin`'s
  closure contains `UniqueTypingN`'s version, so **no `Theory/SetModel/` module can be
  imported into the joined cone at all** — neither `scripts/dup-names.lean` nor
  `scripts/sorry-census.lean` sees `SetModel/`.  (A separate scan over the `SetModel/` cone
  finds **8** declarations containing `sorryAx`, all of them *inherited* from
  `Theory/Typing/Injectivity.lean`, `UniqueTyping.lean` and `Inductive/Decl.lean`; `SetModel/`
  declares **none** of its own, so the census's TOTAL 19 is not understated **[measured]**.)
  Consequence:
  every claim that "the model's residual syntactic import is `PropTypeAgree`" and every claim
  about `PropTypeAgree` on the `Theory/Typing/` side are claims about **different
  statements**, and no proof can span them.  Not fixed here: the `Theory/Typing/` occurrences
  live in `PropConv.lean`, `AppCase.lean`, `RegPiSat.lean`, `ShapeSpine.lean`, which this
  stream does not own.  The natural rename is `UniqueTypingN`'s to `PropTypeAgreeN`, matching
  that file's own `IsPropN`/`HasTypeN`/`SortInvN` convention (18 + 16 + 7 + 5 + 1 references).

## A.5 Refutation shapes tried this round and why each died

| shape | died at |
|---|---|
| `proofIrrel` at a closed proposition | its three premises are about the endpoints themselves; if the endpoints and the proposition are `Γ`-free and typeable downstairs, the rule fires **downstairs too**. Separation zero. **[analysis]** |
| `proofIrrel` at a proposition mentioning the stripped variable | needs `Γ`-free `h, h'` typed at that `p` upstairs; their types downstairs must then convert to `p` upstairs — a *type-level* conversion available upstairs only, which **is** the hole. **[analysis]** |
| `beta`/`eta` with a `Γ`-free redex | the endpoints are determined by the rule; the premises are typings of `Γ`-free terms, i.e. `TypingStrengthening`. Fixed point. **[analysis]** |
| junk `Δ` at general `k` (entries below the insertion point) | `Ctx.LiftN` forces `Δ' = Δ` lifted, so "Δ is a type upstairs, junk downstairs" is `SortDescend` — part of the hole. **[analysis; confirms the previous round]** |
| model-theoretic `⊬` at the smaller context | **circular** — §A.1. **[machine-checked, on the circularity]** |
| any existing `⊬` instrument | all lift-stable — §A.2. **[measured]** |
| `n = 0`, `U = 0`, `A = .sort .zero` degeneracies | `n = 0` makes `Γ' = Γ`; `.sort .zero` is *inhabited* (by any proposition), so §1's substitution closes it. **[analysis]** |

**The one-line summary of why refutation is hard here, and it is not a soft claim.**
`extra` is context-free (previous round, `[read]`); `bvar` is the only context-sensitive
rule; and every route from `bvar` to a conversion between `Γ`-free terms passes through a
*type-level* conversion between `Γ`-free types that holds upstairs and not downstairs —
which is the statement itself, at the type level.  A counterexample is therefore
**self-supporting**: it cannot be built bottom-up out of smaller counterexamples, because
every mechanism that would produce it consumes a smaller instance of itself.

## A.6 What the next attempt should do

1. **Do not use the set model** until `PropSplit.Stable` is obtained by a route that is not
   `PropDescend` — §A.1 names the only candidate and its price.
2. **Attack `StrengtheningCanonUninhab`, not `Strengthening1`.**  It is equivalent
   (`StrengtheningCanonUninhab.iff_strengthening1`, then `Strengthening1.iff_target`) and the
   context is now one closed entry per level, assumed uninhabited.  Concretely: is
   `∀ (α : Sort u), α :: Γ ⊢ e₁.lift ≡ e₂.lift → Γ ⊢ e₁ ≡ e₂`, when the entry has no
   inhabitant in `Γ`?
3. **The `noUnsafe` question is open and cheap to price, and nobody has priced it for *this*
   statement.**  `LogRelRowZero.headStep_not_wf` blocks the logical-relation route only at
   full `VEnv.WF` generality, and its witness is one `.unsafeDef` step
   (`CycleConv.loopEnv2_wf_noUnsafe` shows the *conversion* relation survives without it).
   `Verify/SafeFragment.lean` §2 has already done this analysis **for `Injectivity.lean`** —
   `VContext.EwfNoUnsafe` delivers `noUnsafe` at `c.safety = .safe`, with the proviso that
   the consumers must be reached only at `.safe`, which is a restructuring nobody has
   attempted.  The same question for `weakN_iff`'s ~~111~~ **312** (re-measured 2026-09-02)
   transitive users has **not** been asked.  **[read, on SafeFragment; not measured for `weakN_iff`]**
4. `PiDescend` is still the cheaper sub-target, and is now known to need *conversion*
   strengthening too, not just typing strengthening: its second conjunct asks for
   `Γ ⊢ a : A₀` with `A₀` **f's** domain, and reconciling `a`'s own downstairs type with
   `A₀` is `TransStrengthening`. **[analysis]**

## A.6b Files

* `Lean4Lean/Theory/Typing/StrengthenCanon.lean` — **new this round**, 26 source
  declarations, all `sorry`-free.  Imports `StrengthenVerdict` (for `onCtx_levelWF` and
  `univType`) and `Theory/Consistency` (for `falseProp`).  Nothing imports it yet; it is
  built by `lake build` through the `Lean4Lean.Theory.*` glob.
* `Lean4Lean/Theory/SetModel/StableAudit.lean` — **read, not modified**.  §A.1's circularity
  is entirely that file's own already-committed content.
* Everything else in this stream's file set is unchanged.

## A.7 Measurements this round

* `scripts/sorry-census.lean`: **TOTAL 19** at the start **[measured]**; `weakN_iff` has
  **111** transitive users **[measured]**.  Nothing was closed, so the end count must also be
  19 — any other number is a regression to investigate.
* `scripts/sorry-census.lean` at the **end**: **TOTAL 19** **[measured]** — unchanged, as it
  must be, since nothing was closed.
* `scripts/dup-names.lean`, default run at the start **and** at the end: **no duplicates**
  **[measured]**.  A dedicated run adding `StrengthenCanon` + `StrengthenVerdict` + `ConstVar`
  to that closure: **no duplicates** **[measured]** — the new file introduces none.  Adding
  `StableAudit` to the same run *fails to import*, which is how the pre-existing
  `PropTypeAgree` collision of §A.4 was found.
* The 31 non-derivability statements of §A.2 **[measured]**.

---

# §B. Previous round (the "decide it" round)

## 0. The verdict

**Not decided.**  The statement was neither proved nor refuted, and no witness was found.
*"No witness is not evidence of truth."*  What this round adds is three things that were not
in the tree, all machine-checked, plus one finding from outside it.

0. **The reference has this statement, and its proof of it does not go through.**
   `~/lean-type-theory/typesys.tex:88–89` — `thm:weak` parts (3) and (4) — are exactly
   strengthening:

   > (3) If `Γ,Δ ⊢ e : α` and `FV(e) ⊆ Γ` then `Γ ⊢ e : α`.
   > (4) If `Γ,Δ ⊢ e ≡ e'` and `FV(e) ∪ FV(e') ⊆ Γ` then `Γ ⊢ e ≡ e'`.

   `typesys.tex:95` proves them "by mutual induction on the first hypothesis".  **That
   induction cannot work**: the reference's conversion judgment carries an explicit
   transitivity rule with an arbitrary middle term (`axioms.tex:33`,
   `Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₃ → Γ ⊢ e₁ ≡ e₃`), and the hypothesis constrains `FV(e₁)` and
   `FV(e₃)` only, so neither induction hypothesis applies.  `VEnv.Strengthening.iff_trans`
   **[machine-checked, `[propext]` only]** is the sharp form: the `trans` case **is** the
   statement.  **[read, on the reference; machine-checked, on the tree]**

   Scope, stated in registers: the reference's (3)/(4) strip a **suffix** (de Bruijn `k = 0`);
   `weakN_iff` also strips an entry from the **middle** (general `k`).  The gap is in the
   proof as written, not a counterexample — this is a **proof gap in the published
   reference**, not a refutation of it, and there is nothing to file.  It does settle one
   thing: the hole is not an artefact of this formalisation.

1. **The hole has a positive instance now, and it is the first one.**
   `Theory/Typing/StrengthenVerdict.lean` exhibits a `VEnv.WF` environment at which
   `StrengtheningTarget` — hence `AxiomConservativityUninhabWF`, hence `weakN_iff`'s forward
   direction — **is a theorem**, for every `U` (`exists_univInhabEnv`,
   `exists_univInhabEnv_axiomConservativity`, `[propext, Classical.choice, Quot.sound]`).
   `Strengthen.lean` §12's `strengtheningTarget_of_allInhabited` had **no** environment
   instance anywhere in the tree before this [measured: `grep`, its only occurrences were its
   own statement and one docstring].
2. **A correction to a claim that has been travelling in the briefs.**  The claim is
   *"inconsistent environments make the problem easier — a closed `f : ∀ p, p` inhabits every
   `Prop` entry"*.  The parenthesis does not reach the conclusion.  `∀ p : Prop, p` applies
   only to entries at `.sort .zero`; `Strengthening1Uninhab` quantifies over entries at every
   sort, and `Theory/` has no `False.rec` to lift one **[analysis]**.  So
   `MutualDefUnsound.selfRefDV` and `LogRelRowZero.loopEnv`, both at `uvars = 0` and
   `falseProp`, do **not** discharge the target.  The constant that does is
   `∀ (α : Sort u), α`, which needs a universe parameter — `univDV` in the new file.
3. **The cheapest counterexample shape is dead, at its own witness.**  See §2.

---

## 1. Where the obstruction actually sits, after this round

Every mechanism traced this round bottoms out in **one** place, and it is not a new place:

* `proofIrrel` is the only rule whose side condition asks for a judgement at a **fixed**
  sort (`Γ ⊢ p : .sort .zero`).  It is therefore the only rule at which "what is a
  proposition" can differ between `Γ` and a context extending it.  But for it to relate two
  lifted terms upstairs and not downstairs, those terms must fail to be typeable at a common
  proposition downstairs — which is *typing* strengthening, i.e. `PiDescend`/`SortDescend`,
  i.e. the hole again.  **[analysis]**
* `beta` and `eta` can link a `Γ`-free term to one mentioning the stripped variable, but
  only through a discarded-argument position; making that link *essential* again requires a
  conversion between a `Γ`-free type and a variable-containing one.  **[analysis]**
* `extra` cannot separate the two contexts **at all**: every `VDefEq` a `VEnv.WF`
  environment carries is typed in the *empty* context (`VDefVal.WF`, `VDecl.WF.def`,
  `.unsafeDef`, ι-rules built by `VExpr.mkLams`, `quotDefEq`), so the rule fires in every
  context identically.  **[read]**
* `bvar` is the only genuinely context-sensitive rule, and the terms in question do not
  mention the stripped variable.

So a counterexample must be a *minimal* failure of conversion strengthening whose every
sub-failure is a smaller failure of conversion strengthening — which is the shape of an
induction that works for every rule except `trans`.  That is `Strengthening.iff_trans`,
restated.  **[analysis]**

**The corollary for search strategy, and it corrects the brief.**  The brief says *"No model
argument can reach it: soundness over an uninhabited context is vacuous."*  That is right
about **proving** the target and wrong as a blanket statement.  A refutation needs the
*negative* half — `Γ ⊬ e₁ ≡ e₂` at the **smaller** context, which is not vacuous — and a set
model is exactly the instrument for that.  The vacuity blocks the affirmative direction only.
`Theory/SetModel/` is therefore the right tool for anyone attacking this from the refutation
side, and the wrong one from the proof side.  **[analysis; correction to the brief]**

---

## 2. The attack that was built and killed

**The shape.**  Take `Γ' = .sort .zero :: Γ`.  Then `.bvar 0` is a *variable proposition*
upstairs and is not a proposition downstairs, so `proofIrrel` fires upstairs at a `p` that
downstairs is not even typeable.  To use it one needs two `Γ`-free terms of type `.bvar 0`,
and the cheapest supply is a constant whose declared type is `.bvar 0`.  Such a constant is
impossible in an `Ordered` environment, so the witness could only ever have refuted
`StrengtheningTarget` as an **unqualified** predicate (it is stated without `VEnv.WF env`;
the equivalences supply that separately) — which is still worth having, since it would show
the `WF` hypothesis load-bearing, the way `sortUniq_badEnv` does for `SortUniq`.

**Why it is dead.**  `constOpenType_hasType_any` **[machine-checked, `[propext]`]**: a
constant `c` with `env.constants c = some ⟨0, .bvar 0⟩` satisfies `Γ ⊢ c : e` for **every**
`e` that is inhabited in `Γ`, by one `beta` step —
`(fun (_ : A) => c) e : (.bvar 0).inst e = e`.  So both candidates land at the closed
proposition `∀ (p : Prop), p` **downstairs**, where `proofIrrel` equates them just as well:
`constOpenType_collapse` **[machine-checked]** derives `[] ⊢ c₁ ≡ c₂` outright.  The
separation is zero.  (`allProp_isProp` is the small lemma that `∀ (p : Prop), p` really is a
proposition — `.imax (.succ .zero) .zero ≈ .zero`, closed by `defeqDF`+`sortDF`.)

**What that tells the next attempt.**  The hypothesis that kills it is `Ordered`'s *declared
types are closed*.  Any bad-environment refutation must therefore separate the two contexts
without an open constant type — and `extra` cannot (§1), so `bvar` and `proofIrrel` are the
whole budget.

---

## 3. The positive instance, and exactly how little it proves

`Theory/Typing/StrengthenVerdict.lean`, 14 declarations, all `sorry`-free, all
`[propext(, Classical.choice), Quot.sound]` **[measured]**.

| name | statement |
|---|---|
| `univType`, `univCV`, `univDV` | `univInhab : ∀ (α : Sort u), α := univInhab`, one universe parameter |
| `univType_isType` | its type is a type over any environment |
| `hasType_univInhab_app` | **the universal inhabitant**: `Γ ⊢ .app (.const univInhab [u]) A : A` whenever `Γ ⊢ A : .sort u` |
| `onCtx_levelWF` | a well-formed context is level-well-formed (needed to get `u.WF U`) |
| `strengtheningTarget_of_univInhab` | **any `VEnv.WF` environment declaring `univInhab` satisfies the target**, at every `U` |
| `univInhabDecl_wf` | the `VDecl.WF.unsafeDef` step is well formed wherever the name is free |
| `exists_univInhabEnv` | **the environment exists and is `VEnv.WF`** |
| `exists_univInhabEnv_axiomConservativity` | the same through `ConstVar.lean`'s equivalence |
| `univInhab_no_uninhabited_entry` | **the scope statement** (below) |
| `constOpenType_hasType_any`, `allProp_isProp`, `constOpenType_collapse` | §2 |

**The scope statement is the important half.**  `univInhab_no_uninhabited_entry`
**[machine-checked]** says that at such an environment `Strengthening1Uninhab`'s
uninhabitedness hypothesis is satisfiable at **no** well-formed context.  So the positive
instance lives **entirely inside the case `Strengthen.lean` §1 already closes**, and tests
nothing whatever about the obstruction.  It is a satisfiability witness — the target is not
contradictory at a `VEnv.WF` environment — and nothing more.  Recording it that way is the
point: working rule 4 asks for the obligation to be fired at a witness, and this is the
honest report of what the only available witness covers.

The environment is inconsistent (it inhabits every type), which is the reason it is easy —
and it is the *first* environment for which "inconsistent makes it easier" is more than an
assertion.

---

# §C. Earlier rounds

## 4. The chain of equivalences (previous round, re-verified here)

The hole is **equivalent** to each of these, all `sorry`-free
**[measured, `#print axioms` re-run this round]**:

* `TransStrengthening` — its own `trans` case (`Strengthening.iff_trans`,
  `StrengtheningTarget.iff_trans`);
* `Strengthening1` — the same at a single stripped entry (`Strengthening1.iff_target`);
* `Strengthening1Uninhab` — the same at a single **uninhabited** entry
  (`Strengthening1Uninhab.iff_target`);
* `AxiomConservativityWF` — conservativity of adding one axiom, over a well-formed context
  (`axiomConservativityWF_iff_target`);
* `AxiomConservativityUninhabWF` — the same for an axiom with **no inhabitant**
  (`axiomConservativityUninhabWF_iff_target`), and
  `axiomConservativityWF_iff_uninhabWF`: restricting to uninhabited axioms loses nothing.

It is **implied by** (one direction only, still the only one-directional link left):

* `AxiomConservativity` / `AxiomConservativityUninhab` (`StrengthenAxiom.lean`), which
  quantify over an **arbitrary** context.  The converse fails by exactly one hypothesis:
  `StrengtheningTarget`'s only context hypothesis is `OnCtx Γ'`, and `Γ ++ Ts` cannot be well
  formed unless `Γ` is.  This costs nothing — every use has `OnCtx Γ` in scope.  **[read +
  machine-checked]**

Its *reflexive instance* is equivalent to `PiDescend` alone
(`TypingStrengthening.iff_piDescend`; `sorryAx` via `forallE_inv`).

---

## 5. `ConstVar.lean` — the previous round's transport (unchanged)

666 lines, 79 declarations, **0** with `sorryAx` in their transitive closure, **0** whose
cone contains `weakN_iff` [measured, previous round].  The headline is
`StrengtheningTarget.axiomConservativityWF`: given the target, an axiom added to `env` is
conservative — translate every occurrence of the new constant into a context variable, one
per `≈`-class of level list the derivation uses, and strip those variables again with the
target.

The three decisions that made it small, worth not re-deriving:

* **Quantify over covers, don't extract.**  `cvarMain`'s conclusion is
  `∃ L₂, LWF U L₂ ∧ ∀ L', LWF U L' → LCov L' L₂ → <derivation at L'>`.  Extraction of a
  derivation's level lists is **not expressible** (a derivation is a `Prop`) and **not
  needed**.  Because every term in the conclusion is computed at `L'`, the `trans` case
  instantiates both hypotheses at the same `L'` and the middle terms match on the nose.
* **New entries at the BOTTOM of the context** (`Γ ++ Ts`), so `cvar` is the identity on
  `c`-free terms and the final application is a rewrite, not a computation.
* **`IsDefEq.instL_r`** (`Strong.lean:823`) for the `≈`-class.  `ConstSubst.lean`'s header
  once said level congruence "is not available"; it is, and that file's own body already used
  it.  **Anything a brief tells you is "not available" about level congruence is stale.**

---

## 6. Routes attempted, and the exact step each failed at

| route | failed at |
|---|---|
| direct induction on `IsDefEqU` | `trans`, and `trans` **is** the statement. **[machine-checked]** |
| "prove the typed form instead" | same `trans`; inter-derivable (`Strengthening.iff_typed`). **[machine-checked]** |
| a *propagated* restatement | makes `trans` free, needs a coherence clause whose base case is the target. **[analysis]** |
| Church–Rosser (`ChurchRosser.lean`) | four declarations circular through the `weakN` family; `NormalEq.descend` has three refuted branches. **[measured]** |
| `HeadReduction.lean` | its only conversion⟹reduction bridges are `church_rosser` calls. **[measured]** |
| model side (`Theory/SetModel/`) | vacuous over an uninhabited entry — for the **proof**. For a **refutation** it is the right tool (§1). **[machine-checked / analysis]** |
| `VExpr.Skips` / `IsDefEq.skips` | downstream of the hole, not toward it. **[read]** |
| route 1: axiom conservativity, and its converse | **succeeds as an equivalence** (`ConstVar.lean`) — the residual *is* the hole. **[machine-checked]** |
| substitution (inhabited entry) | **succeeds**, covers the target's general `n`. **[machine-checked]** |
| induction on `HasTypeStrong` (reflexive instance) | **succeeds**; residual `PiDescend`. **[machine-checked]** |
| **λ-form** — "`λ(_:A).e₁ ≡ λ(_:A).e₂` implies `e₁ ≡ e₂`" | reduces the hole to one conversion at `k = 0`, and **the reduction of general `k` to `k = 0` needs typed λ-inversion**, i.e. `forallE_inv` (~~a `sorry` with 105 users~~ — **corrected 2026-09-02: `IsDefEqU.forallE_inv` is a proved theorem, `sorryAx`-tainted through `WF.rigidShapeUniqNS`, not itself a census hole; `docs/audit-doc-claims.md` L2**).  `HasType.lam_inv` (`Strong.lean:904`) gives only `∃ B`, and moving the *equation* from the IH's type to `∀A.B` needs `IsDefEq.uniq`, which is `sorryAx`-tainted **[measured]**.  **Abandoned as tainted, not as wrong.** **[analysis, new]** |
| **`Stratified` (Carneiro's `⊢ₙ`)** | still has an explicit `trans` at `n+1` with an arbitrary middle term (`Stratified.lean:87`); the index drops only the *typing* premises.  No trans elimination is available there. **[read, new]** |
| **junk-environment refutation** (`proofIrrel` at a variable `Prop`) | **collapses at its own witness** — §2. **[machine-checked, new]** |
| **junk-*context* refutation** (`StrengtheningTarget` has no `OnCtx Γ`) | `Ctx.LiftN` + `OnCtx Γ'` forces `OnCtx Γ` at `k = 0`, and at general `k` recovering it is `SortDescend` — part of the hole.  No slack. **[analysis, new]** |
| extraction of a derivation's level lists | **abandoned as not expressible**, and **not needed** — §5. **[analysis]** |

**Do not re-attempt**: a direct conversion induction; the typed form; a model argument *for
the proof direction*; `skips`; re-deriving `Strengthening` from `TransStrengthening`-shaped
residuals; a standalone `PiDescendNeutral → PiDescend` (a tautology); the `_fires`-style
tautological witnesses `StrengthenWitness.lean` §2 records; re-deriving `ConstsIn`;
re-deriving level congruence (`IsDefEq.instL_r` is it); the λ-form *as an equivalence*
without `forallE_inv`; and the open-constant-type witness of §2.

---

## 7. Measurements this round

* `scripts/sorry-census.lean`: **TOTAL 19** at the start and **19** at the end [measured].
  Nothing was closed, so before = after; any claim of 18 would be wrong.
* `scripts/dup-names.lean` (default run): **no duplicates** [measured].  A dedicated run
  importing `Verify/Guard` + `Experimental/ConeJoin` + `ConstVar` + `StrengthenVerdict` in one
  file **caught a real collision** — `Lean4Lean.loop_wf` already existed in
  `Theory/Typing/LogRelRowZero.lean` — which was renamed away (`univInhabDecl_wf`), and the
  run then reports **no duplicates** [measured].  This is the fourth time that instrument has
  paid for itself; run it.
* Axioms on the new file's results: `exists_univInhabEnv`,
  `exists_univInhabEnv_axiomConservativity`, `strengtheningTarget_of_univInhab`,
  `univInhab_no_uninhabited_entry` are `[propext, Classical.choice, Quot.sound]` — the choice is
  inherited from `Strengthen.lean`'s closure, not used in the new proofs [measured, not
  attributed to a particular lemma];
  `univInhabDecl_wf`, `hasType_univInhab_app`, `allProp_isProp`, `onCtx_levelWF`,
  `constOpenType_collapse` are `[propext, Quot.sound]`; `constOpenType_hasType_any` is
  `[propext]` [measured].
* The previous round's five equivalences re-checked: all `[propext, Classical.choice,
  Quot.sound]`, no `sorryAx` [measured].
* `IsDefEq.uniq` and `IsDefEqU.of_l` **are** `sorryAx`-tainted [measured] — this is what
  ruled the λ-form out; do not assume `UniqueTyping.lean`'s non-`weakN_iff` lemmas are clean.

---

## 8. What to pick up first

1. **Read §0.0.**  The reference's own proof of this statement is gapped at `trans`.  Nobody
   has a proof of strengthening for this system to transcribe; a new argument is required.
2. **If you attack it: the only known routes are normalisation-flavoured** — an untyped
   conversion relation with a back-translation, or a logical relation.  `proofIrrel` blocks
   the first (there is no untyped rewriting relation whose equivalence closure is `IsDefEq`),
   and `LogRelRowZero.headStep_not_wf` blocks the second **at the `VEnv.WF` generality**
   (there is a `VEnv.WF` environment whose head reduction is not well founded).  Anything
   that gets past those two facts is new.
3. **If you refute it: use the model, and use a consistent environment.**  §1's correction.
   A counterexample must (a) live in an environment where `Γ ⊬ e₁ ≡ e₂` can be *established*
   — a set model does that — and (b) separate the contexts using only `bvar` and
   `proofIrrel`, since `extra` cannot and open constant types collapse (§2).
4. **`PiDescend`** — equivalently the reflexive instance — is unchanged and still open, and
   is the cheaper target: refuting it refutes the hole.
5. **Do not** spend time on `HeadReduction.lean` or `ChurchRosser.lean`.
6. Optional and cheap: fold `AxiomConservativityWF` back into `StrengthenAxiom.lean` by
   adding `OnCtx Γ` to `AxiomConservativity` in place (a weakening, safe direction).
   Deliberately not done: working rule 3 prefers a separate predicate, and the copy is 25
   lines.

---

## 9. Files

* `Lean4Lean/Theory/Typing/StrengthenVerdict.lean` — **new this round**, 14 declarations, all
  `sorry`-free.  §1's positive instance, §2's killed attack, and the reference note.
  **No other module imports it** — it is a witness/measurement file — but it *is* built by
  `lake build`, since the `Lean4Lean.Theory` library globs `Lean4Lean.Theory.*` [read,
  `lakefile.toml`], so it cannot rot silently.  It is **not** in `Experimental/ConeJoin`'s
  closure, so check it with the dedicated `dup-names` run in §7, not the default one.
* `Lean4Lean/Theory/Typing/ConstVar.lean` — previous round, unchanged.
* `Lean4Lean/Theory/Typing/{Strengthen,StrengthenAxiom,StrengthenWitness,ConstSubst,ConstSubstNested}.lean`
  — unchanged this round.
* `Lean4Lean/Theory/Typing/UniqueTyping.lean` — unchanged; the `sorry` at `:174` stands.
* Read-only and load-bearing: `Strong.lean` (`IsDefEq.instL_r`, `HasType.lam_inv`),
  `Stratified.lean` (has `trans`), `LogRelRowZero.lean` (`headStep_not_wf`, and the
  `loop_wf` name), `Theory/MutualDefUnsound.lean` (the `unsafeDef` pattern).

---

# Round 5 (2026-08-31) — the `trans` residual, narrowed; and the user split

New file: `Lean4Lean/Theory/Typing/StrengthenNarrow.lean` (22 declarations, no new holes;
census stays at 14).  Added to `Experimental/ConeJoin.lean` so both instruments see it.
New script: `scripts/weakn-gate-split.lean`.

## 5.0 First, a correction to the round-5 brief

The brief said this hole "has had less direct attention than `WF.rigidShapeUniq` and
`IsDefEqU.forallE_inv_stratified`".  That is **false** and should not be repeated: five
dedicated files (`Strengthen.lean` 755 lines, `StrengthenAxiom.lean` 385,
`StrengthenCanon.lean` 295, `StrengthenVerdict.lean` 216, `StrengthenWitness.lean` 222) plus
`ConstVar.lean` (666) and this 764-line document precede round 5.  The brief's *direction*
claim was correct: what is open is the strengthening direction
`IsDefEqU Γ' (e1↑) (e2↑) → IsDefEqU Γ e1 e2`; the weakening direction is `h.weakN henv W`.

## 5.1 What was wrong with round 4's capstone, and the repair

`Strengthen.lean` §9 correctly noticed that §8's capstone
`Strengthening ↔ SortDescend ∧ PiDescend ∧ TransStrengthening` is a **tautology** in the `←`
direction: `TransStrengthening.strengthening` instantiates the residual's middle term at
`e2.liftN n k` and its second premise at reflexivity, recovering the whole statement.  So
round 4 ended with a *case analysis*, not a reduction.

The repair is one observation: that self-instantiation picks a middle term that is **itself a
lift**, and in exactly that situation the two induction hypotheses of the `trans` case — which
`Strengthening.of_typing` discards — apply verbatim and `IsDefEqU.trans` composes them.  So
restrict the residual to `¬ b.Skips n k` (equivalently `∀ b₀, b ≠ b₀.liftN n k`, proved
equivalent as `TransStrengtheningNarrow.hyp_iff`).  That kills the self-instantiation
(`TransStrengtheningNarrow.not_hyp_of_lifted`) and leaves a genuine reduction:

* `Strengthening.of_typing_narrow` — `of_typing` with only its `trans` case changed.
* `Strengthening.iff_typing_narrow`, `StrengtheningTarget.iff_typing_narrow`,
  `Strengthening.iff_descend_narrow`, and the sharpest form
  **`StrengtheningTarget.iff_piDescend_narrow` : the hole ↔ `PiDescend ∧
  TransStrengtheningNarrow`** — two statements, neither of which implies the other trivially.

`TransStrengtheningNarrow` also carries three things the `trans` case has in hand and round 4
threw away: a type `T` for the left endpoint **downstairs**, well-formedness of the right
endpoint downstairs, and both premises retyped at the **lifted** type `T.liftN n k` (obtained
by `IsDefEq.uniqU` + `IsDefEqU.defeqDF` against `hT.weakN`).  All three are free at the call
site, so the residual is strictly weaker than `TransStrengthening` in three further ways.

Negative controls, all sorry-free: `not_hyp_of_lifted`, `hyp_iff`, `vacuous_at_zero`
(nothing is stripped at `n = 0`, so the hypothesis is unsatisfiable — the narrowing has not
hidden content in the degenerate case), `vacuous_of_closedN`.

## 5.2 Circularity: measured, not assumed

Using `scripts/hole-cone.lean`'s `deps` (`allowOpaque := true`):

* the **equivalence chain** — `strengthen_of_instN`, `Strengthening.iff_trans`,
  `Strengthening.iff_target`, `Strengthening1.iff_target`, `Strengthening1Uninhab.iff_target`,
  `StrengtheningCanon.iff_target`, `StrengtheningCanonUninhab.iff_strengthening1`,
  `strengtheningTarget_of_allInhabited`, `TypingStrengthening.iff_descend` — has **no** named
  hole in its cone.  A refutation or verdict reached along it would be independent of the
  other two holes.
* every route through the **typing form** — `Strengthening.of_typing`,
  `TypingStrengthening.iff_piDescend`, `PiDescend.sortDescend`, `TypingStrengthening.typed`,
  and therefore all of round 5's §2/§3/§5 — carries **both** `WF.rigidShapeUniqNS` and
  `IsDefEqU.forallE_inv_stratified`, entering through `IsDefEqU.forallE_inv` in
  `Strengthen.lean` §3's ascription-redex trick and **nowhere else**.
* `IsDefEq.church_rosser` and `NormalEq.descend` carry all four holes including
  `IsDefEqU.weakN_iff` itself — the Church–Rosser route is genuinely cyclic, confirming §8.5.
* **nothing** in `Strengthen.lean` or `StrengthenNarrow.lean` depends on
  `IsDefEqU.weakN_iff`: verified for all 22 declarations of the new file.

So the answer to "is it circular with the other two?" is *no cycle, but a shared dependency*:
any proof that goes through the typing half will be `forallE_inv`-tainted until
`forallE_inv_stratified` closes.  The chain that does **not** go through the typing half is
clean, which is why the refutation/verdict work in `StrengthenCanon.lean` and
`StrengthenAxiom.lean` remains the independent line.

## 5.3 The user split — 43 of 296, so the residual is the bottleneck

`UniqueTyping.lean` proves nine wrappers off the full *conversion* form that do not need it:
`OnCtx.weakN_inv`, `HasType.weakN_iff`, `IsType.weakN_iff`, `VExpr.WF.weakN_iff`,
`HasType.skips`, `OnCtx.weak'_inv`, `HasType.weak'_iff`, `IsType.weak'_iff`,
`VExpr.WF.weak'_iff`.  §5 of `StrengthenNarrow.lean` reproves all nine from
`TypingStrengthening` alone (`TypingStrengthening.{onCtx_inv, isType_inv, hasType_inv, wf_inv,
hasType_weakN_iff, hasType_weak'_iff, isType_weak'_iff, onCtx_weak'_inv, wf_weak'_inv,
hasType_skips}`).  Note `Strengthen.lean` §10's `Strengthening.onCtx_inv` runs the same
induction off the *full* `Strengthening` and so needs `SortDescend` where
`TypingStrengthening.typed` suffices.

`scripts/weakn-gate-split.lean` then does reverse reachability with those nine cut:

```
transitive users (all)                  : 296
still reach it with the typing gates cut: 253
freed by the typing half alone          :  43
```

**These are the re-measured figures (2026-09-01).**  Every count in this section previously
read `131 / 113 / 18`, because `scripts/weakn-gate-split.lean` skipped internal names
(`_proof_*`, `_eq_def`, …) when *building* the reverse-reachability graph rather than only
when printing it, so a user reaching the hole through one of its own equation lemmas was
invisible.  Internal names are now pass-through nodes in the graph and the reported set is
still non-internal.  The same bug was fixed in `scripts/hole-rank.lean` days earlier and not
propagated here; **every transitive-user count quoted from these two scripts before
2026-09-01 is an undercount.**  The *shape* of the conclusion is unchanged — the typing half
frees a minority — but the ratio moved from 14% to 15%, and the absolute residual more than
doubled.

**A tenth gate (2026-09-01, same day).**  `hasType_app_bvar0` is provable from
`TypingStrengthening` alone (`CRPiDescend.lean:152` has the verbatim statement with that as its
only added hypothesis), so it belongs in the gate set and is now in the script's `typingGates`.
With it:

```
transitive users (all)                  : 296
still reach it with the typing gates cut: 250
freed by the typing half alone          :  46
```

So the 43 above is itself a floor and **46 / 250 is the figure to quote**; the marginal
conversion-gate losses below are unchanged.  Note the gate is a *hypothesis*-level fact, not a
proof of `hasType_app_bvar0` — `StrengthenInhabGate.lean` §5 has a version needing only an
inhabitant of the binder, with a strictly smaller hole set, but neither of its two call sites
can supply one.

The surviving 253 enter through the five genuine two-endpoint conversions, which are *not* in
the gate set.  Additionally cutting one of them as well loses, marginally (the sets overlap,
so these do not partition the 253): `IsDefEq.weakN_iff` 3, `IsDefEq.weakN_iff'` 5,
`IsDefEqU.weak'_iff` 3, `IsDefEq.weak'_iff` 1, `IsDefEq.skips` 2.  The bulk of the 253 route
through several of them, i.e. through `IsDefEq.weakN_iff'`, which is the load-bearing wrapper.

**Consequence for prioritisation, and it reverses §8.4 of this document.**  §8.4 said
`PiDescend` is "the cheaper target".  It is cheaper, but it is not where the users are:
closing `PiDescend` alone unblocks 43 of 296.  The next round should spend its budget on
`TransStrengtheningNarrow`, not on shape descent.

## 5.4 Verdict

The statement is believed true and is not closable by induction on the derivation.  Exactly
one thing is open, and round 5 states it: **given `Γ' ⊢ e1↑ ≡ b` and `Γ' ⊢ b ≡ e2↑` at a
lifted type, where `b` genuinely mentions a variable of the stripped block, produce
`Γ ⊢ e1 ≡ e2`.**  `~/lean-type-theory/typesys.tex:88-89` (thm:weak (3)(4)) claims this "by
mutual induction on the first hypothesis"; the gap in that proof is precisely here.  Closing
it needs either a normalisation result pushing `b` into the image of the lift — which is what
`NormalEq`/Church–Rosser would give and which is cyclic in this import order — or a model
interpreting open terms.  Round 5 adds no new route; it makes the remaining obligation sharp
and shows it is where the users are.

## 5.5 Do not reattempt (round 5 additions to §8's list)

* Do not "reduce the hole to `TransStrengthening`" or restate §8's capstone: that is the
  tautology of §9/§5.1.  Any residual must exclude middle terms in the image of the lift.
* Do not prove the nine typing wrappers again; §5 of `StrengthenNarrow.lean` has them.
* Do not expect `PiDescend` to unblock the tree: 43 of 296 (§5.3).

# Round 6 — the `NormalEq` route: strengthening below `trans`

New file: `Lean4Lean/Theory/Typing/NormalEqStrengthen.lean` (336 lines, green, zero `sorry`).
Census 14 before, 14 after.  Nothing outside that file was edited.

## 6.1 The lead, and how it changed under measurement

Round 5 ended with: closing the residual needs "a normalisation result pushing `b` into the
image of the lift — which is what `NormalEq`/Church-Rosser would give and which is cyclic in
this import order".  Round 6 attacked the cyclicity instead of the residual.

`NormalEq` (`ChurchRosser.lean:165`) has **no `trans` constructor** — nine constructors:
`refl sortDF constDF appDF lamDF forallEDF etaL etaR proofIrrel` (`NormalEq.trans` at `:481`
is a theorem needing confluence).  `trans` is the one `IsDefEq` rule that defeats
strengthening.  So `NormalEq`-strengthening should not need the hole.  Measured case by case,
against the elaborated types rather than the informal table:

| case | what `weakN_iff` was actually instantiated at | needs |
| --- | --- | --- |
| `sortDF`, `constDF` | — | nothing |
| `refl`, `proofIrrel` | `⟨_, h⟩` with `h : HasType` (i.e. `VExpr.WF.weakN_iff`) | typing half |
| `forallEDF`, `etaL`, `etaR` | `HasType.weakN_iff` at `.sort _` / `.forallE _ _` | typing half |
| `appDF` | genuine conversion, middle term = the upstairs type | **eliminable** |
| `lamDF` | genuine conversion, but at type `.sort u` | sort residual |

Two of the informal table's claims were wrong: `appDF` is not irreducible, and
`etaL`/`etaR`/`forallEDF` are not "restricted conversion" at all, they are pure typing.

`appDF` is eliminated, not weakened: the original retypes the second argument using
`uniqU` upstairs, whose `.trans` has an upstairs middle term.  But the two induction
hypotheses already give `NormalEq Γ f₁ f₂` and `NormalEq Γ a₁ a₂` *downstairs*, and
`NormalEq.defeq` converts those into the retyping conversions directly.  This is the one
substantive change to the proof.

## 6.2 The sort residual collapses (the round's real result)

`SortConvStrengthening` = `Strengthening` with the premise's type a sort.  It is **provable
from the typing half**:

> `SortConvStrengthening.of_typing (henv) : TypingStrengthening env U → SortConvStrengthening env U`

Given `A₂↑ ≡ A₁↑ : Sort u` upstairs, build `fun (_ : A₂↑) => bvar 0 : A₂↑ → A₂↑`, retype it by
`defeqDF` through `forallEDF` at `A₁↑ → A₁↑`.  Both subject and type are now lifts
(`liftN_lam_bvar0`, `liftN_forallE_self_lift`), so `TypingStrengthening.hasType_inv` descends
it; `uniqU` against `lamDF hA₂ (.bvar .zero)` downstairs and `forallE_inv` recover `A₂ ≡ A₁`.

**Why this does not extend to the full hole.**  Encoding a conversion inside a typing
judgement needs a type former with a slot for the converted object.  `forallE` supplies one
for *types*.  Nothing in this pure fragment supplies one for a general *term*: the obvious
attempt, applying a constant function, is information-free —
`sortConv_encoding_vacuous` (§4) proves
`app (lam T (sort 0)) e1 ≡ app (lam T (sort 0)) e2 : Sort 1` with **no hypothesis relating
`e1` and `e2`**, by `beta.trans beta.symm`.  That is the exact boundary of the trick, and it
is why `TransStrengtheningNarrow` survives round 6.

Immediate consequence, `TransStrengtheningNarrow.at_sort`: every **sort-typed** instance of
round 5's residual is closed by the typing half.  Round 5's "43 of 296" pessimism about
`PiDescend` is unchanged for the general residual, but the sort-typed slice is now free.

## 6.3 What is now known

* `NormalEq.weakN_inv_DFC_of_typing`, `NormalEq.weakN_iff_of_typing`: `ChurchRosser.lean:361`
  and `:466` hold from `TypingStrengthening` **alone** — equivalently from `PiDescend`.
* `StrengtheningTarget.of_normalEqComplete`, `.iff_piDescend_of_normalEqComplete`,
  `TransStrengtheningNarrow.of_normalEqComplete`: with confluence as the explicit hypothesis
  `NormalEqComplete : ∀ {Γ e1 e2 A}, OnCtx Γ (IsType env univs) → (Γ ⊢ e1 ≡ e2 : A) →
  Γ ⊢ e1 ≡ₚ e2`, the **hole is exactly `PiDescend`**.  Contrast
  `StrengtheningTarget.iff_piDescend_narrow` (round 5), which additionally needed the narrow
  `trans` residual: `NormalEqComplete` removes that conjunct.

Measured cones (`hole-cone.lean`'s `deps`, `allowOpaque := true`):

| seed | holes |
| --- | --- |
| `NormalEq.weakN_inv_DFC` (original) | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `NormalEq.weakN_iff` (original) | `weakN_iff`, `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `IsDefEq.church_rosser` | + `NormalEq.descend` |
| all 13 results of `NormalEqStrengthen.lean` | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `TypingStrengthening.onCtx_inv` (baseline) | `forallE_inv_stratified`, `rigidShapeUniqNS` |

## 6.4 Verdict, stated without inflation

`TypingStrengthening` has no unconditional inhabitant here; it *is* `PiDescend`, still open.
So round 6's result is "**`NormalEq`-strengthening reduces to `PiDescend`**", not "the hole is
closed".  It removes **one of the two** cycle entries:
`NormalEq.weakN_iff → weakN_inv_DFC → IsDefEqU.weakN_iff` is gone; the other,
`NormalEq.parRed → ParRed.weakN_inv → IsDefEqU.weakN_iff`, is untouched — `ParRedK` defers it
behind `WeakNInvDS` and discharging that reinstates it.  `NormalEqComplete` is a hypothesis,
not an instantiation of `IsDefEq.church_rosser`, because that proof's cone still contains the
hole and routes through `NormalEq.parRed`, whose statement `ParRedPropRefute.lean` refutes.

The reference gap is unchanged and now better localised: `~/lean-type-theory/typesys.tex:88-89`
(thm:weak (3)(4)) is sound for every conversion rule except `trans`, and for `trans` it is
sound whenever the shared type is a sort (§6.2).  Recorded here only.

## 6.5 Proposed edit to `ChurchRosser.lean` (NOT made — file owned by another stream)

Add `(HT : TypingStrengthening env univs)` to `NormalEq.weakN_inv_DFC` (`:361`) and
`NormalEq.weakN_iff` (`:466`), and replace their bodies with
`NormalEqStrengthen.lean`'s `weakN_inv_DFC_of_typing` / `weakN_iff_of_typing`: concretely,
the `IsDefEqU.weakN_iff` / `VExpr.WF.weakN_iff` / `HasType.weakN_iff` / `OnCtx.weakN_inv`
appeals in `:361-470` become `HT.wf_inv`, `HT.hasType_inv`, `HT.onCtx_inv`.  This makes
`ChurchRosser.lean` import `StrengthenNarrow.lean`; check that direction is acyclic before
applying (`NormalEqStrengthen.lean` currently imports `ChurchRosser`, so the shared §2 proof
must move into `ChurchRosser.lean` or into a file both import).

## 6.6 Do not reattempt

* Do not try to run §6.2's identity-function encoding on term-level conversions;
  `sortConv_encoding_vacuous` is the counterexample.
* Do not instantiate `NormalEqComplete` from `IsDefEq.church_rosser` as it stands (§6.4).
* Do not claim the hole closed from round 6: `PiDescend` is the remaining obligation, and
  `ParRed.weakN_inv` is the remaining cycle entry.

---

# Round 7 (2026-09-03) — the projection corner needs only the **typing** half, and the restructure is machine-checked

New files, both owned by this stream:

* `Lean4Lean/Theory/Typing/WeakNProjGate.lean` — 18 source declarations (26 constants with
  equation-compiler auxiliaries), no `sorry`.
* `Lean4Lean/Theory/Typing/WeakNProjSwap.lean` — 5 source declarations, no `sorry`.
  **This one imports `Lean4Lean.Verify.Typing.ProjGenSwap` from a `Theory/` module, which is
  backwards.**  It is a verification harness for §7.4's edit, deliberately separate so it can be
  deleted at any time with no loss to `WeakNProjGate.lean`; delete it or move it into
  `Verify/Typing/` when the edit lands.

Marks as elsewhere in this document: **[measured]** = a run reproduced here, **[read]** = read off
source, **[analysis]** = neither.

## 7.0 Verdict

**The hole is not closed and not refuted.**  Nothing here removes a `sorry`; the census is
unchanged (see the caveat in §7.5 — the census script could not run this round, for a reason
outside this stream).

What is settled:

1. **The whole projection corner — `TrProj.wf`, wall 2 (`VEnv.IsStructureG.projTermG_hasType`)
   and its firing witness — reaches this hole only through the *typing* wrappers.**  Its entire
   dependence is **four call sites, all in `Verify/Typing/ProjSkip.lean`** **[measured, §7.1]**.
   So the corner is unblocked by `PiDescend` alone; the narrow `trans` residual is **not** on its
   route.
2. **One of those four call sites is spurious** — `OnCtx.of_appendTele` appeals to
   `OnCtx.weakN_inv` at `k = 0`, where the "strengthening" is just dropping an appended block: a
   two-line list induction with no `VEnv.WF`, no hypothesis and no hole
   (`VEnv.onCtx_of_appendL`) **[machine-checked]**.
3. **The restructure costs no new hole.**  The obvious substitution —
   `StrengthenNarrow.lean` §5's `TypingStrengthening.{onCtx_inv, isType_inv, hasType_inv}` — would
   trade the hole `weakN_iff` for the hole `WF.rigidShapeUniqNS`, because those go through
   `TypingStrengthening.typed`, hence `IsDefEqU.forallE_inv` **[measured, §7.2]**.  §1–§3 of
   `WeakNProjGate.lean` avoid that: `OnCtx`/`IsType` descent from the typing half is
   **hole-free**, and the sort-typed `HasType` descent the corner actually uses costs only
   `IsDefEqU.forallE_inv_stratified`, which the corner already carries.
4. **Machine-checked end to end at the crux**: `ftype_hasType_swappedGT`
   (`WeakNProjSwap.lean`) is `ftype_hasType_swappedG`'s statement verbatim plus
   `(HT : TypingStrengthening env U)`, and `IsDefEqU.weakN_iff` is **absent from its cone**
   (cone 3536 vs the original's 3535 — the same proof, not a detour) **[measured]**.
5. **Globally the conversion half is still the bottleneck**, so this does not overturn §5.3:
   319 transitive users, **260** still reach the hole with the ten typing gates cut **[measured]**.

The one-line consequence for planning: **proving `PiDescend` does nothing for the projection
corner until §7.4's edit is applied, and after it is applied `PiDescend` alone frees the whole
corner.**  Those two halves have to be scheduled together.

## 7.1 The measurements

Instrument: `deps` = `getUsedConstantsAsSet` over type **and** value with
`allowOpaque := true`, i.e. `scripts/hole-cone.lean`'s walker.  Two graph operations: reverse
reachability with a *cut set* (a cut node is reached but does not propagate), and forward cones.
`scripts/` is not this stream's to edit, so the scripts lived in `/tmp/weakn7/`; the reusable
core is reproduced in §7.9.  **Import closure** (this matters — a module outside it counts as zero):
`Verify.Guard`, `Experimental.ConeJoin`, `Theory.Typing.StrengthenNarrow`,
`Verify.Typing.ProjGenTerm`, `Verify.TypeChecker.ProjGenTermWitness`,
`Verify.Typing.ProjWeakInvSplit`.  Gate set = `scripts/weakn-gate-split.lean`'s ten
`typingGates`.

**(a) Global split, re-measured in that closure** — 24442 graph nodes, 20719 non-internal:

```
transitive users (all)                  : 319
still reach it with typing gates cut    : 260
freed by the typing half alone          :  59
```

Compare `scripts/weakn-gate-split.lean`'s **296 / 250 / 46** at `d67375b`: the difference is the
closure (that script does not import the projection modules), not a change in the tree.  Both
say the same thing — the typing half frees a minority.  Top modules among the 260 survivors:
`Verify.Primitive` 29/29, `Verify.TypeChecker.IsDefEq` 21/22, `Verify.Typing.Lemmas` 20/30,
`Theory.Typing.ChurchRosser` 13/13, `Verify.Typing.ConstSpine` 11/11, `Theory.Typing.KMeasure`
11/11, `UniqueTyping` 11/14.  `Verify.Typing.ProjGenTerm` does **not** appear: 0 survivors.

**(b) The projection corner.**  Seeds: every non-internal declaration of
`Verify.Typing.{ProjGenTerm,ProjSkip,ProjGenSwap,ProjWeakInv,ProjWeakInvSplit}` and
`Verify.TypeChecker.ProjGenTermWitness` (197 seeds), plus `TrProj.wf`, `TrProj.weak'_inv`,
`VEnv.HasType.{swapCtx,swapTele}`, `OnCtx.swapCtx`, `VEnv.IsStructureG.projTermG_hasType`:

```
seeds reaching the hole                 : 32
still reaching with typing gates cut    :  3
freed by the typing half                : 29
still reaching: TrProj.weak'_inv_of_constRigid,
                constAppDefeqStrengthenInh_of_constRigid,
                constAppDefeqStrengthenRF_of_constRigid
```

The three survivors are the `constRigid` line of `ProjWeakInv{,Split}.lean` — the
`ConstAppDefeqStrengthen` residual, which `docs/handoff-trproj-weakinv.md` §3 already argues is
**not in the strengthening family at all**.  `TrProj.weak'_inv` itself reaches the hole *not at
all*: it is its own `sorry`.

**(c) Routes.**  In the cone of each of `TrProj.wf` (5091), `projTermG_hasType` (5271),
`projTerm_hasType` (5082) and `MutField.projTermG_hasType_at_mutual`, the **only** direct user of
`IsDefEqU.weakN_iff` is `VEnv.IsDefEq.weakN_iff'` — and `weakN_iff'` is reached only through
`HasType.weakN_iff` / `IsType.weakN_iff` / `OnCtx.weakN_inv`, which are its own wrappers
(`UniqueTyping.lean:229-242`) **[measured + read]**.

**(d) The four call sites.**  Declarations in the corner's modules whose direct dependencies
contain a gate, **internal names included**:

```
ProjSkip :: OnCtx.of_appendTele            -> OnCtx.weakN_inv
ProjSkip :: VEnv.HasType.swapSkipped       -> VEnv.HasType.weakN_iff
ProjSkip :: OnCtx.swapCtx._f               -> OnCtx.weakN_inv
ProjSkip :: VEnv.HasType.swapCtx._f        -> OnCtx.weakN_inv
Verify.Typing.Lemmas :: VLocalDecl.weakN_iff, VLocalDecl.weak'_iff,
                        HasType.skips, TrExprS.weakFV'_inv        (other routes)
```

and a per-seed check confirms the corner uses the first four and **none** of the four in
`Verify/Typing/Lemmas.lean` **[measured]**.

> **Trap, hit again, in a new script, on the same day it was documented.**  My first version of
> (d) skipped internal names and reported **6** sites, missing `OnCtx.swapCtx._f` and
> `VEnv.HasType.swapCtx._f` — the equation-compiler bodies of the two structurally recursive
> `swapCtx`es, i.e. exactly the two sites that matter most.  This is §5.3's bug in a third
> instrument.  **Any scan of "who calls what" in this tree must keep internal names as nodes.**

**(e) Uses of the swap, by type.**  `VEnv.HasType.swapCtx` has exactly two non-witness callers,
`ftype_hasType_swapped` (`ProjSkip.lean:615`, the call at `:629`) and
`ftype_hasType_swappedG` (`ProjGenSwap.lean:52`, the call at `:64`), and **both use it at a sort type** — the conclusion is
`… ⊢ (C.fields.getD i default).type.instL us : .sort ((C.fields.getD i default).lvl.inst us)`.
The `bar*` witnesses (`ProjSkip.lean:288,431`) are sort-typed too **[read, all five sites]**.
That is what makes §7.2's cheap route sufficient.

## 7.2 Why the obvious substitution is a bad trade, and what the file does instead

Hole cones **[measured]**:

| declaration | holes in cone |
|---|---|
| `TypingStrengthening.of` | *none* |
| `TypingStrengthening.sortDescend` | *none* |
| `IsDefEq.uniq`, `.uniqU`, `IsDefEqU.sort_inv`, `IsDefEqU.defeqDF` | `forallE_inv_stratified` |
| `TypingStrengthening.typed`, `.onCtx_inv`, `.isType_inv`, `.hasType_inv`, `.wf_inv` | `forallE_inv_stratified`, **`rigidShapeUniqNS`** |
| `IsDefEqU.forallE_inv`, `SortConvStrengthening.of_typing`, `PiDescend.sortDescend` | `forallE_inv_stratified`, **`rigidShapeUniqNS`** |
| `TrProj.wf`, `projTermG_hasType` (today) | `weakN_iff`, `forallE_inv_stratified` |

So substituting `StrengthenNarrow.lean` §5's wrappers into the corner would give hole set
`{forallE_inv_stratified, rigidShapeUniqNS}` — a hole for a hole, plus an open hypothesis.  Not
progress.

The fix is to route the descent through `SortDescend` rather than through `typed`:

* `TypingStrengthening.typed` upgrades "some type downstairs" to "the given type downstairs" by
  the ascription-redex trick of `Strengthen.lean` §3, and inverting that redex needs
  `IsDefEqU.forallE_inv`.  **That is where `rigidShapeUniqNS` enters, and it enters nowhere
  else on this route.** **[measured]**
* For a judgement whose type is a **sort**, no upgrade is needed: `SortDescend` produces a sort
  type downstairs directly, and `TypingStrengthening.sortDescend` supplies `SortDescend` from the
  typing half **hole-free**.
* `IsType` leaves the level existential, so `IsType`/`OnCtx` descent is *exactly* what
  `SortDescend` returns — hole-free, both of them.
* Only pinning the **level** (which the corner needs: the stored `lvl.inst us`) costs anything,
  and it costs `IsDefEqU.sort_inv`, i.e. `forallE_inv_stratified` — **already** in the corner's
  cone.

`hasType_inv` at a general type still costs `rigidShapeUniqNS`
(`TypingStrengthening.hasType_swapSkipped`, §4 of the file, kept for contrast); by §7.1(e) the
corner never needs it.  **[analysis, on the "you cannot use a conversion without inverting the
type former" argument; measured, on every cone quoted]**

## 7.3 What is machine-checked

`Lean4Lean/Theory/Typing/WeakNProjGate.lean` (namespace `Lean4Lean.VEnv`):

| name | statement | axioms | holes |
|---|---|---|---|
| `onCtx_of_appendL` | `OnCtx (As ++ Γ) P → OnCtx Γ P` | none | none |
| `onCtx_of_appendTele_free` | `ProjSkip.OnCtx.of_appendTele`'s statement, **without `VEnv.WF`** | none | none |
| `TypingStrengthening.onCtx_isType_inv` | `OnCtx` descent **and** `IsType` descent, together (one induction) | `propext, Quot.sound, Classical.choice` | **none** |
| `TypingStrengthening.onCtx_inv'` | `OnCtx.weakN_inv` from the typing half | same | **none** |
| `TypingStrengthening.isType_inv'`, `.isType_weakN_iff'` | `IsType.weakN_iff`, forward and as an `iff` | same | **none** |
| `TypingStrengthening.hasType_sort_inv` | `HasType.weakN_iff` forward **at a sort type, level preserved** | + `sorryAx` | `forallE_inv_stratified` |
| `TypingStrengthening.hasType_sort_swapSkipped`, `_one` | `ProjSkip.VEnv.HasType.swapSkipped{,_one}` at a sort type | + `sorryAx` | `forallE_inv_stratified` |
| `TypingStrengthening.hasType_sort_swapTele` | `ProjSkip.VEnv.HasType.swapTele` at a sort type | + `sorryAx` | `forallE_inv_stratified` |
| `TypingStrengthening.hasType_swapSkipped` | the **general** swap, for contrast | + `sorryAx` | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `exists_typingStrengthening_env` | **the hypothesis is inhabited** at a `VEnv.WF` env, every `U` | `propext, Quot.sound, Classical.choice` | **none** |
| `exists_env_hasType_sort_swapSkipped_one` | …and the swap holds there unconditionally, ∀ `U Γ A A' b u` | + `sorryAx` | `forallE_inv_stratified` |
| `bvar0_not_liftN_one`, `liftN_zero_ctx_eq`, `liftN_ctx_length`, `not_liftN_swap`, `hasType_sort_swapSkipped_zero` | the negative controls (§7.5) | ≤ `propext, Quot.sound, Classical.choice` | none |

`Lean4Lean/Theory/Typing/WeakNProjSwap.lean` (namespace `Lean4Lean`) — the harness:

| name | = | `weakN_iff` in cone | holes |
|---|---|---|---|
| `VEnv.HasType.swapTeleT` | `swapTele` + `HT`, sort-typed | **no** | `forallE_inv_stratified` |
| `OnCtx.swapCtxT` | `OnCtx.swapCtx` + `HT`, verbatim | **no** | **none** |
| `VEnv.HasType.swapCtxT` | `VEnv.HasType.swapCtx` + `HT`, sort-typed | **no** | `forallE_inv_stratified` |
| `ftype_hasType_swappedGT` | **the corner's crux**, `ftype_hasType_swappedG` + `HT`, verbatim otherwise | **no** (cone 3536 vs 3535) | `forallE_inv_stratified` |
| `onCtxFields_swappedGT` | the `OnCtx` companion `ProjGenSwap.lean:139` needs | **no** | **none** |

`lake build` green on both modules; `scripts/dup-names.lean` with each of them added to the
joined cone: **no duplicates** **[measured, twice]**.  Every row's axiom column was produced by
`#print axioms` on the fully qualified name, read off the files' own `namespace` lines
(`Lean4Lean` + `VEnv` for `WeakNProjGate`, `Lean4Lean` only for `WeakNProjSwap`) — all 19 names
resolved, none reported `unknown constant` **[measured]**.

**Honesty, in the terms this document uses.**  Nothing above is *discharged*: §1's results are
conditional on an open hypothesis, and §2–§4's carry `sorryAx` through
`IsDefEqU.forallE_inv_stratified` (a hole owned by another stream).  "`weakN_iff` absent from the
cone" is not "hole-free".

## 7.4 The edit, exactly — `Verify/Typing/ProjSkip.lean`, four sites

Not this stream's file.  All four are in `ProjSkip.lean`; each is a body replacement plus, for
three of them, one added hypothesis `(HT : VEnv.TypingStrengthening env U)` threaded to the
callers (`ftype_hasType_swapped`, `ftype_hasType_swappedG`, `VIndCtor.swapDataG`, and onward to
`projTermG_hasType` / `TrProj.wf`).

1. **`OnCtx.of_appendTele` (`:327`)** — drop `henv`, body becomes the list induction:
   `VEnv.onCtx_of_appendL`.  No hypothesis, no hole.  *This one is free and independent of
   everything else.*
2. **`VEnv.HasType.swapSkipped` (`:156`)** — add `HT`, restrict `B` to `.sort u`, body becomes
   `VEnv.TypingStrengthening.hasType_sort_swapSkipped`.  (`swapSkipped_one` likewise.)
3. **`OnCtx.swapCtx` (`:360`)** — add `HT`; replace its `OnCtx.weakN_inv` by `HT.onCtx_inv'` and
   its `OnCtx.of_appendTele` by `VEnv.onCtx_of_appendL`.  Proved: `OnCtx.swapCtxT`, hole-free.
4. **`VEnv.HasType.swapCtx` (`:332`) and `.swapTele` (`:245`)** — add `HT`, restrict `B` to
   `.sort u`, same two replacements inside.  Proved: `VEnv.HasType.swapCtxT`, `.swapTeleT`.

`WeakNProjSwap.lean` *is* those four, elaborated, plus the crux they feed
(`ftype_hasType_swappedGT`).  The `B := .sort u` restriction is safe by §7.1(e): every existing
caller is sort-typed.  If a future caller needs a general `B`, `hasType_swapSkipped` (§4 of
`WeakNProjGate.lean`) covers it at the price of `rigidShapeUniqNS`.

After the edit the corner's hole set is `{forallE_inv_stratified}` plus the hypothesis
`TypingStrengthening` ⟺ `PiDescend` — whose discharge site is
`Strengthen.lean`'s `TypingStrengthening.iff_piDescend` / `TypingStrengthening.of`, i.e. **shape
descent, and nothing about `trans`.**

## 7.5 Anti-vacuity

* **The hypothesis is inhabited**: `exists_typingStrengthening_env` **[machine-checked,
  hole-free]** — a `VEnv.WF` environment satisfying `TypingStrengthening` at every `U`, via
  `StrengthenVerdict.lean`'s `exists_univInhabEnv` and `StrengtheningTarget → Strengthening →
  TypingStrengthening`.  **Read §3's scope statement with it**: that environment declares
  `univInhab : ∀ (α : Sort u), α`, so it is inconsistent and (by
  `univInhab_no_uninhabited_entry`) has no uninhabited context entry, which is precisely the case
  `Strengthen.lean` §1 already closes.  It is a *satisfiability* witness — the hypothesis is not
  contradictory — and nothing more.  `exists_env_hasType_sort_swapSkipped_one` fires the swap
  there with **every** hypothesis discharged and quantified over `U`, `Γ`, both binder types, the
  subject and the level; the conclusion at that environment is also independently provable, so
  that firing shows satisfiability, not content.
* **Quantification.**  Everything in `WeakNProjGate.lean` is quantified over `env`, `U`, `n`,
  `k`, both contexts, the terms and the levels; only the inhabitation results choose an
  environment, and they must (the hypothesis is open in general).
* **Negative controls** **[machine-checked]**:
  (a) `bvar0_not_liftN_one` — `.bvar 0` is not in the image of `liftN 1 · 0`, so the swap's
  "subject is a lift" hypothesis is a *proper* restriction: the lemma is not the (false) claim
  that every judgement survives a binder change.
  (b) `liftN_zero_ctx_eq` + `liftN_ctx_length` + `not_liftN_swap` — once the two binders differ,
  the swap's source and target contexts are related by **no** `Ctx.LiftN` whatsoever, so the
  transport is genuinely not weakening and no composition of weakenings replaces it.
  (c) `hasType_sort_swapSkipped_zero` — at `n = 0` the conclusion *is* the hypothesis, so all
  content lives at `n ≥ 1` (the `vacuous_at_zero` discipline of §5.1).
* **What is missing, and it is missing for a reason already recorded.**  There is no `⊬` control
  here — no witness at which the swap *fails* — because §A.2's census found the tree's 31
  non-derivability instruments are all head-shape facts and all lift-stable, so none separates
  two contexts.  I did not re-measure that census; I am relying on it **[read]**.
* **Census.**  `scripts/sorry-census.lean` **could not run** this round: it fails with
  `object file … Theory/SetModel/InductOracleWitness.olean … does not exist`, from another
  stream's in-flight edit under `Theory/SetModel/`.  So "census unchanged" is *not* measured this
  round.  What is measured: neither new file contains the token `sorry`, and every `sorryAx` in
  their cones is reached through `IsDefEqU.forallE_inv_stratified` **[measured]**.

## 7.6 Where the brief and earlier rounds are wrong

1. **The brief calls this "the most load-bearing hole in the projection corner".**  Load-bearing
   yes, but the corner's load is carried entirely by the **typing** half — and the round-5
   prioritisation the brief inherits (§5.3: *"spend its budget on `TransStrengtheningNarrow`, not
   on shape descent"*) is therefore **wrong for the projection corner**, while remaining right
   globally (260 of 319).  Round 5's own §5.5 *"do not expect `PiDescend` to unblock the tree"*
   should read: *`PiDescend` unblocks the projection corner and nothing else measured so far.*
2. **"Reduce it, or price it honestly" assumed the price is paid at `weakN_iff`.**  For the
   corner, one quarter of the price is paid at nothing at all: `OnCtx.of_appendTele` calls the
   tainted gate where a two-line induction does the job (§7.0(2)).  A gate call is not evidence
   that strengthening is needed.
3. **`docs/handoff-trproj-weakinv.md` §0's "the route is closed"** is about
   `ConstAppDefeqStrengthen`, the residual of `TrProj.weak'_inv` — a *different* statement from
   `TrProj.wf`'s dependence, and the measurement confirms the separation: those three
   declarations are exactly the 3 of 32 that the typing half does **not** free (§7.1(b)).  Do not
   read that verdict as covering `TrProj.wf`.
4. **`ProjSkip.lean`'s own docstring** (`:49-51`, `:610`) says the swap costs "exactly one
   `VEnv.HasType.weakN_iff` per swapped binder … an existing hole owned by another stream".  True
   but overpriced: what it needs is one **sort-typed** typing strengthening per swapped binder,
   which is a strictly weaker statement, and its `OnCtx` half needs no strengthening beyond
   `OnCtx` descent, which is hole-free from the typing half (§7.3).
5. **§6.5's proposed `ChurchRosser.lean` edit** and this round's §7.4 are the same manoeuvre in
   two places, and both are still unapplied.  Whoever applies one should apply the other.

## 7.7 What was not achieved

* `PiDescend` / `SortDescend` were **not** attacked; the hole's own status is unchanged.  I did
  not attempt a proof or a refutation of either.
* The 260 global survivors are untouched.  The conversion half is where they are, and this round
  says nothing new about it.
* **A cheaper target than `PiDescend` for the corner does not exist in the obvious place.**
  `SortDescend` alone is *not* enough for the corner, and the reason is in the definitions:
  `SortDescend` carries the premise `VExpr.WF env U Γ e` — it presupposes the term is typeable
  downstairs — whereas `IsType.weakN_iff` must *produce* typeability from nothing.  The producing
  step is `TypingStrengthening` itself, whose `app` case is the only one that needs `PiDescend`
  (`Strengthen.lean:395-402`).  So the corner needs full `PiDescend` unless the terms it
  strengthens are application-free, and field types are not.  **[read, on both definitions;
  analysis, on the conclusion]**
* An **inhabited-replacement shortcut does not exist either**, and it is worth recording because
  it looks obvious: the swap replaces a field binder by the *inhabited* `VExpr.swapUnit`, and
  `Strengthen.lean` §1's proved half strips *inhabited* entries — but the entry being **stripped**
  is the field type (arbitrary, possibly uninhabited), and the inhabited term is the one being
  **inserted**.  Weakening first and substituting afterwards does not help: substituting the
  field entry needs an inhabitant of it in the smaller context, and substituting the inserted
  `swapUnit` entry undoes the insertion.  **[analysis]**

## 7.8 What to pick up first

1. **Apply §7.4 site 1 unconditionally.**  `OnCtx.of_appendTele → VEnv.onCtx_of_appendL` needs no
   hypothesis, removes a gate call, and cannot regress anything.
2. **Decide whether to apply §7.4 sites 2–4.**  They put `TypingStrengthening` in the projection
   corner's hypotheses in exchange for removing `weakN_iff` from its cone with no new hole.  This
   is a scheduling decision, not a mathematical one: it is worth doing exactly if `PiDescend` is
   going to be attacked.  `WeakNProjSwap.lean` is the proof that the edit elaborates.
3. **Then attack `PiDescend`, knowing the corner is what it buys.**  Its `app` case is the whole
   statement (`Strengthen.lean:395`), and §6.2's identity-function encoding is known not to
   extend to term-level conversions (`sortConv_encoding_vacuous`).
4. **Do not** re-run the "which users need which half" measurement without internal names in the
   graph (§7.1's warning), and do not re-attempt anything in §6/§8's do-not lists.

## 7.9 The instrument, reproduced (it is not in `scripts/` — that directory is not this stream's)

Save as a file anywhere and run `lake env lean <file>`.  The `cut` parameter is the whole point:
a cut node is *reached* but does not propagate, which is what turns "who reaches the hole" into
"who reaches the hole *other than through the typing wrappers*".  **Keep internal names as graph
nodes** (§7.1's warning).

```lean
import Lean4Lean.Verify.Guard
import Lean4Lean.Experimental.ConeJoin
import Lean4Lean.Theory.Typing.StrengthenNarrow
import Lean4Lean.Verify.Typing.ProjGenTerm
import Lean4Lean.Verify.TypeChecker.ProjGenTermWitness
import Lean4Lean.Verify.Typing.ProjWeakInvSplit
open Lean Elab Command

private def depsOf (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | none => {}
  | some ci =>
    let cs := ci.type.getUsedConstantsAsSet
    match ci with
    | .thmInfo v => cs.union v.value.getUsedConstantsAsSet
    | _ => match ci.value? (allowOpaque := true) with
           | some v => cs.union v.getUsedConstantsAsSet
           | none => cs

private def hole : Name := ``Lean4Lean.VEnv.IsDefEqU.weakN_iff

private def typingGates : List Name :=          -- = scripts/weakn-gate-split.lean's ten
  [``Lean4Lean.VEnv.hasType_app_bvar0, ``Lean4Lean.VEnv.HasType.weakN_iff,
   ``Lean4Lean.VEnv.IsType.weakN_iff, ``Lean4Lean.VExpr.WF.weakN_iff,
   ``Lean4Lean.OnCtx.weakN_inv, ``Lean4Lean.OnCtx.weak'_inv,
   ``Lean4Lean.VEnv.HasType.weak'_iff, ``Lean4Lean.VEnv.IsType.weak'_iff,
   ``Lean4Lean.VExpr.WF.weak'_iff, ``Lean4Lean.VEnv.HasType.skips]

/-- forward cone of `seed`, not traversing *through* members of `cut`. -/
partial def coneCut (env : Environment) (cut : NameSet) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then coneCut env cut rest seen else
    let seen := seen.insert n
    if cut.contains n then coneCut env cut rest seen else
    coneCut env cut ((depsOf env n).toList ++ rest) seen

run_cmd do
  let env ← getEnv
  let gates : NameSet := typingGates.foldl (·.insert ·) {}
  for g in hole :: typingGates do
    if (env.find? g).isNone then logError s!"UNRESOLVED {g}"   -- never trust a silent zero
  for s in [``Lean4Lean.TrProj.wf, ``Lean4Lean.VEnv.IsStructureG.projTermG_hasType] do
    let now := (coneCut env {} [s] {}).contains hole
    let cut := (coneCut env gates [s] {}).contains hole
    logInfo s!"{s}  reaches:{now}  reaches-with-typing-gates-cut:{cut}"
  -- the four call sites: internal names INCLUDED
  for (n, _) in env.constants.toList do
    unless (`Lean4Lean).isPrefixOf n do continue
    let used := typingGates.filter (depsOf env n).contains
    unless used.isEmpty do
      if (coneCut env {} [``Lean4Lean.TrProj.wf] {}).contains n then
        logInfo s!"   site: {n} -> {used}"
```

Verbatim output at this round's tree **[measured — this block was extracted from this document
and run]**:

```
Lean4Lean.TrProj.wf  reaches:true  reaches-with-typing-gates-cut:false
Lean4Lean.VEnv.IsStructureG.projTermG_hasType  reaches:true  reaches-with-typing-gates-cut:false
   site: Lean4Lean.OnCtx.swapCtx._f -> [Lean4Lean.OnCtx.weakN_inv]
   site: Lean4Lean.VEnv.HasType.swapCtx._f -> [Lean4Lean.OnCtx.weakN_inv]
   site: Lean4Lean.OnCtx.of_appendTele -> [Lean4Lean.OnCtx.weakN_inv]
   site: Lean4Lean.VEnv.IsDefEq.weakN_iff -> [Lean4Lean.OnCtx.weakN_inv]
   site: Lean4Lean.VEnv.HasType.swapSkipped -> [Lean4Lean.VEnv.HasType.weakN_iff]
```

Five rows, **four** of them the edit sites of §7.4 (all in `ProjSkip.lean`).  The fifth,
`VEnv.IsDefEq.weakN_iff`, is `UniqueTyping.lean:229`'s own wrapper: it is in the *uncut* cone but
is reached only *through* `HasType.weakN_iff`, so cutting the gates never visits it and it is not
a site to edit.  If you want the site list alone, filter the last loop by module.
