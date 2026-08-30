# Handoff: strengthening — `IsDefEqU.weakN_iff`

**Target:** the forward (strengthening) direction of `Lean4Lean.VEnv.IsDefEqU.weakN_iff`,
`Theory/Typing/UniqueTyping.lean:172`.  **Still open. Not proved, not refuted.**  Census
re-run this pass: **19**, unchanged, and this pass added no `sorry`.

Marks, kept strictly separate throughout:
**[machine-checked]** = a named `sorry`-free Lean declaration in this tree;
**[measured]** = a machine run whose output is reproduced here;
**[read]** = read off source; **[analysis]** = neither.

This pass **corrected three inherited claims** (§5) and landed three new sorry-free sections
in `Theory/Typing/Strengthen.lean` (§1).  Read §0 first.

---

## 0. The five things to know before touching this

0. **§1–§9 of `Strengthen.lean` did not formally reach the hole, and now they do.**
   `Strengthening` (the file's own statement) carries **two** context hypotheses, `OnCtx Γ`
   *and* `OnCtx Γ'`; the `sorry` carries only `OnCtx Γ'`.  An extra hypothesis makes
   `Strengthening` a *weaker* statement, so proving it would not have discharged the hole.
   The gap is `OnCtx.weakN_inv`, which is downstream of the hole.  It is now closed —
   non-circularly, because that induction only uses strengthening at strictly smaller lifting
   witnesses — by `Strengthening.iff_target`. **[machine-checked, sorry-free]**  This was a
   real defect in the development's *statement of what it was doing*, not in any proof.
1. **The obstruction is exactly the uninhabited context entries — this is now a theorem, not a
   remark.**  `Strengthening1Uninhab.iff_target` **[machine-checked]**: the target follows from
   itself restricted to strippings whose entry has **no inhabitant in its own prefix context**.
   Its vacuity dual is also machine-checked (`strengtheningTarget_of_allInhabited`): if every
   stripped entry were inhabited, §1's substitution argument alone would close the target.  So
   the residual carries content exactly to the extent that uninhabited entries exist — and
   *exhibiting one over a `VEnv.WF` environment is itself open in this tree*
   (`VEnv.Consistent` is a `def`; `leanTTConsistent` is proved nowhere here). **[read]**
2. **Stripping one entry at a time is enough** (`Strengthening1.iff_target`,
   **[machine-checked]**).  This matters because *every* tool in §1 of `Strengthen.lean` —
   `Ctx.LiftN.exists_instN`, `IsDefEqU.strengthen_of_instN`, `IsDefEq.strengthen_of_instN` —
   is stated at `Ctx.LiftN 1 k` only, and until now nothing connected them to the target's
   arbitrary `n`.
3. **`HeadReduction.lean` cannot deliver, and the reason is one line of source, not a
   judgement call.**  Its *only* two conversion-to-reduction bridges, `IsDefEq.reduce_sort`
   (`:470`) and `IsDefEq.reduce_forallE` (`:488`), both open with `H.church_rosser hΓ`.
   **[read]**  Measured: of the file's 203 declarations, **21 are `sorryAx`-tainted**, and of
   the 66 whose *statement* mentions `IsDefEq`/`HasType`/`IsDefEqU`/`IsType`, the 45 clean ones
   are **entirely** recursors, `casesOn`, `below`, match-auxiliaries, three constructors and
   the three `*.instN` stability lemmas — **no clean theorem in the file relates conversion to
   reduction**. **[measured, §4]**
4. **The relay's "`church_rosser`'s statement is machine-checked FALSE" is overstated, twice.**
   `KCanonical.not_crStatement_of_kstep` is (a) conditional on nine rigidity hypotheses about a
   witness that **no `Params` instance in this tree satisfies** — the file says so itself
   ("The instance that would test it does not exist") — and (b) **itself `sorryAx`-tainted**,
   through exactly `IsDefEqU.forallE_inv_stratified` and nothing else. **[measured, §5.1]**
   The honest reading is *conditional* refutation, and it does not change the verdict on
   `HeadReduction.lean`, which is independent (§4).

---

## 1. What landed this pass — `Theory/Typing/Strengthen.lean` §10–§12

All sorry-free; axioms measured with `#print axioms`. **[measured]**

| name | statement | axioms |
|---|---|---|
| `StrengtheningTarget` | the hole's statement verbatim (`OnCtx Γ'` only) | — (`def`) |
| `StrengtheningTarget.strengthening` | the easy direction | `[propext]` |
| `Strengthening.onCtx_inv` | `OnCtx.weakN_inv` **from `Strengthening`**, non-circularly | `[propext, Classical.choice, Quot.sound]` |
| **`Strengthening.iff_target`** | **the development's statement is the hole's** | same |
| `StrengtheningTarget.iff_trans` | chaining §9: the hole *is* `TransStrengthening` | same |
| `Ctx.LiftN.eq_of_zero` | a `LiftN 0` is the identity on contexts | `[propext]` |
| `Ctx.LiftN.split_one` | `LiftN (n+1) k` factors as `LiftN n k` then `LiftN 1 k` | `[propext]` |
| `Strengthening1` | the target at `n = 1` | — (`def`) |
| `Strengthening1.onCtx_inv` | §10's induction at `n = 1` | `[propext, Classical.choice, Quot.sound]` |
| **`Strengthening1.iff_target`** | **one entry at a time is enough** | same |
| `Strengthening1Uninhab` | the target at `n = 1`, entry uninhabited | — (`def`) |
| `Strengthening1Uninhab.strengthening1` | classical case split on inhabitedness | same |
| **`Strengthening1Uninhab.iff_target`** | **the uninhabited case is the whole target** | same |
| `strengtheningTarget_of_allInhabited` | the vacuity dual of the line above | same |
| `onCtx_uninhab_premises` | premise satisfiability at an uninhabited entry, `k = 0` | `[propext]` |

**Non-circularity.**  None of these mentions `IsDefEqU.weakN_iff`; the `onCtx_inv` inductions
apply the *hypothesis* `Strengthening`/`Strengthening1`, never the theorem.  `Strengthen.lean`
builds green and `StrengthenWitness.lean` and `SetModel/StableAudit.lean` (its two importers)
still build. **[measured]**

**Collapse test applied to §12** (the one new *reduction*): `Strengthening1Uninhab`'s premises
are the target's plus `n = 1`, plus `OnCtx Γ`, plus uninhabitedness.  There is no
instantiation of its quantifiers that degenerates those into the target's — the extra premise
is not derivable from the others.  It is therefore a strictly weaker statement, i.e. a genuine
reduction, and its *only* degenerate mode (uninhabitedness never satisfiable) is exactly the
mode in which the target is already proved, which is what
`strengtheningTarget_of_allInhabited` makes machine-checkable.

**Polarity check.**  `Strengthening1Uninhab` occurs in *positive* position (it is what a future
proof would establish), so adding a hypothesis weakens it — the safe direction.  Nothing was
widened in negative position.

---

## 2. Where the target actually stands

Chaining §9, §10, §11 and §12, all sorry-free, the hole is **equivalent** to each of:

* `TransStrengthening` — its own `trans` case, which is why the direct induction is not a
  reduction (inherited, `Strengthening.iff_trans`);
* `Strengthening1` — the same at a single stripped entry;
* `Strengthening1Uninhab` — the same, at a single **uninhabited** stripped entry.

And its *reflexive instance* is equivalent to `PiDescend` alone (inherited,
`TypingStrengthening.iff_piDescend`, `sorryAx` via `forallE_inv`).

### 2.1 The crux, stated as sharply as this pass can state it  **[analysis]**

Every route bottoms out in one question:

> **Can an extra context entry make two `Γ`-terms convertible when they are not convertible in
> `Γ`?**

The reduction of everything else to that is worth writing down, because it kills three
tempting sub-attacks at once:

* **`proofIrrel` cannot be the mechanism on its own.**  Suppose `Γ' ⊢ e1↑ ≡ e2↑` by
  `proofIrrel` at some `p : Sort 0` that mentions the stripped variable.  Then `e1↑ : p`, so by
  `IsDefEq.uniq` the `Γ`-type `A1` of `e1` satisfies `Γ' ⊢ A1↑ ≡ p`, hence `Sort u1 ≡ Sort 0`,
  hence `u1 ≈ 0`: `A1` was already a proposition *in `Γ`*.  Same for `A2`.  What remains is
  `Γ' ⊢ A1↑ ≡ A2↑`, i.e. the question above, at *types*.
* **`proofIrrel` cannot fire between two `Γ`-types either.**  A term that is both a `Sort u`
  and a proof of a `Prop` forces `Sort 0 ≡ Sort 1` through `uniq`.  So no conversion *between
  types* ever comes from proof irrelevance.
* **`PiDescend`'s open cases are the same question.**  Given `Γ' ⊢ f↑ : ∀ A B` and
  `Γ ⊢ f : Tf`, `uniq` gives `Γ' ⊢ Tf↑ ≡ ∀ A B`; extracting a Π shape for `Tf` and then
  matching its domain against `a`'s `Γ`-type is again a conversion between two lifted types.

Every other rule of `IsDefEq` (`sortDF`, `constDF`, `appDF`, `lamDF`, `forallEDF`, `beta`,
`eta`, `extra`, `defeqDF`) is context-independent in its *contraction*; the context enters only
through the typing premises and through `trans`'s middle term.

### 2.2 Refutation attempts, and where each stopped  **[analysis unless marked]**

The base rate of this session is that such statements turn out false, so this was attempted
first.  It did not succeed, and here is the exact shape of the failure, so nobody repeats it.

| attempted witness | why it does not refute |
|---|---|
| a `Prop` entry over an **inconsistent** `VEnv.WF` env (`MutualDefUnsound`, `CycleConv`) | such an env has a closed `f : ∀ p, p`, so **every** `Prop` entry is inhabited downstairs and §1 discharges it outright.  Inconsistency makes the problem *easier*, not harder. |
| `Γ' = [0 = 1]` (a genuinely uninhabited `Prop`) with an ι/K mechanism | the stripped variable is a *stuck* major premise; `Theory/` registers only constructor-matching ι rules (`Pattern.lean:293`), so nothing fires, and the closed endpoints can only be reached back through β, which returns the term you started from |
| `Γ' = [Sort (.param 0)]` over `VEnv.empty` at `U = 1` | this **is** a valid `OnCtx` context with a (syntactically) uninhabited entry, but `VEnv.empty` has no constants and no `defeqs`, so the only conversions between closed terms are β/η/congruence, which the entry cannot touch.  Proving the entry uninhabited is itself a normalisation statement. |
| `proofIrrel` at a `p` mentioning the variable | §2.1, first two bullets: collapses to the crux |
| structure-eta / unit-like (`isDefEqUnitLike`) | not rules of `Theory/`'s `IsDefEq` at all **[read, `Theory/Typing/Basic.lean`]**, so unavailable as a mechanism here |

**The honest summary: no counterexample was found, and no argument was found that one cannot
exist.**  "No witness" is not evidence of truth.

### 2.3 Two routes with a price, neither attempted  **[analysis]**

Recorded so the next pass can price them rather than rediscover them.

1. **Turn the context entry into an environment axiom.**  Π-close the stripped entry over its
   prefix, add it as a fresh axiom constant `c`, and substitute `x := c ⟨prefix bvars⟩`.  Then
   `IsDefEqU.strengthen_of_instN` applies over `env⁺ = env.addConst c C`, and what is left is
   **conservativity of adding one axiom**: `env⁺ ⊢ Γ ⊢ e1 ≡ e2` with everything `c`-free
   implies `env ⊢ Γ ⊢ e1 ≡ e2`.  Price: a Π-closure construction over a context plus its
   typing lemma; nothing like it is in `Theory/Typing/`.  **Value: it removes all de Bruijn
   bureaucracy and makes the unknown uniform.  It does *not* escape the model wall** — if `C`
   is empty in every model, `env⁺` has no model, exactly as in §3 — which is evidence the
   reduction is faithful rather than a cheat.
2. **Reduce to `k = 0`.**  λ-abstract the `k` entries above the stripped one on both sides,
   apply strengthening at the innermost position, then re-apply to the bound variables and
   β-reduce.  This is valid (the abstraction of a lifted term is the lift of the abstraction)
   and would let a future reduction relation deal only with `Γ' = T :: Γ` and `e.lift`.
   Price: `mkLams`-over-a-context machinery with its typing lemmas.

---

## 3. Why no model argument reaches this — unchanged, and now with §12 behind it

`(e.liftN 1 k).inst e₀ k = e`, so an inhabitant of the stripped entry turns the `Γ'`-conversion
into a `Γ`-conversion (`IsDefEqU.strengthen_of_instN`, sorry-free).  §12 upgrades that from a
remark to `Strengthening1Uninhab.iff_target`: the difficulty is **confined to entries that are
uninhabited downstairs**, and over such a context every soundness statement is vacuous, so
`Theory/SetModel/` cannot see the difference. **[machine-checked + analysis]**

The same argument applies verbatim to §2.3's route 1, one level up.

---

## 4. `HeadReduction.lean`: the measurement, and the verdict

Instrument: forward reachability over the declaration graph reading declaration **values**
(`getUsedConstantsAsSet` with `allowOpaque := true`, so `.thmInfo` bodies are seen), scope =
every `Lean4Lean.*` constant in the closure of `Lean4Lean.Theory` + `Strengthen` +
`HeadRedStuck` + `KCanonical` + `ParamsBuild` (4465 constants). **[measured]**

```
HeadReduction decls: 203, tainted: 21
decls whose STATEMENT mentions IsDefEq/HasType/IsDefEqU/IsType: 66
  of which sorry-free: 45
```

and the 45 are, exhaustively: `WHRed.rec/casesOn/recOn/below.*`, `InferType.rec/casesOn/
recOn/below.*`, sixteen `*.match_1_*` auxiliaries, the constructors `WHRed.extra`,
`InferType.app`, `InferType.lam`, and the three stability lemmas `WHRed.instN`,
`WHRedS.instN`, `StRed.instN`. **[measured]**

**So: no `sorry`-free theorem in `HeadReduction.lean` relates a conversion to a reduction.**
The two that do — `IsDefEq.reduce_sort` (`:470`) and `IsDefEq.reduce_forallE` (`:488`) — both
begin `have ⟨…⟩ := H.church_rosser hΓ`. **[read]**  That is the whole answer to "does
`HeadReduction.lean` help": *the direction strengthening needs is conversion ⟹ joinability,
and the file obtains it only from `church_rosser`.*  This is independent of §0.4's correction:
even if `church_rosser`'s statement were fine, `reduce_forallE`'s conclusion
(`∃ A' B', Γ ⊢ e ⤳* .forallE A' B'`) relates `A' B'` to nothing, which is
`docs/handoff-headreduction.md` §3(a) and still stands **[read]**.

What *is* salvageable is unchanged from that document and worth keeping: `WHRed.determ`,
`WHRedS.determ`, `InferType.determ` and the whole 182-declaration reduction layer are
sorry-free and cost nothing from this corner.

---

## 5. Corrections to the relay this pass was briefed on

| relayed claim | status after this pass |
|---|---|
| "`IsDefEqU.weakN_iff` has 169 users and an empty cone" | **empty cone confirmed**: its forward cone (1614 constants) contains **none** of the other 18 holes. **[measured]**  The user count is scope-dependent: 9 direct / **200** transitive over the 9566-constant scope `Verify/*` + `Theory` + `Strengthen`, counting internal names; 8 / 40 over the smaller `Verify.Soundness` + `Theory` scope.  Quote the scope with the number. |
| "`church_rosser`'s statement is now machine-checked FALSE" | **overstated twice.**  §0.4 and §5.1. |
| "`weakN_iff` ↔ `TypingStrengthening` ↔ `PiDescend`" | **`weakN_iff` ↔ `TypingStrengthening` is *not* in the tree and is not claimed by `Strengthen.lean`.**  What is proved is `Strengthening → TypingStrengthening` and `TypingStrengthening ↔ PiDescend`; the converse of the first is exactly the open direction.  `TypingStrengthening` is the target's *reflexive instance*, strictly weaker as far as anything here shows. |
| "`TransStrengthening` IS the target" | **confirmed**, and now also against the hole's own statement rather than `Strengthening`'s: `StrengtheningTarget.iff_trans`, sorry-free. |
| "no model argument can reach it" | **confirmed and strengthened** to a theorem about the residual (§3). |
| "`HeadReduction.lean` is the only untried reduction relation — assess it" | assessed, §4: it cannot deliver, for a reason internal to the file (its only bridges are `church_rosser` calls) and not dependent on §0.4. |

### 5.1 `not_crStatement_of_kstep`, priced  **[measured]**

* It takes nine hypotheses about the witness (`hstep : KStep …`, `hlam`, `hnp`, `hrig`,
  `hrigA`, `hrigT`, `hne`, plus two `OnCtx`s and two typings).  `KCanonical.lean`'s own
  closing comment says the instance that would satisfy them **does not exist** in this tree,
  because `paramsOfWF`'s `PatWF` is open in exactly its ι and quotient cases, and
  `KStep` is *empty* at the only concrete `Params` (`refParams_no_kstep`). **[read]**
* Its own axiom set is `[propext, sorryAx, Classical.choice, Quot.sound]`, and a forward scan
  of its 3542-constant cone finds exactly one declaration directly containing `sorryAx`:
  **`IsDefEqU.forallE_inv_stratified`**. **[measured]**

So it is a *conditional* refutation relative to `forallE_inv_stratified`, with no witness.
That is still a useful negative — it says a confluence development at a K-registering `Params`
must fail — but it is not "the statement is false", and it must not be cited as one.

---

## 6. Routes attempted across all passes, and the exact step each failed at

| route | failed at |
|---|---|
| direct induction on `IsDefEqU` | `trans`, and `trans` **is** the statement. **[machine-checked]** |
| "prove the typed form instead" | same `trans`; inter-derivable (`Strengthening.iff_typed`). **[machine-checked]** |
| a *propagated* restatement | makes `trans` free, needs a coherence clause whose base case is the target. **[analysis]** |
| Church–Rosser (`ChurchRosser.lean`) | four declarations circular through the `weakN` family; `NormalEq.descend` has three refuted branches; `CRStatement` conditionally refuted. **[measured]** |
| `HeadReduction.lean` | its only conversion⟹reduction bridges are `church_rosser` calls; nothing clean in the file connects the two. **[measured, §4]** |
| model side (`Theory/SetModel/`) | vacuous over an uninhabited entry — now a theorem about the residual. **[machine-checked + analysis]** |
| `VExpr.Skips` / `IsDefEq.skips` | downstream of the hole, not toward it. **[read]** |
| refutation by counterexample | §2.2: five mechanisms traced, all collapse to the crux. **[analysis]** |
| substitution (inhabited entry) | **succeeds**, and now covers the target's general `n`. **[machine-checked]** |
| induction on `HasTypeStrong` (reflexive instance) | **succeeds**; residual `PiDescend`. **[machine-checked]** |
| `OnCtx Γ` from `OnCtx Γ'` inside the development | **succeeds**, non-circularly. **[machine-checked, new]** |

**Do not re-attempt**: a direct conversion induction; the typed form; a model argument;
`skips`; re-deriving `Strengthening` from `TransStrengthening`-shaped residuals; a standalone
`PiDescendNeutral → PiDescend` (a tautology — the `.forallE` head case needs `Strengthening`
itself); or the `_fires`-style tautological witnesses `StrengthenWitness.lean` §2 records.

---

## 7. What to pick up first

1. **§2.3 route 1 — axiom conservativity.**  It is the only reformulation on the table that
   changes the *shape* of the unknown rather than its packaging, and §12 has already cut the
   problem down to a single uninhabited entry, which is exactly what that route consumes.
   Price it before building: the Π-closure lemma is the whole cost.
2. **`PiDescend`** (equivalently the reflexive instance).  Unchanged from the previous pass;
   its case split is `docs/handoff-weakn.md` (previous revision) §2.5, reproduced nowhere else.
   Two of its five cases close from `sort_forallE_inv`; the `.forallE` case needs the target.
3. **Do not** spend time reviving `HeadReduction.lean` (§4) or `ChurchRosser.lean` (§6).
4. **If a fresh refutation attempt is wanted**, the only untried lever is an environment with
   ι-rules — every witness in §2.2 was over δ-only or empty environments, because that is the
   only fragment where `Params` is inhabited unconditionally (`paramsOfDelta`).  A refutation
   does not need `Params` at all, though, so this is not blocked: it needs an `AddInduct`
   environment and the patience to type-check a term by hand.

---

## 8. Files

* `Lean4Lean/Theory/Typing/Strengthen.lean` — **§10, §11, §12 new**, all sorry-free; §1–§9
  unchanged.  755 lines.
* `Lean4Lean/Theory/Typing/StrengthenWitness.lean` — **unchanged**; still builds.  Its §2
  `_fires` theorems are tautologies (its own header says so); quote §3's `_premises` theorems.
* `Lean4Lean/Theory/Typing/UniqueTyping.lean` — **unchanged**; the `sorry` at `:172` stands.
* Measurement scripts for §4 and §5.1 were scratch; the reproducible recipe is in §4's
  instrument paragraph (`scripts/cone-measure.lean`'s `deps` function, seeded differently).
