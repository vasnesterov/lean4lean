# Structure eta: `tryEtaStructCore.WF` and `isDefEqUnitLike.WF`

Stream owning `Lean4Lean/Verify/TypeChecker/{IsDefEq,Basic,Reduce,WHNF}.lean`,
`Verify/{EqSafety,QuotConsts}.lean`.  Tree at `b32b29b` + this stream's edit to
`Verify/TypeChecker/IsDefEq.lean` (no other file touched).

Every claim below is tagged **[checked]** (machine-checked this session, command given) or
**[source]** (read off the source, not machine-checked).  Nothing is tagged from memory.

---

## Bottom line

1. **One new proved theorem, non-vacuous**: `isDefEqUnitLike.WF_prop` — the `Prop` half of
   `isDefEqUnitLike.WF`, proved *without* the dead `.inductInfo` gate, so it is a component of
   the eventual real proof rather than a placeholder.  Plus its natural-hypothesis corollary
   `isDefEqUnitLike.WF_proof`.  **[checked]**
2. **Neither hole is false, and neither has an under-constrained quantifier.**  Both are
   *vacuously true today* (the two `*_never_true` witnesses), and both would become false the
   moment `AddInduct` gains constructors *unless* the spec gains `structEta`.  No witness of
   falsity can be exhibited today, and the reason is structural, not effort. §4.
3. **The unique-typing re-test paid off, but not where the relay expected.**  Neither hole was
   blocked *on* unique typing for its structure-eta content.  But the *plumbing* of both is
   gated on it through `inferType.WF`, and that gate went from the whole injectivity family to
   the single hole `IsDefEqU.forallE_inv_stratified`.  That is what made §2's theorem
   worth writing now instead of later. §3.
4. **`tryEtaStructCore`'s Prop half does *not* go through, and the failing step is exact**: the
   `for` loop's `isDefEq (.proj I (i - np) t) args[i]` needs `c.TrExprS (.proj …) _`, hence a
   `TrProj`, hence `env.IsStructure I …`, obtainable only from the gate `TrEnv'` refutes.  The
   residual goal is transcribed verbatim in §5. **[checked]**
5. **Sharpened dependency separation** (correcting `docs/research-structeta.md` §5): at zero
   fields the parameter lists never have to be compared, because `s` can be transported to
   `t`'s type; at `n > 0` fields they do not have to be compared *either*, provided the
   `TrProj` is built at `s`'s parameters.  So **neither hole needs const-application
   injectivity** — `tryEtaStructCore` needs `TrProj.wf`-style *construction*, which is a
   different thing from `TrProj.uniq`. §6. **[source]**

Census unchanged at **20**; this stream's file still holds exactly its two, by name. **[checked]**

---

## 1. Inventory

| | `tryEtaStructCore.WF` | `isDefEqUnitLike.WF` |
|---|---|---|
| file | `Verify/TypeChecker/IsDefEq.lean` | same |
| status | `sorry` | `sorry` |
| vacuity witness | `tryEtaStructCore_never_true` | `isDefEqUnitLike_never_true` |
| witness sorry-free? | **yes** | **no** (borrows `inferType.WF`'s cone) |
| Prop half | **blocked**, §5 | **proved**, §2 |
| still needs | `structEta`; `TrProj` construction; AddInduct bridge | `structEta` at zero fields; AddInduct bridge |

Statements, verbatim:

```lean
theorem tryEtaStructCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := sorry

theorem isDefEqUnitLike.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := sorry
```

---

## 2. What closed: the `Prop` half of `isDefEqUnitLike`  **[checked]**

`docs/research-structeta.md` §2 observed that neither check tests the structure's level, so both
fire on `Prop` structures where `IsDefEq.proofIrrel` — an existing spec rule — already settles
the case, and tabulated the split.  That table was never machine-checked.  It is now, for the
zero-field column:

```lean
theorem isDefEqUnitLike.WF_prop {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hprop : ∀ A, c.HasType e₁' A → c.HasType A (.sort .zero)) :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂'

theorem isDefEqUnitLike.WF_proof {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hA : c.HasType e₁' A) (hAp : c.HasType A (.sort .zero)) :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂'
```

**Why this is not the vacuous close in disguise.**  `isDefEqUnitLike_never_true` kills the
branch with `TrEnv.not_inductInfo`.  `WF_prop` does the opposite: it `split`s at each of the
four gates, discharges the `return false` arms with `nofun`, and **enters** the
`.inductInfo`/`.ctorInfo` arm, taking its conclusion from the trailing
`isDefEqCore tType (← inferType s)` and `proofIrrel` alone.  Nothing in the proof mentions
`AddInduct`, `not_inductInfo`, or any `TrEnv'` shape lemma, so it survives the AddInduct flip
verbatim.  That is the acceptance test that matters here: it is a *component* of the eventual
proof, and the only thing left in its column is the non-`Prop` case.

**Non-vacuity.**  The hypothesis is used at a real instance: `hprop` is applied to the type
`inferType.WF` actually hands back, with the `HasType` derivation in hand, inside the branch
where the function returns `isDefEqCore …`.  `WF_proof` further shows the hypothesis is implied
by the manifestly satisfiable "`e₁'` inhabits some proposition", so it is not a disguised
`False`.  What is *not* available is a firing at a concrete `VContext` whose environment holds a
unit-like structure — no such `VContext` exists, because `AddInduct` has no constructors; that
is the same wall as everything else in §4, not a gap in this theorem.

---

## 3. The unique-typing re-test  **[checked]**

Measured with a transitive `getUsedConstantsAsSet` sweep against the 20 census holes
(script: `scratchpad/deps.lean`, reproduced below), plus `#print axioms`:

| declaration | census holes in its cone |
|---|---|
| `VEnv.IsDefEq.uniq` | `{forallE_inv_stratified}` |
| `VEnv.IsDefEqU.sort_inv` | `{forallE_inv_stratified}` |
| `TrProj.defeqDFC` | `{forallE_inv_stratified}` |
| `TypeChecker.Inner.inferType.WF` | `{forallE_inv_stratified, TrProj.uniq, TrProj.wf}` |
| `isDefEqUnitLike_never_true` | `{forallE_inv_stratified, TrProj.uniq, TrProj.wf}` |
| `isDefEqUnitLike.WF_prop` | `{forallE_inv_stratified, TrProj.uniq, TrProj.wf}` |
| `isDefEqUnitLike.WF_proof` | `{forallE_inv_stratified, TrProj.uniq, TrProj.wf}` |
| `tryEtaStructCore_never_true` | `{}` — sorry-free |

Three things follow, and the first two correct the relay.

* **`sort_inv` is proved but not sorry-free.**  `#print axioms Lean4Lean.VEnv.IsDefEqU.sort_inv`
  reports `sorryAx`.  "Proved" here means *reduced to `forallE_inv_stratified`*, which is still
  a `sorry` in `Theory/Typing/Injectivity.lean`.  Anything built on `sort_inv`, `SortUniq`,
  `IsDefEq.uniq`, `piUniq` inherits that.  Worth saying plainly because a reader of the relay
  could reasonably conclude the unique-typing corner is clean; it is one hole, not zero.
* **Neither of this stream's holes was ever waiting on unique typing for its *content*.**  The
  missing ingredient is `structEta`, a `VEnv.IsDefEq` constructor.  Unique typing does not
  supply it and never could.
* **But the *plumbing* of both is gated on unique typing**, through `inferType.WF`'s single
  appeal to `TrExprS.uniq`/`IsDefEq.uniq` (whose `.proj` case is `TrProj.uniq`).  That gate
  shrank from the whole injectivity family to one named hole.  `WF_prop` inherits exactly
  `inferType.WF`'s three and adds none of its own — which is the useful measurement: **the
  `Prop` half of `isDefEqUnitLike` costs no structure-eta content at all.**

Reproduce:

```
lake build Lean4Lean.Verify.TypeChecker.IsDefEq
lake env lean scripts/sorry-census.lean          # 20
```
and for the cone table, a `run_cmd` walking `ConstantInfo.value?` (with the `.thmInfo` trap
handled as `scripts/sorry-census.lean` does) and intersecting with the 20 hole names.

---

## 4. Scope audit: **neither statement is false, and neither is under-constrained**

The defect being hunted is the one that made `NormalEq.descend` false — a quantifier ranging
over more than intended, with no registration hypothesis tying it down.  Checklist run against
both statements:

| check | `tryEtaStructCore.WF` | `isDefEqUnitLike.WF` |
|---|---|---|
| every auto-bound implicit (`e₁ e₂ e₁' e₂'`) constrained by a hypothesis | ✓ | ✓ |
| argument order matches the implementation (`t := e₁`, `s := e₂`) | ✓ | ✓ |
| conclusion polarity (`b → …` / `b = .true → …`) matches the `Bool` returned | ✓ | ✓ |
| no missing `MLCWF`/`withMLC` (neither function extends the local context) | ✓ | ✓ |
| `VState` universally quantified, as in every sibling | ✓ | ✓ |

The implicit-binder check is **[checked]**, not eyeballed: an experimental partial proof
(§5) put the elaborated context on screen, and it contains exactly
`e₁ e₁' e₂ e₂' c s he₁ he₂` — no stray auto-bound variable.

**Truth today.**  Both are *vacuously true*, machine-witnessed by `tryEtaStructCore_never_true`
and `isDefEqUnitLike_never_true`: `AddInduct` (`Verify/Environment/Basic.lean`) still has no
constructors, `TrEnv'.induct` cannot fire, and both checks are gated behind a constant-map
lookup that `TrEnv.not_ctorInfo` / `TrEnv.not_inductInfo` forbid. **[checked]**

**Truth after the flip.**  Both would be **false** as stated, unless `VEnv.IsDefEq` gains a
`structEta` constructor.  This is stated as a claim, not a result: **[source]**

* Surjective pairing `t ≡ mk ps (proj₀ t) … (projₙ₋₁ t)` for a *variable* `t` is not among the
  13 constructors (`bvar symm trans sortDF constDF appDF lamDF forallEDF defeqDF beta eta
  proofIrrel extra`); `beta`/`eta` need a λ, and `extra`'s ι-rules fire only at a constructor
  application.  At zero fields the same holds for `t ≡ u ps`.
* **Why this cannot be machine-refuted today, and it is not for lack of trying.**  A refutation
  needs a countermodel.  The set model (`Theory/SetModel/`) *validates* struct-eta — a unit-like
  inductive is interpreted as a singleton — so it cannot separate `bvar 0` from `u`.  The only
  other route is syntactic: Church–Rosser / normalisation, i.e. "two distinct rigid normal forms
  are not convertible".  That machinery is `Theory/Typing/ChurchRosser.lean`, whose
  `NormalEq.descend` is itself a `sorry` *and was reported false this session*
  (`Theory/Typing/DescendRefute.lean`; reported by the orchestrator, not re-verified here).  So the refutation
  is blocked on a hole that is worse off than these two.  `docs/research-structeta.md` §3
  reached the same conclusion independently; this is a confirmation, not a new result.

The practical consequence: **do not read "no witness of falsity" as evidence of truth here.**
The two statements are open-or-false, and which one is settled entirely by whether `structEta`
lands in the spec before `AddInduct` lands in `Verify/`.

---

## 5. `tryEtaStructCore`: the exact failing step  **[checked]**

An experimental `tryEtaStructCore.WF_prop` (the `Prop`-hypothesis analogue of §2's theorem) was
written and elaborated.  Everything up to and including
`unless ← isDefEq (← inferType t) (← inferType s)` goes through: the four gates `split` cleanly,
`inferType.WF` fires on both sides, `isDefEq.WF` fires, and `proofIrrel` yields
`key : c.IsDefEqU e₁' e₂'` — the conclusion, in hand, with the loop not yet run.

It then stops, at exactly one goal (transcribed from the elaborator, `mkInfo` renamed for
readability):

```
key : c.IsDefEqU e₁' e₂'
⊢ RecM.WF c s'
    (let args := e₂.getAppArgs;
     do let __s ← forIn' [mkInfo.numParams:args.size] (none, ()) fun i h __s => do
          let __do_lift ← isDefEq (Expr.proj mkInfo.induct (i - mkInfo.numParams) e₁) args[i]
          if __do_lift = true then pure (ForInStep.yield (none, ()))
                               else pure (ForInStep.done (some false, ()))
        match (__s : Option Bool × Unit).fst with
        | some r => pure r
        | none   => pure true)
    fun b _ => b = true → c.IsDefEqU e₁' e₂'
```

**Why having `key` already does not finish it.**  `M.WF` is not just a postcondition: unfolding
(`Verify/TypeChecker/Basic.lean:278`) it also demands that the *resulting* `VState` satisfy
`vs'.WF c` and `vs ≤ vs'`.  So even with the postcondition trivially true, the loop must be shown
to preserve the state invariant, and the only lemma that does that for an `isDefEq` call is
`Methods.WF.isDefEqCore`, whose hypotheses are `c.TrExprS e₁ e₁'` and `c.TrExprS e₂ e₂'`.
For the first argument that is `c.TrExprS (.proj I (i - np) e₁) _`, i.e. a
`TrProj c.venv _ c.vlctx.toCtx I k e₁' _`, and `TrProj.mk` (`Verify/Typing/Expr.lean:81`) opens
with `env.IsStructure S D T C`.  The only source of `IsStructure` for a name the *kernel*
environment calls a structure is the AddInduct bridge, which does not exist.

**So the exact failing step is:** *supply `c.venv.IsStructure I D T C` from
`c.env.isNonRecStructure I = true`.*  Nothing before it fails, and nothing after it has been
attempted.  This is a one-line summary of a machine-checked goal, not an estimate.

The experiment was **removed** from the file — it needed a `sorry` — and is recorded here
instead.  Re-creating it is ~18 lines and takes minutes; the recipe is §2's proof with the
gate splits reordered and `he₂`'s head used instead of `he₁`'s type.

---

## 6. Correction to `research-structeta.md` §5: neither hole needs injectivity  **[source]**

`research-structeta.md` §5 schedules `tryEtaStructCore.WF` behind `TrProj.uniq`, and
`TrProj.uniq`'s own docstring is blocked on const-application injectivity
(`IsDefEqU.const_app_inv`).  The transitive reading — "structure eta needs injectivity" — is
**wrong**, for a reason worth writing down because it changes the schedule:

* The check establishes `inferType t ≡ inferType s`, i.e. `S ps' ≡ S ps` where `ps'` are `t`'s
  parameters and `ps` are `s`'s.  Naively, concluding `t ≡ s` from
  `t ≡ mk ps' (proj^{ps'} t)` and `s = mk ps args` needs `ps' ≡ ps`, which *is* `const_app_inv`.
* But `TrProj.mk` reads its parameter list off a `HasType` premise, **not** off a syntactic
  type: `env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ ιs))`.  Since
  `S ps' ≡ S ps` is in hand, `HasType t (S ps)` follows by `defeqU_r`, and the `TrProj` for
  `.proj I i t` may simply be **built at `ps`**, `s`'s parameters.  Then `structEta` at type
  `S ps` gives `t ≡ mk ps (proj^{ps} t)`, congruence with `s = mk ps args` needs only the
  field comparisons the check already performed, and the parameter lists are never compared.
* At zero fields (`isDefEqUnitLike`) the same move is even shorter: transport `s` to `t`'s type
  and apply zero-field `structEta` to both.

So what `tryEtaStructCore.WF` needs from the `TrProj` family is **construction**
(`TrProj.wf`-shaped: build a `TrProj` from a `HasType` plus `IsStructure`), not **uniqueness**.
`TrProj.uniq` still appears in its cone, but only borrowed through `inferType.WF`, exactly as it
does for `isDefEqUnitLike` — which `research-structeta.md` §5 lists as *not* blocked on `TrProj`
at all.  Both are blocked on it to the same (borrowed) degree, and neither is blocked on it for
structure-eta reasons.

I got this wrong once mid-session before checking `TrProj.mk`'s premise; recording the wrong
version and the fix so the next reader does not have to re-derive it.

---

## 7. C++ conformance, and two proposed `divergences.md` entries  **[source]**

Both checks were re-read gate-for-gate against `~/lean4/src/kernel/type_checker.cpp`
(`try_eta_struct_core` `:889`, `is_def_eq_unit_like` `:1159`) and
`~/lean4/src/kernel/inductive.cpp` (`is_non_rec_structure` `:28`).  The gate *sequences* agree,
including the fact — load-bearing for §4 — that **neither C++ function tests the structure's
universe**, so both fire on `Prop` structures.

Two differences, both unreachable in a kernel-accepted environment, neither currently in
`divergences.md`.  I have **not** edited `divergences.md` (not this stream's file); proposed
text:

* `isDefEqUnitLike`: C++ writes `env().get(ctor_name).to_constructor_val()`, which raises a
  kernel exception if the inductive's sole listed constructor name does not resolve to a
  constructor.  lean4lean writes `let .ctorInfo { numFields := 0, .. } ← env.get c | return
  false`, folding "not a constructor" together with "has fields" into a `false`.  Reachable only
  if a `.inductInfo` lists a constructor name that is not a `.ctorInfo`, which
  `Environment.addInductive` cannot produce.
* `tryEtaStructCore`: C++'s `is_non_rec_structure` calls `env.get(decl_name)` (throws on an
  unknown name); lean4lean's `Environment.isNonRecStructure` uses `find?` and returns `false`.
  Reachable only if a `.ctorInfo`'s `induct` field names a constant not in the environment.

Both are in the same class as the existing `unreachable!` entry: lean4lean rejects-or-declines
where C++ throws, on inputs neither can be handed.

**Kernel Arena was not run**: this stream changed no executable code — the only edited file is
`Verify/TypeChecker/IsDefEq.lean`, which contains theorems only, and the two additions are
theorems with no `@[implemented_by]`, no `partial`, and no effect on `Lean4Lean.addDecl`'s cone.
The baseline to hold remains 185 correct / 6 either / 0 incorrect.

---

## 8. What to pick up first

Ordered by ratio of unblocked content to cost.

1. **`structEta` in `Theory/Typing/Basic.lean`** — still the single largest unplanned item, and
   still the only thing that makes either hole *have* content.  `docs/design-inductive.md:724–765`
   carries the design; §4 above and `research-structeta.md` §2 carry the correction it needs
   (the proposed `IsNeverZero` side condition is wrong for these two call sites, which fire on
   `Prop` structures; either drop it or pair the rule with a `proofIrrel` branch — §2's theorem
   is that branch, for the zero-field case, already written).
2. **The AddInduct bridge**, in the specific shape §5 names:
   `c.env.isNonRecStructure I = true → ∃ D T C, c.venv.IsStructure I D T C` (plus the level and
   parameter side conditions `TrProj.mk` wants).  This single lemma is what unblocks
   `tryEtaStructCore`'s loop, and it is also what `inferProj.WF` and `reduceProjCore.WF` need.
   It cannot be written before `AddInduct` gains constructors.
3. **`IsDefEqU.forallE_inv_stratified`** — one hole standing between `inferType.WF` (and hence
   §2's theorem, and hence most of `Verify/TypeChecker/`) and a clean unique-typing cone.  Not
   this stream's, but it is the highest-leverage single name in the census for this corner.
4. **Do not** close either hole vacuously, and **do not** weaken or build on
   `tryEtaStructCore_never_true` / `isDefEqUnitLike_never_true`.  They are two of the nine
   placeholder statements the standing ruling keeps live precisely so that the ι-reduction,
   projection-reduction and structure-eta obligations stay visible as theorems.  Note the
   asymmetry recorded in §1: the `tryEtaStructCore` witness is sorry-free and the
   `isDefEqUnitLike` one is not, so they will not go red together.
