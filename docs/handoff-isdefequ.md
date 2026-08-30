# The `IsDefEqU'` enlargement (`docs/backward-analysis.md` §5): designed, prototyped, measured

**Verdict, first.** The claim §5 makes —

> With (E), `sort_inv` and `forallE_inv_stratified` leave `kernel_sound`'s cone entirely:
> 174 declarations' worth of dependence becomes four constructors.

— is **false**, and the measurement is not close. In `kernel_sound`'s own closure the
enlargement removes **62 of 235** transitive users of `IsDefEqU.sort_inv` (26%); the residue
still reaches `Bridge.not_leanTTConsistent_of_kernel_proves_false`. `IsDefEq.uniq` stays,
`forallE_inv_stratified` stays, and `IsDefEqU.forallE_inv` is untouched (69 users before,
69 after). **[measured]**

Two further results, both new and both more useful than the headline:

1. **(E) is exactly half of a cut that does work.** The minimal set that takes `sort_inv` out
   of the goal's cone is **(E) together with `HasType.piUniq` and `IsDefEq.weakN_iff'`** —
   three items, and all three are necessary: dropping any one leaves the cone reaching the
   goal. Cutting the residual sites *without* (E) leaves 200 users and still reaches the
   goal. So (E) is a necessary half of a two-step plan, not a plan. **[measured]**
2. **The in-place version of (E) trades a proved `uniq` for an unproved one.** Adding the
   rule to `Basic.lean`'s `IsDefEq` forces matching constructors down the
   `IsDefEqStrong` → `HasTypeStrong` → `HasTypeStratified` chain, and so adds a case to
   `IsDefEq.uniq`'s own induction whose obligation is `UniqAcross` — which is
   **`uniq` again**, machine-checked in both directions
   (`Enlarged.uniqAcross`, `Enlarged.uniqU_of_uniqAcross`). The collapse test fails.
   **[machine-checked]**

Files added by this stream, both green and both `sorry`-free:
`Lean4Lean/Theory/Typing/Enlarged.lean`, `Lean4Lean/Theory/Typing/EnlargedModel.lean`.
Nothing outside them was edited. `scripts/sorry-census.lean` total unchanged at **19**.

---

## 1. The enlargement, stated — and the correction to §5's statement of it

§5's literal proposal is

> **(E, literal)** replace `IsDefEqU` by the reflexive/symmetric/transitive **closure** of
> `fun e₁ e₂ => ∃ A, IsDefEq Γ e₁ e₂ A`, and change the conversion rule from
> `Γ ⊢ A ≡ B : .sort u → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ ≡ e₂ : B`
> to `IsDefEqU' Γ A B → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ ≡ e₂ : B`.

**That form loses regularity, and loses it in a circle.** `IsDefEq.isType'`
(`Theory/Typing/Lemmas.lean:869`) discharges its `defeqDF` case with `⟨_, h1.hasType.2⟩` —
it reads `IsType Γ B` straight off the `.sort u` index of the conversion premise. Delete
that index and the case can only be closed by `IsType.defeqU_l`, which is **one of the twelve
lemmas (E) exists to make free**. An enlargement whose own regularity proof needs a member of
the family it is enlarging to discharge is not usable. **[read]**

The repair is the one the brief's own datum predicts — *carry the typing premise on the rule
instead of inverting it*. The enlargement prototyped is therefore

> **(R)** add to `IsDefEq` the single rule
> ```
> retype : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ : B → Γ ⊢ e₁ ≡ e₂ : B
> ```

`Theory/Typing/Enlarged.lean` defines `IsDefEqE` = `IsDefEq` + `retype` and proves
`IsDefEq.toE`. Nothing in `Basic.lean` was touched.

**Why (R) is the right shape.** `retype` is composition-at-different-types as a rule: it
re-indexes an equation at any *other* type of its left endpoint. Every one of the twelve
`(E)`-family lemmas is an instance. Because the second premise is a full derivation, an
induction that needs a fact about `B` gets it from the second induction hypothesis — that is
what fixes regularity, and it is the whole of the difference from (E, literal).

### 1.1 What is free under (R) — machine-checked, `axioms = [propext]`

Ten of the twelve, with **no `VEnv.WF`, no `OnCtx`, no `uniq`** (compare
`Theory/Typing/UniqueTyping.lean:117–170`, where every one takes `henv`, `hΓ` and goes
through `IsDefEq.uniq`):

`IsDefEqE.trans_l`, `.trans_r`, `.transU_l`, `.transU_r`, `IsDefEqUE.of_l`, `.of_r`,
`.trans`, `HasTypeE.defeqU_l`, `IsTypeE.defeqU_l`, `isDefEqE_iff`.

The two exceptions, `IsDefEqUE.defeqDF` and `HasTypeE.defeqU_r`, convert along a conversion
between *types*, so they need `IsTypeE Γ A` — regularity, and nothing else. They are stated
with that hypothesis explicit rather than hidden inside an `henv`.

Note `IsTypeE.defeqU_l` is free: `IsTypeE Γ A₁` **is** a typing of the equation's left
endpoint, so `retype` applies directly. That is the circle of §1 cut.

### 1.2 Conservativity, and what "safe" means here

`IsDefEqE.toIsDefEq` (machine-checked): given `IsDefEq.uniq`, `IsDefEqE` collapses to
`IsDefEq`; `isDefEqE_iff_isDefEq` packages the equivalence. Consequences, stated because the
brief asked for the argument rather than the assertion:

* **The enlargement is the safe direction for soundness.** It admits more conversions, so
  the refinement obligation (checker accepts ⟹ `TrEnv` + `VEnv.WF`) gets *weaker* and the
  model's obligation gets *stronger*. `VEnv.WF`, `VConstant.WF` and `VDefEq.WF` are all
  conjunctions of `HasType` facts in **positive** position, so enlarging `IsDefEq` cannot
  make any of them harder to establish.
* **The polarity check.** `HasType` does appear in negative position in `Verify/` — every
  lemma that *inverts* a `TrExprS`-carried typing has one as a premise, and those get harder,
  not easier. That cost is real and is priced in §4: it is one case per induction, and the
  case is mechanical because `retype` does not move the endpoints.
* **The model owes nothing new that it does not already owe for `uniq`** — but that is a
  weaker statement than "model-neutral", because the *collapse itself* consumes `uniq`. See
  §5 for what the model owes for the rule directly, which is genuinely nothing.
* **Non-vacuity, and its ceiling.** `retype_fires` fires the rule at `CycleConv.propLoopEnv`
  — proved `VEnv.WF`, provably non-terminating head reduction (`propLoop_headStep_not_wf`) —
  on an instance whose two type indices, `.const `A []` and `.const `B []`, are
  syntactically distinct terms. That is the strongest witness available: conservativity
  *proves* the enlargement is not strict given `uniq`, so no witness can show `IsDefEqE`
  deriving something `IsDefEq` does not. Whether it is strict when `uniq` fails is open and
  not claimed.

---

## 2. The measurement **[measured]**

Instrument: a transitive `getUsedConstantsAsSet` fixpoint over `env.constants`, with the
`.thmInfo` trap handled (`ConstantInfo.value? (allowOpaque := true)`), internal names
included. Source in the appendix; it is `scripts/cone-measure.lean` re-aimed at
`kernel_sound`'s own scope.

**Scope K** = the import closure of `Verify/Bridge.lean` = 92 `Lean4Lean` modules,
**13 339 source declarations**. This is the set of declarations `kernel_sound` can use.
`Verify/Primitive.lean` **is** in it (via `Environment/Extension` → `Environment/Checker` →
`Environment/Boundaries`); `Theory/Typing/ChurchRosser.lean` is not.

"Reaches the goal" below means: is a transitive user that includes
`Bridge.not_leanTTConsistent_of_kernel_proves_false`.

### 2.1 Baseline

| statement | transitive users | direct consumers |
|---|---|---|
| `IsDefEqU.sort_inv` | 235 | 1 — `IsDefEq.uniq` |
| `IsDefEqU.forallE_inv_stratified` | 252 | 2 — `IsDefEq.uniq`, `piInvStrat_axiom` |
| `IsDefEqU.forallE_inv` | 69 | 2 — `HasType.piUniq`, `piInv_axiom` |
| `IsDefEq.uniq` | 234 | 5 — `prim_domain_nat`, `trans_l`, `trans_r`, `uniqU`, `isDefEq_iff` |
| `IsDefEq.uniqU` | 170 | 3 — `isDefEqUnitLike.WF_proof`, `HasType.piUniq`, `IsDefEq.weakN_iff'` |
| `HasType.piUniq` | 66 | 3 — `TrExpr.beta`, `inferApp.loop.WF._f`, `VExpr.WF.app_arg_typed` |
| `IsDefEq.weakN_iff'` | 164 | 2 — `OnCtx.weakN_inv`, `IsDefEq.weakN_iff` |
| `TypeChecker.prim_domain_nat` | **0** | — |

### 2.2 Before and after, seed `IsDefEqU.sort_inv`

The "(E) cut" removes the twelve `(E)`-family declarations as edges — justified by §1.1,
where ten are proved free outright and two are free given regularity.

| cut | users | reaches the goal |
|---|---|---|
| none | **235** | yes |
| (E) | **173** | **yes** |
| (E) + `piUniq` | 168 | yes |
| (E) + `weakN_iff'` | 71 | yes |
| (E) + `isDefEqUnitLike.WF_proof` | 172 | yes |
| (E) + `prim_domain_nat` | 172 | yes |
| (E) + `piUniq` + `weakN_iff'` | **4** | **no** |
| (E) + all four residual sites | 2 | no |
| all four residual sites, **no** (E) | **200** | **yes** |

Seed `forallE_inv_stratified`: 252 → 190 under (E) → 21 under (E)+`piUniq`+`weakN_iff'` → 17
under the full cut, and at 17 it no longer reaches the goal. Those 17 are all inside
`Theory/Typing/Injectivity.lean` itself (`piInvStrat_axiom`, `WF.sortUniq'`, `IsProof.*`,
the four dead `const_*`/`sort_forallE` inversions, …).

Seed `forallE_inv`: **69 under every cut that includes (E)** — the enlargement does not touch
it, exactly as §5 itself says.

### 2.3 Reading the table

* **(E) alone fails.** 173 declarations, still reaching the goal.
* **(E) is necessary.** The last row: cutting all four residual `uniq` sites without (E)
  leaves *more* users (200) than (E) alone does. The two halves are independent.
* **The live residue is two sites, not four.** `prim_domain_nat` has **zero** transitive
  users, and `isDefEqUnitLike.WF_proof`'s cone does not reach the Bridge export. Cutting only
  `piUniq` and `weakN_iff'` on top of (E) already disconnects `sort_inv` from the goal.
* **`weakN_iff'` is the elephant**: it alone carries 102 of (E)'s 173 survivors.

### 2.4 Why none of the four residual sites is composition

This is the structural reason (E) cannot reach them. Each uses `uniq` to relate **two types
of one term**, which `retype` does not do — `retype` re-indexes an equation, it does not
compare two indices. **[read]**

| site | file | what it actually needs |
|---|---|---|
| `HasType.piUniq` | `Verify/Typing/Lemmas.lean` | unique typing **at Π types**: two Π types of one term have convertible domains and codomains |
| `IsDefEq.weakN_iff'` | `Theory/Typing/UniqueTyping.lean:190` | unique typing across a weakening; **also** blocked on the `sorry` in `IsDefEqU.weakN_iff` |
| `isDefEqUnitLike.WF_proof` | `Verify/TypeChecker/IsDefEq.lean:912` | **`PropUniq`** — "some type of `e` is a `Prop`" ⟹ "this type of `e` is a `Prop`" |
| `prim_domain_nat` | `Verify/Primitive.lean` | unique typing at `.natLit n`, against `.nat` |

The third row is worth relaying to whoever is running `docs/backward-analysis.md` §6: it is a
`PropUniq` consumer, not a full-`uniq` consumer, and §6's argument (`hfalse` + `PropTypeAgree`
⟹ `PropUniq`) would discharge it. It is not on the (E) route at all.

---

## 3. The debit side: the in-place migration breaks `uniq`'s proof **[read + machine-checked]**

Adding `retype` to `Basic.lean`'s `IsDefEq` propagates:

1. `IsDefEq.strong`'s new case has `IsDefEqStrong Γ e₁ e₂ A` and `IsDefEqStrong Γ e₁ e₁ B`
   and must produce `IsDefEqStrong Γ e₁ e₂ B`. `IsDefEqStrong.defeqDF` wants
   `Γ ⊢ A ≡ B : .sort u`. **So `IsDefEqStrong` needs a `retype` constructor.**
2. `IsDefEqStrong.hasType'` (`Strong.lean:829`) must then produce `HasTypeStrong Γ e₂ B` from
   `HasTypeStrong Γ e₂ A` and `HasTypeStrong Γ e₁ B`; `HasTypeStrong.defeq` wants the same
   conversion. **So `HasTypeStrong` needs one, and `HasTypeStratified` after it.**
3. `IsDefEq.uniq` (`UniqueTyping.lean:13`) inducts on `HasTypeStratified`. Its new case has a
   node typing `e₂` and a premise typing `e₁` — **two different terms**, so the induction
   hypothesis does not apply.

The obligation that case creates is written out and named in `Enlarged.lean`:

```lean
def UniqAcross (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ e₁ e₂ A₀ A B}, OnCtx Γ (env.IsType U) → env.IsDefEq U Γ e₁ e₂ A₀ →
    env.HasType U Γ e₁ A → env.HasType U Γ e₂ B → env.IsDefEqU U Γ A B
```

and both directions are machine-checked:

* `uniqAcross` — `UniqAcross` follows from `uniq` (so it is not a *new* mathematical fact);
* `uniqU_of_uniqAcross` — **`UniqAcross` implies `uniqU`**, by taking the conversion to be
  the first typing itself. `axioms = [propext]`; no `uniq`, no `sorry`.

**That is the collapse test, and it fails**: the residual's quantifiers instantiate so its
premises degenerate into the target's. An in-place `retype` would move `IsDefEq.uniq` from
*proved (modulo one `sorry`-backed input)* to *open*, while — per §2 — leaving it in the
cone. It is a strict regression.

The parallel-relation form prototyped here does **not** have this problem, because the base
relation is untouched and `uniq`'s stratified induction runs on it unchanged. But then the
collapse `IsDefEqE → IsDefEq` consumes `uniq` at every boundary, and every statement in
`Verify/` is about `IsDefEq`. **Neither form of the enlargement escapes.**

---

## 4. The migration price **[measured]**

Instrument: count declarations whose type-or-value mentions each eliminator. Scope: every
`Theory/Typing/*.lean` plus the `Verify/Bridge.lean` closure.

| eliminator | declarations | where |
|---|---|---|
| `VEnv.IsDefEq.rec` | 22 (21 pre-existing) | `Lemmas` 9, `Basic` 3, `ConstSubst` 2, `Strong` 2, `ChurchRosser` 1, `Strengthen` 1, `CycleConv` 1, `RawDefEq` 1, `SetModel/Consts` 1, `Enlarged` 1 (this stream's) |
| `VEnv.IsDefEqStrong.rec` | 20 | `Strong` 13, `Injectivity` 5, `Stratified` 1, `SetModel/SoundInduction` 1 |
| `VEnv.HasTypeStrong.rec` | 14 | `Strong` 9, `HeadReduction` 1, `Strengthen` 1, `NotProof` 1, `UnivDiscrim` 1, `SortUniq` 1 |
| `VEnv.HasTypeStratified.rec` | 10 | `Strong` 8, `UniqueTyping` 1, `Injectivity` 1 |

**65 pre-existing induction sites**, and **zero of them are in `Verify/`.** The migration is
entirely inside `Theory/`, and the `Verify/` side needs no edit at all if the twelve
`(E)`-family lemmas keep their current signatures (with `henv`/`hΓ` becoming unused
arguments) and only their proofs change.

By owner:

* **`Theory/Typing/Strong.lean` — 32 of 65 (this stream owns it).**
* `Theory/Typing/Lemmas.lean` — 9, plus the one-line `isType'` patch
  (`| retype _ _ ih1 ih2 => exact ih2 hΓ`). Not this stream's.
* `Theory/Typing/Basic.lean` — 3, plus the constructor itself. Not this stream's.
* `Theory/Typing/Injectivity.lean` — 6. Not this stream's.
* `Theory/Typing/UniqueTyping.lean` — 1 (`uniq`), the one that **does not close** (§3).
* `Theory/SetModel/` — 2, both mechanical (§5). Read-only to this stream.
* twelve scattered singletons in `ConstSubst`, `Strengthen`, `ChurchRosser`, `CycleConv`,
  `RawDefEq`, `HeadReduction`, `NotProof`, `UnivDiscrim`, `SortUniq`.

Every case except `uniq`'s is mechanical, for one structural reason: **`retype` does not move
the endpoints, only the type index.** A congruence induction rebuilds the rule from its two
IHs; an inversion keyed on an endpoint's shape returns the first IH, exactly as it already
does for `defeqDF` (`Injectivity.lean:836`, `| defeqDF _ _ _ _ ih => exact ih`). Both shapes
are exercised in `Enlarged.lean` rather than asserted: `IsDefEqE.mono` (congruence, all 15
cases) and `loop_conv_collapseE` (endpoint-sensitive — its `extra` case must still inspect
both sides; its `retype` case is one line).

**No tree-wide edit was attempted, and none is recommended** — §3 says the destination is
worse than the origin.

---

## 5. The model side **[machine-checked]**

`Theory/SetModel/` was **not edited**; `Theory/Typing/EnlargedModel.lean` imports it and
proves the case the induction would have to discharge.

`SoundInduction.lean` runs on `IsDefEqStrong` and carries
`Sound Γ e₁ e₂ A = ⟨eq : ⟦e₁⟧ρ = ⟦e₂⟧ρ, type : ⟦e₁⟧ρ ∈ ⟦A⟧ρ⟩` under an `Above` threshold. The
`retype` case is:

```lean
theorem retype_sound (h₁ : Sound M L Γ e₁ e₂ A) (h₂ : Sound M L Γ e₁ e₁ B) :
    Sound M L Γ e₁ e₂ B where
  eq := h₁.eq
  type := h₂.type
```

— a **re-pairing of the two induction hypotheses**: part 4 from the first premise, part 3
from the second. No side condition, no `PropSplit` field, no `IsProp`/`IsProof` decision, and
no new threshold beyond `Above.and` (`retype_soundAbove`). It joins `Sound.symm` as a case
that is pure bookkeeping. `defeqDF_sound'` is proved alongside it so the contrast is visible:
`defeqDF` must *transport* part 3 along part 4 for the types; `retype` does not, because its
second premise already supplies part 3 at the target.

So **§5's "the enlargement is model-neutral" is confirmed, for (R), and is now
machine-checked rather than analysis.** What it does not confirm is §5's conclusion, because
the cost is not on the model side at all — it is §3.

Note this also settles the model side for the *stronger* rule someone will be tempted by
next. A rule "two types of one term are convertible" (i.e. `uniq` as a rule) would owe the
model `⟦A⟧ρ = ⟦B⟧ρ` from `⟦e⟧ρ ∈ ⟦A⟧ρ` and `⟦e⟧ρ ∈ ⟦B⟧ρ` alone — semantic unique typing,
which is not a bookkeeping case and is not obviously true in the set model. **[read]** That
is the difference between (R) and the thing that would actually reach the four residual sites.

---

## 6. Confidence, kept apart

**Machine-checked (built green, `sorry`-free, axioms as noted):**

* `Enlarged.lean`: `IsDefEq.toE`; the ten free `(E)`-family lemmas and the two
  regularity-conditional ones, all `[propext]`; `IsDefEqE.mono`; `loop_conv_collapseE`;
  `retype_fires` `[propext, Classical.choice, Quot.sound]`; `uniqU_of_uniqAcross` `[propext]`;
  `uniqAcross` and `IsDefEqE.toIsDefEq` `[propext, sorryAx, Classical.choice, Quot.sound]`
  (the `sorryAx` is inherited from `uniq`, as expected).
* `EnlargedModel.lean`: `retype_sound`, `retype_soundAbove`, `defeqDF_sound'`.
* Every number in §2 and §4.

**Read off source, not machine-checked:**

* §1's diagnosis that (E, literal) breaks `IsDefEq.isType'`.
* §3's steps 1–3 — that `IsDefEqStrong`, `HasTypeStrong` and `HasTypeStratified` each need a
  new constructor. The *consequence* (§3's `UniqAcross`) is machine-checked; the claim that
  the constructors are forced is a reading of `Strong.lean:18/99/…` and `Strong.lean:829`.
  What is **not** established is that no restructuring of `uniq`'s induction closes the new
  case; I did not find one, and did not prove one cannot exist.
* §2.4's classification of the four residual sites.
* §5's last paragraph about the stronger rule.

**Corrections to earlier documents:**

* `docs/backward-analysis.md` §5's headline claim — refuted (§2). §5 has been annotated.
* `docs/backward-analysis.md` §3's counts (187/174 for `sort_inv`) — now 235. Tree growth
  since that scan, not an error in it.
* `docs/handoff-uniqu-removal.md` §5's site list is incomplete as of today: it names
  `TrExpr.beta`, `inferApp.loop.WF`, `weakN_iff'`, `prim_domain_nat`. Two more exist —
  `TypeChecker.Inner.isDefEqUnitLike.WF_proof` (`Verify/TypeChecker/IsDefEq.lean`, a direct
  `uniqU` consumer) and `VExpr.WF.app_arg_typed` (`Verify/Primitive.lean`, a `piUniq`
  consumer added since). Its §4 counterfactual table (129/66/56/2) reproduces in shape but
  not in numbers: in scope A the same cuts now read 154/128/127/3.
* `docs/handoff-uniqu-removal.md` §Correction 1 says `Verify/Primitive.lean` is outside the
  scope it measured. It is outside **scope A**, but it **is** inside `kernel_sound`'s closure.
  `prim_domain_nat` nevertheless has **zero** transitive users there.

---

## 7. What to pick up first

1. **`IsDefEq.weakN_iff'`, and it is not close.** It carries 102 of (E)'s 173 survivors and
   164 users outright; it is also sitting on the `sorry` in `IsDefEqU.weakN_iff`'s
   strengthening direction. `docs/handoff-uniqu-removal.md` §6 already names it first and
   suggests proving the *typed* weakening-inversion directly by induction rather than
   deriving it from the untyped one plus a `uniqU` retyping. This round's measurement raises
   its priority: it is one of exactly three items in the minimal disconnecting cut, and the
   only one nobody has attacked.
2. **Do not spend a round on (E) as an in-place edit.** §3 is the reason, and it is
   machine-checked at the point that matters.
3. **Relay to the `PropTypeAgree` stream:** `isDefEqUnitLike.WF_proof` is a `PropUniq`
   consumer sitting in `Verify/`, not in the model. If `backward-analysis.md` §6 lands, it
   closes that site — which is a use for §6 that §6 does not know about.
4. **`HasType.piUniq` is the other item in the minimal cut**, at 66 users and three call
   sites. "Two Π types of one term have convertible domains and codomains" is strictly weaker
   than `uniqU`; whether it is easier is still unknown and still unattempted.

---

## Appendix: the instrument

Not committed to `scripts/` (this stream does not own that directory). Save as
`scripts/cone-E.lean` and run `~/.elan/bin/lake env lean scripts/cone-E.lean`. It is
`scripts/cone-measure.lean` with the scope re-aimed at `Verify/Bridge.lean`'s closure, the
same `.thmInfo` handling, plus a "does the residual still reach the goal?" query.

```lean
import Lean4Lean.Verify.Bridge
open Lean

/-- Constants referenced by `ci`, from its type *and* its value — theorems included. -/
def deps (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci.value? (allowOpaque := true) with
  | some v => s.union v.getUsedConstantsAsSet
  | none => s

structure Graph where
  fwd : Std.HashMap Name (Array Name)
  rev : Std.HashMap Name (Array Name)

def buildGraph (env : Environment) (inScope : Name → Bool) : Graph := Id.run do
  let mut fwd : Std.HashMap Name (Array Name) := {}
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    unless inScope n do continue
    let ds := (deps ci).toList.toArray
    fwd := fwd.insert n ds
    for d in ds do rev := rev.insert d ((rev.getD d #[]).push n)
  return ⟨fwd, rev⟩

def transUsersCut (g : Graph) (seed : Name) (cut : NameSet) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := [seed]
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      for u in g.rev.getD n #[] do
        if cut.contains u then continue
        unless seen.contains u do seen := seen.insert u; stack := u :: stack
  return seen

def importClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let names := env.header.moduleNames
  let mut idx : Std.HashMap Name Nat := {}
  for h : i in [0:names.size] do idx := idx.insert names[i] i
  let mut seen : NameSet := {}
  let mut stack := roots
  while true do
    match stack with
    | [] => break
    | m :: rest =>
      stack := rest
      if seen.contains m then continue
      seen := seen.insert m
      if let some i := idx[m]? then
        for imp in env.header.moduleData[i]!.imports do stack := imp.module :: stack
  return seen

def modOf (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

def mkScope (env : Environment) (mods : NameSet) : Name → Bool := fun n =>
  match modOf env n with | some m => mods.contains m | none => false

def l4l (s : NameSet) : NameSet := Id.run do
  let mut o : NameSet := {}
  for m in s.toList do if (`Lean4Lean).isPrefixOf m then o := o.insert m
  return o

open Lean4Lean VEnv in
#eval show CoreM Unit from do
  let env ← getEnv
  let g := buildGraph env (mkScope env (l4l (importClosure env [`Lean4Lean.Verify.Bridge])))
  let mkCut (l : List Name) : NameSet := l.foldl (·.insert ·) ({} : NameSet)
  let E := [``IsDefEqU.trans, ``IsDefEqU.defeqDF, ``IsDefEqU.of_l, ``IsDefEqU.of_r,
    ``HasType.defeqU_l, ``HasType.defeqU_r, ``IsType.defeqU_l, ``IsDefEq.trans_l,
    ``IsDefEq.trans_r, ``IsDefEq.transU_l, ``IsDefEq.transU_r, ``isDefEq_iff]
  let pu : Name := ``HasType.piUniq
  let wi : Name := ``IsDefEq.weakN_iff'
  let ul : Name := `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF_proof
  let pd : Name := `Lean4Lean.TypeChecker.prim_domain_nat
  let goal : Name := `Lean4Lean.Bridge.not_leanTTConsistent_of_kernel_proves_false
  IO.println s!"scope K: {g.fwd.size} source declarations"
  for t in [``IsDefEqU.sort_inv, ``IsDefEqU.forallE_inv_stratified, ``IsDefEqU.forallE_inv,
            ``IsDefEq.uniq, ``IsDefEq.uniqU, pu, wi, pd] do
    let direct := (g.rev.getD t #[]).toList.eraseDups
    IO.println s!"  {t}: direct={direct.length} transitive={(transUsersCut g t {}).toList.length}"
    for d in direct.toArray.qsort (·.toString < ·.toString) do IO.println s!"      {d}"
  for (lbl, cut) in [("none", ([] : List Name)), ("(E)", E), ("(E)+piUniq", E++[pu]),
      ("(E)+weakN_iff'", E++[wi]), ("(E)+WF_proof", E++[ul]), ("(E)+prim", E++[pd]),
      ("(E)+piUniq+weakN_iff'", E++[pu,wi]), ("(E)+all four", E++[pu,wi,ul,pd]),
      ("all four, no (E)", [pu,wi,ul,pd])] do
    for t in [``IsDefEqU.sort_inv, ``IsDefEqU.forallE_inv_stratified, ``IsDefEqU.forallE_inv] do
      let s := transUsersCut g t (mkCut cut)
      IO.println s!"  cut {lbl}: {t} -> {s.toList.length}, reaches goal {s.contains goal}"
```
