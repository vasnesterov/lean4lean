# Handoff: strengthening — `IsDefEqU.weakN_iff`'s `sorry`

**Target:** the forward (strengthening) direction of
`Lean4Lean.VEnv.IsDefEqU.weakN_iff`, `Theory/Typing/UniqueTyping.lean:172`. **Still open, and
the statement has not moved.** Nothing in this pass was refuted either; no countermodel was
found and none is claimed.

Everything below is marked **[measured]** (a machine run whose output is reproduced),
**[machine-checked]** (a Lean proof in the tree, named), or **[read]** (read off source).

---

## 0. The four things to know before touching this

0. **The target is now reduced to three named statements, machine-checked.**

       Strengthening  ↔  SortDescend ∧ PiDescend ∧ TransStrengthening

   (`Strengthening.iff_descend`). `SortDescend` and `PiDescend` are shape-descent facts about
   *typing* — "a lifted term whose type upstairs is a sort (a Π) has a sort (a Π) type
   downstairs" — and together they are equivalent to the reflexive instance of the target
   (`TypingStrengthening.iff_descend`, **sorry-free**). `TransStrengthening` is the single
   blocked conversion rule. Everything else — eleven of twelve conversion rules, and five of
   the eight typing rules — is discharged in the tree.
1. **The criterion of `docs/handoff-stratified.md` §5 says the *conversion-level* statement
   fails, at `trans`, and it is right.** The induction *must* look at a conversion derivation
   (see §1), and the conclusion is *asserted of* the endpoints, not propagated along.
   **[machine-checked: `Strengthening.of_typing`, which closes every rule but `trans`.]**
   The *typing-level* half (`TypingStrengthening`) **passes** the criterion, because it has a
   syntax-directed judgment to induct on (§2.4).
2. **The lead relayed with this task — "prove the typed statement `IsDefEq.weakN_iff'`
   directly by induction and it closes both" — is wrong, and the reason is one line.**
   `IsDefEq.trans` shares its type between the two premises, so the typed form does buy a
   *lifted type* at `trans`; it buys nothing about the *middle term*, which is what blocks the
   proof. Formally the two statements are inter-derivable: **[machine-checked:
   `Strengthening.iff_typed`]**. They are one problem, not two.
3. **The Church–Rosser route is circular in this tree.** `IsDefEq.church_rosser`
   (`Theory/Typing/ChurchRosser.lean:2162`) is a *transitive user* of the very `sorry` it
   would discharge. **[measured]** Do not start there without first re-proving
   `NormalEq.weakN_inv_DFC` and `ParRed.weakN_inv` without it (§4).

---

## 1. The criterion, applied and written down

> *Does the statement's induction ever have to look at a conversion derivation at all?  If it
> does, it is tractable exactly when its conclusion is propagated along the conversion rather
> than asserted of its endpoints.*

**Does it have to look at a conversion derivation? For the statement as given, yes.** The
hypothesis is `∃ A, IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) A`, and the only inductive
object is that `IsDefEq` derivation. There is no escape inside the *core* judgment:
**`HasType e A` is *defined* as `IsDefEq e e A`** (`Theory/Typing/Basic.lean:60`), so even the
reflexive instance has nothing else to induct on there. **[read]** (There *is* an escape one
level out — `Theory/Typing/Strong.lean`'s syntax-directed `HasTypeStrong`, reachable by
`IsDefEq.strong` — but it is a *typing* judgment, so it serves the reflexive instance only.
That is §2.4, and it is what makes the split in §0.0 the right one.)

**Is the conclusion propagated or endpoint-asserted? Endpoint-asserted, on both sides.** The
hypothesis "both endpoints are lifted" *and* the conclusion "their strengthenings are defeq
in `Γ`" are statements about the two endpoints. At
`trans : Γ' ⊢ a ≡ b : A → Γ' ⊢ b ≡ c : A → Γ' ⊢ a ≡ c : A` with `a = e1↑`, `c = e2↑`, the
middle `b` is arbitrary and in particular need not be lifted, so **both induction hypotheses
are vacuous** — the companion test fails at the same place.

**Verdict: same row as `sort_inv` / `DefInv` clause (1) — "needs normalisation".** The
criterion predicted this before the proof was written, and it also predicted the *other* half:
the reflexive instance, which does not have to look at a conversion, is the half that closes.

The row to add to §5's table of `docs/handoff-stratified.md`:

| statement | induction sees a conversion? | conclusion | `trans` | outcome |
|---|---|---|---|---|
| `IsDefEqU.weakN_iff` (`Strengthening`) | yes, in the core judgment | endpoint-asserted | fails, IHs vacuous | needs a reduction relation |
| `TypingStrengthening` (its reflexive instance) | **no** — induction on `HasTypeStrong` | — | never arises | tractable, 5 of 8 rules; residual = `SortDescend` ∧ `PiDescend`, **equivalent** |

The second row is the third statement in this development to be settled by inducting on a
*typing* judgment rather than a conversion (`PropUniq` §16.1, `SortForallEDisjoint` §9, and
now this) — and the first where doing so left a residual that is provably *equivalent* to what
was assumed rather than weaker.

---

## 2. What was proved — `Theory/Typing/Strengthen.lean` (new, 437 lines, no `sorry`)

Three definitions, so the residuals can be named rather than described:

```lean
def Strengthening (env) (U) : Prop :=            -- the target
  ∀ {n k Γ Γ' e1 e2}, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

def TypingStrengthening (env) (U) : Prop :=      -- its reflexive instance
  ∀ {n k Γ Γ' e A}, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →
    env.HasType U Γ' (e.liftN n k) A → VExpr.WF env U Γ e

def TransStrengthening (env) (U) : Prop :=       -- the one residual case
  ∀ {n k Γ Γ' e1 e2 b A}, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →
    env.IsDefEq U Γ' (e1.liftN n k) b A → env.IsDefEq U Γ' b (e2.liftN n k) A →
    env.IsDefEqU U Γ e1 e2
```

| name | statement | status |
|---|---|---|
| `Ctx.LiftN.exists_instN` | a `LiftN 1 k` witness is an `InstN` witness for any substituted term | **[machine-checked]**, sorry-free |
| `IsDefEqU.strengthen_of_instN` | **strengthening holds when the stripped entry is inhabited** | **[machine-checked]**, sorry-free |
| `IsDefEq.strengthen_of_instN` | the same for the typed judgment | **[machine-checked]**, sorry-free |
| `VExpr.liftN_eq_{bvar,sort,const,app,lam,forallE}`, `VExpr.liftVar_eq_zero`, `Lookup.weakN_inv` | inversion of `liftN` / `liftVar` against a head constructor | **[machine-checked]**, sorry-free |
| `Strengthening.typing`, `Strengthening.trans` | the target implies its two residuals | **[machine-checked]**, sorry-free |
| `TypingStrengthening.of` | **`SortDescend` ∧ `PiDescend` ⟹ `TypingStrengthening`** | **[machine-checked]**, *sorry-free* |
| `TypingStrengthening.sortDescend`, `.piDescend` | the converses | **[machine-checked]**, *sorry-free* |
| `TypingStrengthening.iff_descend` | **`TypingStrengthening` ↔ `SortDescend` ∧ `PiDescend`** | **[machine-checked]**, *sorry-free* |
| `TypingStrengthening.typed` | `TypingStrengthening` ⟹ the *typed* form `Γ' ⊢ e↑ : A↑ → Γ ⊢ e : A` | **[machine-checked]** |
| `Strengthening.of_typing` | **`TypingStrengthening` ∧ `TransStrengthening` ⟹ `Strengthening`** | **[machine-checked]** |
| `Strengthening.iff_typed` | `Strengthening ↔ TypedStrengthening ∧ TypingStrengthening` | **[machine-checked]** |
| `Strengthening.iff_descend` | **`Strengthening` ↔ `SortDescend` ∧ `PiDescend` ∧ `TransStrengthening`** | **[machine-checked]** |

**Axiom cones, measured with `#print axioms`.** `strengthen_of_instN`, the `liftN`/`Lookup`
inversions, `Strengthening.{typing,trans}` and **all of §7** (`TypingStrengthening.of`,
`.sortDescend`, `.piDescend`, `.iff_descend`) are sorry-free.
`TypingStrengthening.typed`, `Strengthening.of_typing`, `.typed'`, `.of_typed`, `.iff_typed`
and `.iff_descend` are `sorryAx`-tainted **only** through `IsDefEqU.forallE_inv` →
`forallE_inv_stratified` and `IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean`,
pre-existing open obligations).  A forward-reachability search reports **NO PATH** from any of
them to `IsDefEqU.weakN_iff`. **[measured]** So none of this is circular, and the reductions
are real.

### 2.1 The inhabited case, and why it matters

`(e.liftN 1 k).inst e₀ k = e` (`VExpr.inst_liftN`), so if the stripped hypothesis has *any*
inhabitant in the smaller context, `IsDefEqU.instN` turns a `Γ'`-conversion between lifted
terms into a `Γ`-conversion between the terms. **The whole difficulty of strengthening is
therefore confined to context entries that are uninhabited downstairs** — the classical
situation, and the reason no *model* argument can help: over an uninhabited `Γ'` the soundness
statement is vacuous, so `Theory/SetModel/` cannot see the difference. **[read + machine-checked]**

### 2.2 The row zero: `trans` is the only blocked rule

`Strengthening.of_typing` runs the induction and **closes eleven of the twelve `IsDefEq`
rules**. What each needs:

* `bvar` — free (the two endpoints coincide, so `TypingStrengthening` supplies the answer);
* `sortDF`, `constDF`, `extra` — free (both endpoints are forced to be the lifted term itself;
  for `extra` because environment defeqs are closed, `ClosedN.liftN_eq`);
* `symm`, `defeqDF` — free (the endpoints are unchanged, so the IH applies directly);
* `appDF`, `lamDF`, `forallEDF` — `TypingStrengthening` at the whole term, then the standard
  inversion lemma (`app_inv` / `lam_inv` / `forallE_inv` of `Theory/Typing/Strong.lean`) to
  recover the *typed* premises downstairs, then `IsDefEqU.of_l` on the two IHs;
* `beta` — the same, plus `IsDefEq.uniqU` and `IsDefEqU.forallE_inv` to identify the λ's
  annotation with the application's domain (this is the same `piUniq`-shaped step
  `docs/handoff-uniqu-removal.md` §2.2 describes at `TrExpr.beta`);
* `eta` — `TypingStrengthening` at the *λ side*, which yields a Π type downstairs; weakening
  it back up and retyping the `eta` node along `uniqU` makes the function side's typing
  judgment *lifted on both sides*, at which point `TypingStrengthening.typed` applies;
* `proofIrrel` — `TypingStrengthening` at each proof gives types `C`, `C'`; `uniqU` identifies
  both with `p` upstairs, `TypingStrengthening.typed` brings `Γ ⊢ C : Sort 0` and
  `Γ ⊢ e₂ : C` down, and `.proofIrrel` fires;
* **`trans` — blocked.** Hypothesis, not proof.

The useful part of this is not that `trans` is hard (that was predicted) but that
**everything else is genuinely discharged and needs exactly one unknown**,
`TypingStrengthening`. Anyone attacking this can now ignore eleven rules.

### 2.3 The existential and typed forms are the same unknown

`TypingStrengthening` gives only "the term has *some* type downstairs". That is already the
typed form: apply it to the ascription redex `(fun _ : A => #0) e`, whose well-typedness
downstairs forces `e`'s type to meet `A` (`TypingStrengthening.typed`). **[machine-checked]**
So there is no point looking for a weaker "untyped" version of the unknown; the trick that
upgrades it is three lines.

### 2.4 `TypingStrengthening` is exactly two shape-descent statements — sorry-free

```lean
def SortDescend (env) (U) : Prop :=          -- "a lifted term typed at a sort upstairs
  ∀ …, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →      --  is typed at a sort downstairs"
    env.HasType U Γ' (e.liftN n k) (.sort u) → VExpr.WF env U Γ e →
    ∃ u₀, env.HasType U Γ e (.sort u₀)

def PiDescend (env) (U) : Prop :=            -- "a lifted function applied to a lifted argument
  ∀ …, Ctx.LiftN n k Γ Γ' → OnCtx Γ … → OnCtx Γ' … →      --  upstairs is one downstairs too"
    env.HasType U Γ' (f.liftN n k) (.forallE A B) → env.HasType U Γ' (a.liftN n k) A →
    VExpr.WF env U Γ f → VExpr.WF env U Γ a →
    ∃ A₀ B₀, env.HasType U Γ f (.forallE A₀ B₀) ∧ env.HasType U Γ a A₀
```

`TypingStrengthening.iff_descend : TypingStrengthening ↔ SortDescend ∧ PiDescend`, and it is
**sorry-free**. **[machine-checked]**

*Why the induction works where `Strengthening`'s does not.* `TypingStrengthening` has a
**syntax-directed** judgment available, `HasTypeStrong` (`Theory/Typing/Strong.lean:99`),
reached by `IsDefEq.strong … |>.hasType'.1`. Its one non-syntax-directed rule, `defeq`,
**keeps the same term**, so its case closes by the induction hypothesis and *no conversion
derivation is ever inspected*. It therefore **passes** the criterion outright — the same way
`PropUniq` and `SortForallEDisjoint` do (`handoff-stratified.md` §16.1, §9). Of its eight
rules: `bvar`, `sort'`, `const`, `base`, `defeq` close for free; `lam` and `forallE` need only
`SortDescend`; `app` needs only `PiDescend`.

*This is a reformulation, not a weakening — and that is stated deliberately* (trap #11 of
`handoff-stratified.md`: check whether a proposed strengthening is the same statement). The
two descend statements are together **equivalent** to `TypingStrengthening`, machine-checked
in both directions. What the reformulation buys is (i) that only `sort`- and `Π`-shaped types
matter — every other typing rule is discharged — and (ii) that the residual is now stated in
the idiom of `Theory/Typing/Injectivity.lean`, where `sort_inv`, `forallE_inv` and
`SortForallEDisjoint` already live.

*The converses are cheap and instructive.* `SortDescend` follows from `TypingStrengthening`
by applying it to `∀ (_ : e), Prop` — a Π whose *domain* is `e` is well-formed downstairs only
if `e` is a type there, and `HasType.forallE_inv` (sorry-free, `henv` only) reads that off.
`PiDescend` follows by applying it to the application `f a` itself and using
`VExpr.WF.app_inv`. Both sorry-free.

---

## 3. Measured cone — what the `sorry` actually costs

Reproduce with `scripts/cone-measure.lean` (unchanged) and the variant used here (the variant
adds `import Lean4Lean.Theory`, which the committed script does **not** transitively reach —
see §3.1). **[measured]**

Committed script, unchanged, scope A (import closure of `Verify/TypeChecker.lean` +
`Verify/Typing/Lemmas.lean`, 11338 declarations) — this **confirms** the figures relayed with
the task:

| cut | `IsDefEqU.sort_inv` transitive users |
|---|---|
| none | 129 |
| (E) | 66 |
| (E) + `piUniq` | 56 |
| (E) + `IsDefEq.weakN_iff'` | **31** |
| (E) + `piUniq` + `weakN_iff'` | 2 |

Scope B of the committed script (12756 declarations): 192 / 102 / 92 / 67 / 3.

The number that measures **this** target rather than `sort_inv`'s:

| declaration | direct users | transitive users |
|---|---|---|
| `IsDefEqU.weakN_iff` (scope A) | 5 | **58** |
| `IsDefEqU.weakN_iff` (scope B) | 5 | **93** |
| `IsDefEqU.weakN_iff` (**scope C**, +`Lean4Lean.Theory`, 13532 decls) | 9 | **119** |

### 3.1 A correction to the instrument's coverage

`scripts/cone-measure.lean`'s scope B is advertised as "all `Lean4Lean.*` modules", but it is
all modules *reachable from its own import list*, and **nothing under `Verify/` imports
`Theory/Typing/ChurchRosser.lean`** — it is reachable only through `Lean4Lean/Theory.lean`.
**[measured + read]** So scope B silently omits the entire Church–Rosser development. Adding
`import Lean4Lean.Theory` raises the declaration count 12756 → 13532 and `weakN_iff`'s cone
93 → 119. Any future statement of the form "scope B = everything" should be checked against
this. (The committed script was left unmodified; the variant lives only in the scratchpad.)

---

## 4. The Church–Rosser route: priced, and closed as it stands

`Theory/Typing/ChurchRosser.lean` really does prove what the route wants:

* `IsDefEq.church_rosser : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ ≫≪ e₂` (line 2163) — full completeness of
  parallel reduction for the typed conversion, `extra` rules included. **[read]**
* `ParRed.weakN_inv` (765) — a reduct of a lifted term is lifted. **[read]**
* `NormalEq.weakN_iff` (432) / `NormalEq.weakN_inv_DFC` (327) — strengthening for the
  normal-form equality. **[read]**

Together those give strengthening in three lines. **They cannot be used.** A forward
reachability search over the declaration graph finds:

```
IsDefEq.church_rosser → CRDefEq.trans → NormalEq.parRedS → NormalEq.parRed
                      → ParRed.weakN_inv → IsDefEqU.weakN_iff
NormalEq.trans → NormalEq.weakN_iff → NormalEq.weakN_inv_DFC → IsDefEqU.weakN_iff
```

**[measured]** — and `NormalEq.weakN_inv_DFC` and `ParRed.weakN_inv` appear in §3's list of
`weakN_iff`'s nine direct users. Proving `weakN_iff` from `church_rosser` would be circular.

**What it would take to break the cycle, precisely.** The uses divide into two kinds:

* `ParRed.weakN_inv` uses it in **one** place, the `extra` case: a reduction rule's
  `Check` obligations are `IsDefEqU` constraints on the *matched arguments*, which are strict
  subterms of the term being reduced. So this use is at a **strictly smaller term** and a
  well-founded induction can absorb it. **[read]**
* `NormalEq.weakN_inv_DFC` uses it at the **same** term, in `refl`, `appDF`, `etaL`/`etaR` and
  `proofIrrel`, to reconstruct the typing side-conditions that `NormalEq`'s constructors
  carry, and additionally at the *types* of subterms in `appDF`. Those are
  `TypingStrengthening` (and `Strengthening` at types), not a smaller instance. **[read]**

So the honest statement of the reduction is: **`Strengthening` follows from Church–Rosser
plus `TypingStrengthening`**, and Church–Rosser as written already consumes
`TypingStrengthening`. The route is not refuted; it is *unbuilt*. Building it means
re-proving `NormalEq.weakN_inv_DFC` (110 lines) from `TypingStrengthening` alone, and
relocating it so `UniqueTyping.lean` can see it (`ChurchRosser.lean` imports `UniqueTyping.lean`,
so the file order has to change: `IsDefEq.uniq` and friends would move to a new file imported
by both). Neither step was attempted here.

Note also that `ChurchRosser.lean` is not sorry-free for independent reasons: five `sorry`s in
`NormalEq.descend` and a dependency on `IsDefEqU.forallE_inv_stratified`. **[read]** So even a
successful de-circularisation would deliver `weakN_iff` *modulo* those, not sorry-free.

---

## 5. Routes attempted, and the exact step each failed at

| route | failed at |
|---|---|
| direct induction on `IsDefEqU`, statement as given | `trans`: middle term arbitrary, both IHs vacuous. **[machine-checked]** — `Strengthening.of_typing` is that induction, with `trans` extracted as `TransStrengthening`. |
| the relayed lead: induct on the **typed** `IsDefEq.weakN_iff'` instead | same `trans`. `IsDefEq.trans` fixes the *type* across both premises, so lifting the type is inherited for free and buys nothing; the middle *term* is untouched. Formally, `Strengthening.iff_typed`. **[machine-checked]** |
| find a *propagated* restatement (what the criterion asks for) | none exists that is not the statement itself: the property "descends to `Γ`" is only meaningful at terms that are lifted, so any relation extending it to arbitrary middle terms is either vacuous there (and `trans` fails) or is the erasure of a `Γ'`-term to a `Γ`-term, which does not exist when the stripped entry is uninhabited. **[read/argued, not machine-checked]** |
| Church–Rosser (`ChurchRosser.lean`) | circular — §4. **[measured]** |
| model side (`Theory/SetModel/`) | cannot work in principle: `Γ'` may be uninhabited, and every soundness statement over an uninhabited context is vacuous, so the model validates strengthening's *hypothesis* without validating its conclusion. §2.1. **[read/argued]** |
| `VExpr.Skips` / `IsDefEq.skips` | contains no hard content. `IsDefEq.skips` (`UniqueTyping.lean:180`) is a four-line **consequence** of `weakN_iff`, obtained by `skips_iff_exists` and one application of the forward direction. It is downstream, not a lemma toward it. **[read]** |
| substitution (the inhabited case) | **succeeds**, and is now in the tree sorry-free (`IsDefEqU.strengthen_of_instN`). It leaves exactly the uninhabited case. **[machine-checked]** |
| induction on the **syntax-directed** `HasTypeStrong` for the *typing* half | **succeeds** — `TypingStrengthening.of`, sorry-free. Five of eight rules close outright, `lam`/`forallE` need `SortDescend`, `app` needs `PiDescend`, and those two are together equivalent to what was assumed. §2.4. **[machine-checked]** |

---

## 6. Convergence worth recording, and what it does *not* say

`Strengthening.of_typing`'s `beta`, `eta` and `proofIrrel` cases need `IsDefEq.uniqU` and
`IsDefEqU.forallE_inv`, so the *conversion-level* row zero's axiom cone contains `sorryAx`
through `Injectivity.lean` — **the same family `docs/handoff-stratified.md` is about**.
**[measured]** §4's route arrives at the same place independently: `ChurchRosser.lean` also
runs on `IsDefEqU.forallE_inv`.

**What this does not say.** The *typing-level* decomposition of §2.4 is sorry-free — it does
**not** consume Π-injectivity. So the entanglement with `Injectivity.lean` is a property of
the `trans`-side of the problem and of the retyping steps in `beta`/`eta`/`proofIrrel`, not of
the shape-descent statements themselves. Anyone attacking `PiDescend` is not thereby
committed to `forallE_inv`.

---

## 7. What to pick up first

The target is now **exactly three statements**, machine-checked
(`Strengthening.iff_descend`):

    Strengthening  ↔  SortDescend ∧ PiDescend ∧ TransStrengthening

1. **`PiDescend`** — *the* unknown. It is equivalent (with `SortDescend`, which is much the
   smaller half) to `TypingStrengthening`, i.e. to the reflexive instance of the target; and
   the eleven-of-twelve row zero of §2.2 says it is also all that the *general* statement
   needs apart from `trans`. Two things about it that the general statement does not have:
   its induction never sees a conversion derivation (§2.4), and it is a statement about
   Π-shape, which is the subject matter of `Theory/Typing/Injectivity.lean`. **Whether it is
   provable is open and this pass makes no prediction.**
2. **`TransStrengthening`.** Still the one blocked conversion rule, still needing a reduction
   relation, still circular through `ChurchRosser.lean` as the tree stands (§4). If someone
   wants to attack it, the concrete unblocking task is: re-prove
   `NormalEq.weakN_inv_DFC` (110 lines) from `TypingStrengthening` rather than from
   `IsDefEqU.weakN_iff`, and relocate `IsDefEq.uniq` out of `UniqueTyping.lean` so the
   `NormalEq` development can sit below it. `ParRed.weakN_inv`'s single use is already at a
   strictly smaller term and needs no new idea.
3. **Do not** re-attempt a direct conversion induction, a model argument, `skips`, or "prove
   the typed form instead". §5 has the reason for each, and the first and last are now
   machine-checked dead ends rather than opinions.

## 8. Files

* `Lean4Lean/Theory/Typing/Strengthen.lean` — **new**, 437 lines, everything in §2. No `sorry`
  is declared anywhere in it.
* `Lean4Lean/Theory/Typing/UniqueTyping.lean` — **unchanged**; the `sorry` at :172 is still
  there and this pass did not earn the right to remove it.
* `scripts/cone-measure.lean` — **unchanged**; see §3.1 for the coverage caveat.
