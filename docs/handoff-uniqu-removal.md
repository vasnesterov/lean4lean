# Can the unique-typing dependency be dropped at its `Verify/` consumers?

**Short answer: no.** The conjecture this stream was asked to price — *"three proof sites all
use `uniqU` to reconcile a constructed type with a given one; thread one type through the
invariant instead and the dependency disappears at all three"* — is **false**, and the reason
is structural rather than local. What was achievable, and is done, is a narrowing: the whole
`Verify/TypeChecker.lean` closure now reaches `IsDefEq.uniqU` through **one** named lemma
instead of three scattered appeals, and one of the three named sites turned out to be dead
code and is gone.

Everything below marked **[measured]** comes from `scripts/cone-measure.lean` (added by this
stream; run `~/.elan/bin/lake env lean scripts/cone-measure.lean` from the repo root).
Everything marked **[read]** is read off the source and is an argument, not a measurement.

---

## 1. Corrections to `Verify/SafeFragment.lean` §4

§4's numbers reproduce exactly, and its *table* is right. Its **consumer list is wrong in two
ways**, both because it measured a scope that is too small.

| §4 claim | status |
|---|---|
| `IsDefEqU.sort_inv`: 129 transitive users, 1 direct consumer (`IsDefEq.uniq`) | **confirmed [measured]** |
| `IsDefEq.uniq`: exactly 4 direct consumers | **wrong** — 4 in the closure it measured, **5** over all of `Lean4Lean` **[measured]** |
| `IsDefEq.uniqU`: exactly 4 direct consumers | **confirmed as a count**, but see below |
| the E-cut table (129 / 122 / 83 / 83 / 67 / 66 / 0) | **confirmed exactly [measured]** |

**Correction 1 — there is a fifth unique-typing consumer in `Verify/`, and it is not a `uniqU`
consumer.** `Lean4Lean.TypeChecker.prim_domain_nat` (`Lean4Lean/Verify/Primitive.lean:1460`)
calls `IsDefEq.uniq` **directly**:

```lean
exact ⟨A, B, h1, h2.uniq henv trivial (hprim.natLit_hasType hnat n)⟩
```

`Verify/Primitive.lean` is *not* in the import closure of `Verify/TypeChecker.lean` +
`Verify/Typing/Lemmas.lean` (it imports them), so §4's scope could not see it. It is the same
shape as the other sites: `h2` types `.natLit n` at the domain `app_inv` produced, and
`hprim.natLit_hasType` types the same term at `.nat`. Any plan that says "close these three
and unique typing leaves `Verify/`" must account for it. **[measured + read]**

**Correction 2 — one of the three named sites was dead code.**
`TypeChecker.Inner.inferType.WF_uniq` (`Verify/TypeChecker/Basic.lean`) had **zero** users —
transitively, over every `Lean4Lean.*` module. **[measured]** It has been deleted (its text is
preserved in a comment at the same place). Its content is precisely "`inferType` may be
specified against a *given* type rather than the type it computes", which is `uniqU` restated;
nobody wanted it, and nobody can cheaply supply it.

**Correction 3 — the fourth consumer is load-bearing and is not in `Verify/`.**
`VEnv.IsDefEq.weakN_iff'` lives in `Lean4Lean/Theory/Typing/UniqueTyping.lean:190`, which this
stream may not edit. Two things about it:

* Under (E) it alone keeps **56** of the 66 surviving `sort_inv` users alive: cutting the
  `Verify/` sites but not `weakN_iff'` takes 66 → 56; cutting `weakN_iff'` but not the
  `Verify/` sites takes 66 → 31; cutting both takes 66 → 2 (`uniq` and `uniqU` themselves).
  **[measured]**
* It is already blocked on a *different* open obligation: its proof calls
  `VEnv.IsDefEqU.weakN_iff` (`UniqueTyping.lean:172`), whose forward (strengthening) direction
  is a literal `sorry`. **[read]** So "remove `uniqU` from `weakN_iff'`" buys nothing on its
  own; the two must be closed together, and the natural way to close both at once is to prove
  the *typed* statement `IsDefEq.weakN_iff'` directly by induction rather than deriving it from
  the untyped `IsDefEqU.weakN_iff` plus a `uniqU` retyping. That is a lead for whoever owns
  `Theory/Typing/UniqueTyping.lean`; it is not attempted here.

---

## 2. The lead, priced: why threading fails, and where exactly

Both live `Verify/` sites have the shape §4 describes — a constructed type meeting a given one
— but the two types are not two spellings of one thing that an invariant could merge. In both
cases **one type is fixed by the input term's `TrExprS` derivation, built before the checker
ran, and the other is produced by the checker at run time.** Nothing in the algorithm forces
them to be syntactically equal, because *the algorithm deliberately does not check that they
are*.

### 2.1 `TypeChecker.Inner.inferApp.loop.WF` (`Verify/TypeChecker/InferType.lean:250`)

The loop carries `hfty : c.TrExpr (fType.instantiateList lm) fty'` and
`hety : c.HasType e' fty'`, and consumes an `AppStack` whose `.app` node carries
`hf' : c.HasType e' (.forallE A B)` and `ha' : c.HasType a' A`.

The step that fails is the last line of each branch:

```lean
exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
```

`TrExpr.inst` needs the argument typed at the **checker's** Π domain (`tyv`, from `hfty` after
`ensureForallCore`), and `AppStack.app` supplies it typed at the **translation's** Π domain
(`A`, from the `TrExprS.app` node of the original expression). Threading a single type through
the invariant cannot merge `A` and `tyv`:

* `A` is existentially bound inside the `TrExprS.app` constructor
  (`Verify/Typing/Expr.lean`), chosen when the *term* was translated;
* `tyv` is whatever `inferType` returned for the head and `ensureForallCore` whnf'd into a Π,
  at run time;
* `inferApp` **never re-checks the arguments** — that is the whole point of the `inferOnly`
  fast path, and the C++ kernel's `infer_app` does the same — so no run-time test relates them.

The *only* bridge is that `.forallE A B` and `fty'` are two types of the **same** model term
`e'`. That is unique typing, by definition.

Threading in the opposite direction (make the invariant track the checker's type rather than
the stack's, which is what it currently does at each step via `(.app hf' ha')`) moves the
appeal but does not remove it: the recursive `hety` then needs `c.HasType a' tyv` and the stack
still only offers `c.HasType a' A`.

Pushing the appeal to the loop's *entry* does not work either: at `inferApp.WF`
(`InferType.lean:301`) the tracked type and the stack head genuinely agree — both come from the
single `inferType.WF he'.tr` result — so there is nothing to reconcile there. **[read]**

### 2.2 `TrExpr.beta` (`Verify/Typing/Lemmas.lean:2588`), `beta` case

`TrExprS.app` supplies `hf : c.HasType (.lam A' b') (.forallE A B)` and `ha : HasType a' A`;
`HasType.lam_inv` supplies `hA : IsType A'` and `hb : HasType b' B'` and therefore
`hA.lam hb : HasType (.lam A' b') (.forallE A' B')`. Both `TrExprS.inst` and the model's `beta`
rule need `HasType a' A'` — the λ's **annotation** — while the application node fixed `A`.

`BetaReduce` is a purely syntactic relation on `Expr` and carries no typing at all, so there is
no invariant to thread. The obvious repair — strengthen `HasType.lam_inv` to conclude at the
*given* type, `Γ ⊢ .lam A' b' : T → ∃ B', IsDefEqU Γ (.forallE A' B') T` — is exactly the
statement whose proof needs `IsDefEqU`-transitivity across the `defeq`/`conv` steps of the
derivation, i.e. `uniq` again.

There is a *stratified* version of precisely that lemma already in the tree and it is
sorry-free: `HasTypeN.lam_inv` (`Theory/Typing/UniqueTypingN.lean:349`) concludes
`env.IsDefEqN U n Γ (.forallE A B) T`, because `Stratified`'s `conv` rule is three-place so its
`trans` is a constructor. **It cannot be used here**: the converse bridge `IsDefEqN n → IsDefEqU`
is not proved and, per `Theory/Typing/Stratified.lean:323` and `UniqueTypingN.lean:455`, *needs
`IsDefEq.uniq` itself*. So the stratified world reaches the statement but cannot export it.
**[read]**

### 2.3 The general statement

The failure is **general, not site-specific**. `TrExprS` records typing at each syntactic
subterm's own choice of type (`TrExprS.app` fixes the application's domain, `TrExprS.lam` fixes
the λ's annotation), and the checker recomputes types independently. Every proof that composes
two subterms' typings, or that composes the checker's answer with the translation's, must
reconcile two independently-derived types of one model term. No restatement of a `WF` invariant
removes that, because the two derivations have genuinely different provenance.

---

## 3. What was changed, and what it bought

All edits are in files this stream owns. `~/.elan/bin/lake build Lean4Lean.Verify` is green
(1214 jobs; guards 1–3 unchanged, guard 2 still "proof INCOMPLETE: sorryAx present" as before).
A plain `lake build` additionally fails in `Lean4Lean/Theory/Typing/AppCase.lean` and
`Lean4Lean/Theory/Inductive/Companion.lean` — both **untracked, another stream's work in
progress**, unrelated to and unaffected by anything here.

1. **`Verify/TypeChecker/Basic.lean`** — deleted the dead `inferType.WF_uniq` (text kept in a
   comment). One `uniqU` consumer gone at zero cost and zero meaning.
2. **`Verify/Typing/Lemmas.lean`** — added `VEnv.HasType.piUniq`, the named residual:

   ```lean
   theorem VEnv.HasType.piUniq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
       (h1 : env.HasType U Γ e (.forallE A B)) (h2 : env.HasType U Γ e (.forallE A' B')) :
       (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
     (h1.uniqU henv hΓ h2).forallE_inv henv hΓ
   ```

   and rewrote `TrExpr.beta` to use it.
3. **`Verify/TypeChecker/InferType.lean`** — rewrote `inferApp.loop.WF`'s two `uniqU` uses to go
   through `piUniq` as well. `IsDefEqU.trans` is no longer used there; the site now depends on
   `HasType.defeqU_r` (free under (E)) plus `piUniq`.
4. **`scripts/cone-measure.lean`** — the measurement instrument, with the `.thmInfo` /
   `value? (allowOpaque := true)` trap handled. Not in any `lean_lib` glob.

**What this buys.** The `Verify/` side needs unique typing **only at Π types**, never at an
arbitrary pair of types, and that fact is now one grep-able lemma with two call sites instead of
three inline `uniqU` calls in three files. `piUniq` is the single statement to attack (or to
turn into a hypothesis) if anyone wants to decouple `Verify/` from `UniqueTyping.lean`.

**What this does not buy: nothing in the cone.** `piUniq` is *proved from* `uniqU`, so every
number below is unchanged from before the edit except where a declaration was deleted.

---

## 4. Measured cone, before and after **[measured]**

Scope A = import closure of `Verify/TypeChecker.lean` + `Verify/Typing/Lemmas.lean` (§4's
scope). Scope B = every `Lean4Lean.*` module, i.e. all of `Verify/`, `Primitive.lean` included.

| | before (scope A / B) | after (scope A / B) |
|---|---|---|
| source declarations scanned | 11339 / 12757 | 11338 / 12756 |
| `IsDefEqU.sort_inv` transitive users | **129 / 192** | **129 / 192** |
| `IsDefEq.uniq` direct consumers | 4 / 5 | 4 / 5 |
| `IsDefEq.uniqU` direct consumers | **4 / 4** | **2 / 2** |
| `IsDefEq.uniqU` transitive users | 64 / 99 | 64 / 99 |

`uniqU`'s direct consumers, before: `TrExpr.beta`, `inferApp.loop.WF._f`, `inferType.WF_uniq`,
`IsDefEq.weakN_iff'`. After: `HasType.piUniq`, `IsDefEq.weakN_iff'` — and `piUniq`'s own two
consumers are `TrExpr.beta` and `inferApp.loop.WF._f`.

Counterfactual, scope A, cutting the (E) family of twelve (`IsDefEqU.trans`, `defeqDF`,
`of_l`, `of_r`, `HasType.defeqU_l/_r`, `IsType.defeqU_l`, `IsDefEq.trans_l/trans_r/transU_l/
transU_r`, `isDefEq_iff`):

| edges cut | `sort_inv` users remaining |
|---|---|
| none | 129 |
| (E) | 66 |
| (E) + `piUniq` (i.e. both live `Verify/` sites) | **56** |
| (E) + `piUniq` + `IsDefEq.weakN_iff'` | **2** (`uniq`, `uniqU` themselves) |

Scope B: 192 / 102 / 92 / **3** — the third survivor is `prim_domain_nat`, which uses `uniq`
directly and so is untouched by cutting `uniqU`.

**Read this table honestly.** Removing `uniqU` at the `Verify/` sites *without* (E) moves
`sort_inv`'s cone from 129 to 128 — one declaration, `uniqU` itself. The three-site lead was
never worth 129 declarations; under (E) it is worth 10 (66 → 56), and the remaining 56 are
`weakN_iff'`'s.

---

## 5. End state

**Does anything in the `Verify/TypeChecker.lean` closure still depend on `IsDefEq.uniqU`,
`IsDefEq.uniq`, or `IsDefEqU.sort_inv`? Yes — all of it, exactly as before.** Named sites:

* `Lean4Lean.TrExpr.beta` — `Verify/Typing/Lemmas.lean`, via `HasType.piUniq`. **open.**
* `Lean4Lean.TypeChecker.Inner.inferApp.loop.WF` — `Verify/TypeChecker/InferType.lean`, via
  `HasType.piUniq`. **open.**
* `Lean4Lean.VEnv.IsDefEq.weakN_iff'` — `Theory/Typing/UniqueTyping.lean` (read-only to this
  stream), via `uniqU` directly, and additionally blocked on the `sorry` in
  `IsDefEqU.weakN_iff`. **open, not this stream's file.**
* `Lean4Lean.TypeChecker.prim_domain_nat` — `Verify/Primitive.lean` (not this stream's file),
  via `IsDefEq.uniq` directly. **open, and previously uncounted.**
* `Lean4Lean.TypeChecker.Inner.inferType.WF_uniq` — **deleted, was dead.**

Nothing in the tree changed status from unproved to proved. No `sorry` was added; no theorem
statement outside the deleted dead lemma changed, so no downstream proof was perturbed (0
files broken, 0 files outside this stream's ownership touched).

## 6. What to pick up first

1. **`IsDefEq.weakN_iff'` in `Theory/Typing/UniqueTyping.lean`.** It is the largest residue
   under (E) (56 of 66), it is *also* sitting on an unrelated `sorry`
   (`IsDefEqU.weakN_iff`'s strengthening direction), and the two look closable together by
   proving the typed weakening-inversion directly by induction instead of deriving it from the
   untyped one plus a `uniqU` retyping. Whether that induction goes through is **not** priced
   here. Requires the owner of that file.
2. **`piUniq` itself.** "Two Π types of one term have convertible domains and codomains" is
   strictly weaker than `uniqU` and is now the entire `Verify/` demand. Whether it is *easier*
   is unknown — no attempt was made, and the obvious stratified route (`HasTypeN.lam_inv`,
   which does prove the analogous statement sorry-free) is blocked by the missing
   `IsDefEqN n → IsDefEqU` direction, which itself needs `uniq`.
3. **Do not spend more effort on invariant restatement at these sites.** §2 gives the reason:
   the two types have different provenance by construction, and `inferApp`'s `inferOnly` path
   is specified not to relate them.
