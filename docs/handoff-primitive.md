# `checkPrimitiveDef.WF.rest` — the `Nat.gcd` / `Nat.bitwise` branches were **false**, and are not any more

Stream scope: `Lean4Lean/Verify/Typing/Expr.lean`, `Lean4Lean/Primitive.lean`,
`Lean4Lean/Verify/Primitive.lean`, `Lean4Lean/Verify/Environment/Boundaries.lean`
(`checkPrimitiveDef.WF.rest` only), and new files under `Lean4Lean/Verify/`.

Everything below is marked **[machine-checked]** (a `lake build`, the sorry census, a Kernel
Arena run, or `scripts/primitive-wf-refutation.lean` produced it) or **[argued]** (read off the
code, or reasoned). The two are kept strictly apart; the central claim of this round is
machine-checked, and one supporting claim is explicitly not.

| gate | before | after |
| --- | --- | --- |
| sorry census (`lake env lean scripts/sorry-census.lean`) | **19** | **19** **[machine-checked, both runs]** |
| `checkPrimitiveDef.WF.rest`'s open branches | 2 (`gcd`, `bitwise`) | **2** (`gcd`, `bitwise`) |
| ...of which **false as stated** | **2** **[machine-checked]** | **0** **[machine-checked, the witnesses are re-run against the fix]** |
| `lake build Lean4Lean.Verify.Environment.Boundaries` | green | green **[machine-checked]** |
| Kernel Arena (`lean4lean-local`) | 185 / 6 / 0 | **185 / 6 / 0** **[machine-checked, two runs]** |

**`Lean4Lean/Primitive.lean` is changed this round.** `divergences.md` carries the entry
(clause *Eleventh* of the `checkPrimitiveDef` bullet); `bugs-found.md` carries item 16.

---

## 0. Bottom line

1. **The `Nat.gcd` and `Nat.bitwise` branches of `checkPrimitiveDef.WF.rest` were not open —
   they were false.** The recognizer accepted definitions that the Lean kernel does not reduce
   at numerals at all, while `VEnv.HasPrimitives` demands exactly that reduction. §1.
2. Six rounds of proof effort on those branches could not have succeeded. **The brief's
   standing plan — "a fuel induction on the `Nat.rec` skeleton at numerals, whose one named
   prerequisite is a `whnfCore.WF`/`unfoldDefinition.WF` returning a defeq witness" — was
   wrong twice over**: that prerequisite is not needed at all (§3(c)), and the plan would have
   run into the false statement above regardless. §5.
3. **Both branches are fixed on the implementation side**, and the witnesses are re-run against
   the fix and die. §3, §4.
4. A **second** gap, in the same two branches, was closed at the same time: the fixpoint
   equation was pinned at exactly one `ih`. No witness exists for that one and none is claimed;
   it made the obligation *underivable*, not false. §2.
5. The census does not move. `checkPrimitiveDef.WF.rest` is one declaration and two of its four
   branches still carry `sorry`; it reads 18 only when all four close. What moved is that the
   remaining two are now *provable*.

---

## 1. The refutation **[machine-checked]**

`scripts/primitive-wf-refutation.lean`. Run it with `lake env lean`.

`VEnv.HasPrimitives.natGcd` is `env.ReflectsNatNatNat ``Nat.gcd Nat.gcd`, i.e.

```
env.contains ``Nat.gcd → ∀ a b, env.IsDefEqU 0 [] (Nat.gcd (natLit a) (natLit b)) (natLit (Nat.gcd a b))
```

— *definitional* equality, at numerals. `checkPrimitiveDef.WF.rest`'s `preserves` field has to
produce it for the environment the declaration is being added to.

Both branches route through `unfoldNatWellFounded`, which recovers
`WellFounded.Nat.fix α motive h F a₀` from the definition's value. **It checked nothing at all
about the measure `h`.** And (Lean core, `Init/WF.lean`):

```
def Nat.eager (n : Nat) : Nat := if Nat.beq n n = true then n else n   -- "prevents reduction …"
def Nat.fix : (x : α) → motive x := fun x => go (Nat.eager (h x + 1)) x _
```

so the fuel `Nat.rec` fires only once `h x` evaluates to a ground value. A definition whose
measure the kernel cannot evaluate is stuck at every numeral.

**The witness.** `badGcd` has the real `Nat.gcd` body and `termination_by m + 0 * Stuck`, where
`Stuck := Classical.choice ⟨0⟩` — an axiom, so no delta rule reduces it. The measure is
propositionally `m` (`Nat.zero_mul`), so the definition elaborates, type-checks and terminates;
its `eq_def` is the real one. `badBitwise` is the same trick on `Nat.bitwise`.

Measured, before the fix:

```
kernel  Nat.gcd 4 6 = 2          : true        kernel  bitwise and 12 10 = 8    : true
kernel  badGcd  4 6 = 2          : false       kernel  badBitwise and 12 10 = 8 : false
recognizer, real Nat.gcd         : accepted    recognizer, real Nat.bitwise     : accepted
recognizer, badGcd as Nat.gcd    : accepted    recognizer, badBitwise as ~      : accepted
```

The `kernel` rows use `Lean.Kernel.Environment.addDecl` on `@rfl Nat (f 4 6) : f 4 6 = 2`, so
they are the *kernel's* verdict, not the elaborator's. The `recognizer` rows run
`Environment.checkPrimitiveDef` on a `DefinitionVal` named `Nat.gcd` / `Nat.bitwise` carrying
the bad value.

**Scope of the claim.** Machine-checked: the recognizer accepted it, and *Lean's kernel* cannot
reduce it. The remaining step — from "Lean's kernel cannot reduce it" to "`VEnv.IsDefEqU` does
not hold" — is Church–Rosser for the abstract theory, which is not fully proved in this tree
(`VEnv.NormalEq.descend` still carries a `sorry`). So precisely: **either
`checkPrimitiveDef.WF.rest` was false, or `VEnv.IsDefEqU` is strictly coarser than kernel
conversion at these terms** — and the second disjunct would be a considerably worse finding
about `Theory/`. Either way the branch was not provable as it stood.

## 2. The second gap: `F` was pinned at one `ih` **[argued; no witness, and none is claimed]**

`unfoldNatWellFounded` checked `rhs ≡ F a₀ ih'` at exactly one `ih'`, namely
`fun y _ => Nat.fix h F y`. A fuel induction at numerals must evaluate `F a₀` at
`fun y _ => Nat.fix.go h F fuel y _`, a *different* argument, and an `IsDefEqU` at one argument
implies nothing about another. The two λ-terms are pointwise equal only propositionally (that
is `Nat.fix.go_congr`, whose proof is an induction), and function extensionality is not a
definitional rule.

Two dead ends worth not re-deriving:

* **Fuel invariance cannot be recovered.** Proving `go k y ≡ go k' y` from the recurrence would
  need `F y ih₁ ≡ F y ih₂` from `ih₁ z ≡ ih₂ z` for all `z` — funext, not defeq.
* **`ih'` cannot be abstracted after the fact.** `IsDefEqU (F a₀ ih') rhs` is a fact about the
  application, not about `F`.

No counterexample is offered for this half, and that is a real gap in the evidence: `F x ih`
β/ι-reduces uniformly in `ih`, so a *semantic* witness probably does not exist. **"No witness"
is not evidence of truth** — the point here is derivability, and the branch was underivable.

## 3. What changed in `Lean4Lean/Primitive.lean`

`unfoldNatWellFounded` now returns a `NatWFUnfold` (`rhs`, `go`, `pack`, `measure`) instead of a
bare `Expr`, and takes an optional `measureIs`.

* **(a) The measure check.** `checkedIsDefEq (h (pack fvs)) μ`, with `μ` supplied by the branch:
  `m` for `Nat.gcd`, `n` for `Nat.bitwise`. `pack` is `fun fvs => a₀`, built with
  `(← getLCtx).mkLambda fvs a₀` from the `a₀` the reduction recovered. **This is what kills §1's
  witnesses.** Strictly stricter.
* **(b) The fuel recurrence.** Each branch now checks, under fresh `fuel : Nat` and a fuel bound
  `hb` whose domain is *read off `go`'s own type* rather than rebuilt:

  ```
  go (Nat.succ fuel) (pack fvs) hb  ≡  <the branch's body, with the recursive call at go fuel (pack …) prf>
  ```

  For `Nat.gcd` the body is `Condition.natEq.dite #[m, 0] n (go fuel (pack (n % m) m) prf)` with
  `prf := Nat.lt_of_lt_of_le (Nat.mod_lt n (Nat.pos_of_ne_zero (.bvar 0))) (Nat.le_of_lt_succ hb)`
  — `.bvar 0` is the `¬(m = 0)` that `Condition.dite`'s else-branch `lam0` binds. For
  `Nat.bitwise` the outer `n = 0` test becomes a `dite` for the same reason (its `ite` form binds
  nothing, so the recursive call's fuel bound would have no proof of `n ≠ 0` in scope), and
  `prf := Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero (.bvar 0)) (Nat.le.refl)) (Nat.le_of_lt_succ hb)`.
  This is the shape the **proved** `Nat.mod` / `Nat.div` branches use.
* **(c) Two conversions re-established by checked conversions.** `mkAppN e fvs ≡ fix h F (pack fvs)`
  and `fix h F a ≡ go (Nat.eager (h a + 1)) a _` were previously only *found* by
  `whnfCore`/`unfoldDefinition`. Both are now `checkedIsDefEq`s. They hold definitionally
  wherever the reduction found them, so this is accept-set neutral — and it means **the
  verification needs no specification of `whnfCore` or `unfoldDefinition` at all.** The brief's
  "one named prerequisite" is gone.
* `Nat.bitwise`'s `Condition.natEq` check now runs with `dite := true`.

Two implementation traps, both of which cost a build:

1. **`natRec`/`go` must be captured before the `lambdaTelescope`.** That telescope rebinds `F`
   to a *local* free variable; building `go` after it returns a term mentioning an escaped fvar,
   and the failure surfaces as `(kernel) unknown free variable` at the `run_meta` self-test, far
   from the cause.
2. `Condition.dite` wraps both branches in `Expr.lam0`, so anything placed in them shifts by one
   binder; `Condition.ite` does not. The fuel bound's proof term relies on that binder existing.

## 4. Re-running the refutation against the fix **[machine-checked]**

```
recognizer, real Nat.gcd         : accepted = true      recognizer, real Nat.bitwise : accepted = true
recognizer, badGcd as Nat.gcd    : REJECTED             recognizer, badBitwise as ~  : REJECTED
```

and the `run_meta` self-test at the foot of `Lean4Lean/Primitive.lean` still accepts all
eighteen primitives of the real prelude. Both witnesses die; neither real primitive moves.

## 5. Corrections to the brief and to the previous handoff

* *"`unfoldNatWellFounded` is the single blocker, and the route is a fuel induction at numerals
  whose one prerequisite is a `whnfCore.WF`/`unfoldDefinition.WF` returning a defeq witness."*
  **Wrong on both halves.** That prerequisite is not needed (§3(c) removes it with two
  accept-set-neutral checks). And the route could not have worked anyway: the statement it was
  aiming at was false (§1), and the induction step it needed was underivable (§2). Neither of
  those is visible from the `whnfCore` framing.
* *"`unfoldNatWellFounded` not by a checked conversion: the fixpoint equation is propositional,
  not definitional, so a `checkedIsDefEq` there returns `false`."* **Correct, and it survives**
  — but it was over-generalised into "no checked conversion can help here", which is false. The
  *fixpoint* equation is propositional; the *fuel recurrence* and the two reductions of §3(c)
  are definitional, and checked conversions get all three of them.
* The previous handoff's §6 ordering ("`Nat.bitwise` … deepest, attack last") is fine for the
  proof, but the two *implementation* gaps are identical in both branches and were cheaper to
  fix together than apart.

## 6. Kernel Arena and the other gates **[machine-checked]**

`Lean4Lean/Primitive.lean` changed, so the accepted set *did* move (strictly smaller) and these
runs are a measurement, not a consistency check on unchanged code.

| | |
| --- | --- |
| Kernel Arena, `lean4lean-local`, before | 185 correct / 6 either / 0 incorrect |
| Kernel Arena, `lean4lean-local`, after | 185 correct / 6 either / 0 incorrect, twice |
| sorry census | 19 → 19 |
| `scripts/dup-names.lean` | no duplicates |
| `Verify/Guard.lean` guards 1–3 | 25 frozen axioms ✓; `kernel_sound` within whitelist ✓ (proof INCOMPLETE); cone gaps 54/54 ✓ |
| `Verify/Soundness.lean` | `stdPrelude matches the toolchain's core declarations ✓`, `stdPrelude accepted by addDecl ✓` |
| `run_meta` self-test at the foot of `Primitive.lean` | all eighteen primitives accepted |

The `init` arena test replays the whole prelude export in declaration order, so it is what
checks that the newly required constants (`Nat.mod_lt`, `Nat.pos_of_ne_zero`,
`Nat.lt_of_lt_of_le`, `Nat.le_of_lt_succ`, `Nat.div_lt_self`, `Nat.le.refl`) really do precede
`Nat.gcd`/`Nat.bitwise`. They do.

## 7. Pick up first

1. **The `Nat.gcd` fuel induction.** Everything it needs is now checked. The available facts,
   all at `c.venv`, all as `IsDefEqU` under the recognizer's binders:
   * `E m n ≡ fix h F (pack m n)`  (§3(c), first check)
   * `fix h F a ≡ go (eager (succ (h a))) a p`  (§3(c), second check, under a fresh `a`)
   * `eager x ≡ Condition.bool.ite Nat #[Nat.beq x x] x x` (unchanged)
   * `h (pack m n) ≡ m`  (§3(a)) — instantiate at numerals to make `eager` peel via
     `Condition.check.WF_bool` and `HasPrimitives.natBEq`
   * `go (succ fuel) (pack m n) hb ≡ Condition.natEq.dite #[m, 0] n (go fuel (pack (n % m) m) prf)`
     (§3(b)) — this is `reflects_fuel_go`'s recurrence, with `Ok` indexed by the fuel bound
   * the two `rhs` equations (unchanged; now redundant, kept because they are what force `F`'s
     body to match `Nat.gcd.eq_def`'s shape, and dropping them would widen the accepted set)
   The induction is `Nat.gcd`'s usual one: fuel `k`, invariant `m ≤ k`, step `n % m < m ≤ k`.
   `VEnv.reflects_fuel_go` is parametrised by the wrapper, base and recurrence already.
   Two pieces are missing and are cheap: a **pinned** variant of `Condition.check.WF_natEq`
   (`P = .natEq`, `D = .const ``Nat.decEq []`), by analogy with `Condition.check.WF_natLE_pinned`,
   and the `Nat.beq` counterpart of `ReflectsCondAppD.natLE_le` (`Nat.beq a b = (a == b)`, so the
   selection is decided by `HasPrimitives.natBEq` rather than `natBLE`).
2. **`Nat.bitwise`** afterwards. Same facts; the induction is on `n` (its measure), the
   conditional machinery is `Condition.natEq` at `Nat` and `Bool` plus `Condition.bool` at `Nat`
   (all three `Condition.check.WF*` are proved), and `ReflectsNatBitwise` is second order and
   relativized to every extension, so the transport at the end is not a single `IsDefEqU.mono`.
3. `VEnv.ReflectsCondAppD`'s `VExpr.WF` premise is **negative**, so it is not monotone: all
   reduction happens at `c.venv` with one `IsDefEqU.mono` at the very end. Unchanged, still
   forced.

## 8. Carried over, still correct **[machine-checked unless noted]**

* The `Nat.mod` and `Nat.div` branches are **proved** and untouched: `VEnv.reflects_mod_of_equations`,
  `reflects_div_of_equations`, `reflects_fuel_go/mod/div`, `IsDefEqU.instGo5`, `beta_wf`,
  `diteNat_reduce`, `mod_step1/2`, `div_step1/2`, `trExprS_goApp`, `trExprS_modEq1/2_inv'`,
  `trExprS_divEq1/2_inv'`, `goApp3/5_typed`, `app2_congr_arg1'`.
* `TypeChecker.Condition.check.WF` (both arms), `Reflection.check.WF`, `checkITE.WF`,
  `checkNatDITE.WF`, `Condition.check.WF_bool`, and `WF_natLE` / `WF_natEq` / `WF_boolCond` /
  `WF_natLE_pinned`.
* `trExprS_iteNat_inv'` / `diteNat_inv'` carry **no `IsUnique` side condition** — the heads are
  constant-only. `IsUnique` is `False` at a `.proj`, so that vacuity surface stays narrow.
* Π-injectivity here is inherited taint, not a new hole.
* The C++ kernel has **no primitive-definition recognizer at all** (measured), so every
  discrepancy here is a divergence by construction and the Arena's accepted set is the only
  external constraint. Note the flip side, now that §1 exists: the C++ kernel accelerates
  `Nat.gcd` at literals *by name*, with nothing checked about the declaration — so the
  environment §1 builds is one where the C++ kernel's accelerator and the declaration's own
  reduction behaviour disagree. That is upstream's problem, not recorded as ours.
* **The verification can never recover a subterm's type from the fact that an application
  containing it type-checks.** `TrExprS.app` and `VExpr.WF.app_inv` hand back the domain the
  application *invented*. §3(b) reads the fuel bound's domain off `go`'s own type for exactly
  this reason.
* Method: `rw [if_pos h]` rewrites only the first matching `if` (use `simp only`);
  `ClosedN.liftN_eq (Nat.zero_le 0)` pins the depth to `0` (use `(Nat.zero_le _)`); `mkAppB` is
  not reached by unfolding `mkApp2`; `FVarsIn` side conditions are discharged structurally, not
  by feeding `h.fvarsIn` to `simp`; the last `unless … do fail` inside a binder block is
  `.throw`, not `M.WF.bindThrow`; `hasType_lastFVar`, not `…0`, when the domain is not closed;
  `set_option … in` goes *before* the doc comment. `.rest` needs `maxHeartbeats 4000000`.
