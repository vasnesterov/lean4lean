# `checkPrimitiveDef.WF.rest` — inventory, statement audit, and what moved

Stream scope: `Lean4Lean/Primitive.lean`, `Lean4Lean/Verify/Primitive.lean`,
`Lean4Lean/Verify/Environment/Boundaries.lean`.  Everything below is separated into
**[machine-checked]** (a `lake build` succeeded on it, or a run of the Kernel Arena produced
it) and **[source]** (read off the code, not proved).

Bottom line, up front:

* the statement is **not** false, and **not** defective — no auto-bound implicit, no
  under-constrained quantifier, and it is not vacuous **[machine-checked]**;
* the *first* step the previous analysis identified — the `bugs-found.md` item 4 remedy,
  which had been applied to fifteen branches but not to these four — **is now done**, in
  `Lean4Lean/Primitive.lean`, with the Kernel Arena unchanged at **185 / 6 / 0**
  **[machine-checked]**;
* one new spec, `TypeChecker.M.WF.withCheckedLocalDecl`, is proved in
  `Lean4Lean/Verify/Primitive.lean` **[machine-checked]**;
* the `sorry` itself is **not** closed and is **not** closeable in one stream: what is left is
  four pieces of genuinely new reflection metatheory, priced in §5;
* a separate, previously undocumented **divergence from the C++ kernel** turned up on the way
  (§6): `Nat.pow` and `Nat.shiftLeft` numeral-size guards.

---

## 1. Inventory: what the recognizer does and what its `WF` must say

`Lean4Lean.Environment.checkPrimitiveDef : DefinitionVal → M Bool`
(`Lean4Lean/Primitive.lean`) is called from `Lean4Lean/Environment.lean:43`:

```
checkConstantVal env v.toConstantVal (← checkPrimitiveDef v)
```

so it runs **before** `checkConstantVal`, on a `DefinitionVal` nothing has type-checked, and
its `Bool` result is the `allowPrimitive` flag that lets `checkConstantVal` accept a name in
`Environment.primitives`.  It returns `false` for any name it does not recognize (and for any
`v.safety ≠ .safe`), and otherwise either returns `true` or throws.

It recognizes **eighteen** names, in three groups **[source]**:

| group | names | what is checked |
| --- | --- | --- |
| structural recursion (9) | `Nat.add`, `Nat.pred`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.beq`, `Nat.ble`, `Nat.shiftLeft`, `Nat.shiftRight` | value type-checks at `Nat → Nat → Nat` (resp. `Nat → Nat`, `… → Bool`); two defining equations under `withLocalDecl`-bound `Nat`s |
| destructuring (3) | `Nat.land`, `Nat.lor`, `Nat.xor` | value is *syntactically* `Nat.bitwise f`; `f`'s truth table |
| literal type (2) | `Char.ofNat`, `String.ofList` | `v.type` compared with `==` (`Expr.eqv`), plus the ambient `Char`/`List Char` facts |
| **fuel / well-founded (4)** | **`Nat.mod`, `Nat.div`, `Nat.gcd`, `Nat.bitwise`** | **the four in `checkPrimitiveDef.WF.rest`** |

The obligation, `PrimitiveResult (ves.venv .safe) v allow`
(`Verify/Environment/Boundaries.lean:21`), has three fields; when `allow = true`:

1. `safe` : `v.safety = .safe`;
2. `no_level_params` : `v.levelParams = []`;
3. `preserves` : for **every** `venv ≥ ves.venv .safe` with `venv.WF` and
   `venv.HasPrimitives`, every `safety`, and every `ci'` with
   `TrDefVal safety venv (.defnInfo v) ci'` and `ci'.WF venv`, if
   `venv.addConst v.name ci'.toVConstant = some env'` then
   `(env'.addDefEq ci'.toDefEq).HasPrimitives`.

Fields 1 and 2 are one-liners from the guards at the head of each branch.  Field 3 is the
whole content, and by `VEnv.PrimField` / `VEnv.HasPrimitives.addDef`
(`Verify/Primitive.lean:637,809`) it reduces, for a name `n`, to the **single**
`HasPrimitives` field that `n` is responsible for — the other twenty-one transfer across the
step by `HasPrimitives.extend`.  For the four here **[source]**:

| branch | field to produce |
| --- | --- |
| `Nat.mod` | `env'.ReflectsNatNatNat ``Nat.mod`` Nat.mod` |
| `Nat.div` | `env'.ReflectsNatNatNat ``Nat.div`` Nat.div` |
| `Nat.gcd` | `env'.ReflectsNatNatNat ``Nat.gcd`` Nat.gcd` |
| `Nat.bitwise` | `env'.ReflectsNatBitwise` — second order, relativized to every extension |

Where the proof stops: `checkPrimitiveDef.WF` (`Boundaries.lean:86`) splits on the name, sends
the four to `checkPrimitiveDef.WF.rest` **before unfolding anything**, and discharges the other
fourteen names in ~1100 lines below.  `.rest` is `sorry`.  It is 1 of the 20 in
`scripts/sorry-census.lean` **[machine-checked]** — the census still reports exactly 20 after
this stream's work.

---

## 2. Statement audit

Both defect classes were checked against the *elaborated* signature, printed with
`set_option pp.explicit true` **[machine-checked]**:

```
@checkPrimitiveDef.WF.rest : ∀ {env : Lean.Kernel.Environment} {ves : VEnvs}
  (wf : VEnvs.WF env ves) (v : Lean.DefinitionVal) (fuel : FuelConfig),
  Or (v.name = `Nat.mod) (Or (v.name = `Nat.div) (Or (v.name = `Nat.gcd)
    (v.name = `Nat.bitwise))) →
  @TypeChecker.M.WF Bool (@TypeChecker.VContext.mk' env ves wf
      Lean.DefinitionSafety.safe v.levelParams fuel) { }
    (Environment.checkPrimitiveDef v)
    fun allow x => PrimitiveResult (ves.venv Lean.DefinitionSafety.safe) v allow
```

* **Auto-bound implicits: none.**  The signature has exactly the five binders written in the
  source.  `env` and `ves` are both *used* — `env` in `VEnvs.WF env ves` and in
  `VContext.mk'`, `ves` in `VEnvs.WF`, `VContext.mk'` *and* the conclusion
  (`ves.venv .safe`), so neither is a silently captured stand-in for something else.  No
  universe variable is auto-bound.  `PrimitiveResult` likewise has exactly its three declared
  parameters.
* **Under-constrained scope: no.**  The only quantifiers not fixed by the theorem's binders
  are the four inside `PrimitiveResult.preserves` (`safety`, `venv`, `env'`, `ci'`), and every
  one carries a hypothesis pinning it: `checked ≤ venv`, `venv.WF`, `venv.HasPrimitives`,
  `TrDefVal safety venv (.defnInfo v) ci'`, `ci'.WF venv`, and
  `venv.addConst v.name ci'.toVConstant = some env'`.  The generality (an *arbitrary* later
  extension, at an *arbitrary* safety) is what the consumer in
  `Verify/Environment/Checker.lean:211` actually applies it at, not slack.
* **Non-vacuity.**  `M.WF c s x Q` is vacuous when `x` can never return `.ok`.  It can: the
  `run_meta` self-test at the foot of `Lean4Lean/Primitive.lean` runs `checkPrimitiveDef` on
  every one of the eighteen primitives of the current prelude — `Nat.mod`, `Nat.div`,
  `Nat.gcd` and `Nat.bitwise` included — and fails the build unless each returns `.true`;
  and `Verify/Soundness.lean` prints `stdPrelude accepted by addDecl ✓`, which drives the same
  four branches through `addDecl` **[machine-checked, both at build time]**.  The `hrest`
  hypothesis is inhabited by construction.

**So `checkPrimitiveDef.WF.rest` is open, not false.**  The refutation route the previous note
suggested (a declaration that passes the recognizer while leaving an untranslatable term in
the `EquivManager`, breaking `VState.WF`) was examined and **not** pursued to a witness: it
requires an `Environment` with a `ves.WF env` model in which one of the recognizer's baked-in
constants (`Nat.modCore.go`, `Nat.div_rec_fuel_lemma`, `@LE.le Nat _`, `Nat.beq`, …) is
present but degenerate.  Building that *and* proving `ves.WF` of it is strictly more work than
the fix, and the fix removes the route entirely (§3).  **[source]**

---

## 3. What closed on the implementation side

`Lean4Lean/Primitive.lean`, this stream.  Every comparison the four branches make — directly
or through a helper they share — now type-checks *both* of its sides, and every free variable
they introduce now has its domain checked.  Concretely:

* **`Condition.check`**: `inferType cond.prop` → `checkedTypeIs cond.prop`.  Confirming and
  sharpening the previous stream's reading **[source]**: of the three `inferType` calls, only
  `cond.prop` was genuinely uncovered — `asBool` and `proof` both occur inside the term that
  the following `checkType e` checks.  But the *right-hand sides* it compared against
  (`Nat → Nat → Prop`, `Nat → Nat → Bool`, `Bool → Prop`, `Bool → Nat → Nat → Nat`,
  `fun a _ : Nat => a`, …) were unchecked as well, and the previous note did not list them;
  they are now checked too.  `isProp (← inferType proof)` → `isProp (← checkType proof)`.
* **`Reflection.check` / `checkITE` / `checkNatDITE`**: `checkedTypeIs` and `checkedIsDefEq`
  throughout (7 comparison sites).
* **`unfoldNatWellFounded`**: `inferType` → `checkType` at both sites; `checkedIsDefEq` at its
  three comparisons.
* **`lambdaTelescope` / `forallTelescope`**: their binder domains are now checked.
* **`unfoldWellFounded` deleted.**  It was listed in `Boundaries.lean`'s note as a site
  needing the fix; it is **dead code** — no call site anywhere in the tree **[machine-checked:
  `grep -rn unfoldWellFounded --include=*.lean` finds only the definition and that note]**.
  Deleting it is behaviour-preserving and shrinks the surface the proof has to cover.
* **`withCheckedLocalDecl`** (new): `checkIsType` on the domain, then `withLocalDecl`.  This
  is a gap the previous analysis did **not** record and it is independent of the comparison
  one: `M.WF.withLocalDecl0` demands a `TrExprS` *and* an `IsType` for the binder's domain,
  and the domains these branches bind — `1 ≤ y`, `Nat.succ x ≤ Nat.succ fuel`,
  `r.type p Bool.true`, `.arrow (Not p) Nat`, and the type `unfoldNatWellFounded` recovers
  from a `whnf` — are built from constants `VEnv.HasPrimitives` requires only to be
  *present*.  All 17 binders in the four branches and their helpers now use it.

Deliberately **not** changed: `defeqT1` / `defeq2`, whose binders are `q(Nat)` / `q(Bool)` and
whose `IsType` facts the fifteen closed branches already derive from `NatFacts`.  Touching
them would perturb ~1100 lines of working proof for no gain.

Verification **[machine-checked]**:

* `lake build Lean4Lean.Primitive` — succeeds, so the `run_meta` self-test still accepts all
  eighteen primitives with every new check in place;
* `lake build Lean4Lean.Verify.Environment.Boundaries` — succeeds, the fifteen closed branches
  are undisturbed, the only `sorry` is `.rest` (line 107 after the note was rewritten);
* full `lake build` — succeeds; guards 1, 2 and 3 all pass (`54/54` implementation gaps,
  unchanged); `stdPrelude accepted by addDecl ✓`.

### Kernel Arena

| | correct | either | incorrect |
| --- | --- | --- | --- |
| before (`b32b29b`, clean tree) | 185 | 6 | 0 |
| after | 185 | 6 | 0 |

**[machine-checked, `cd ~/lean-kernel-arena && uv run lka.py run --checker lean4lean-local`]**

### `divergences.md`

The accepted set does not change on any well-formed environment: every term newly checked is
either a closed literal built from constants the branch already requires to be present, or a
subterm of a term the branch already checked.  The existing `checkPrimitiveDef` entry's fourth
point already describes this remedy in general terms; it has been extended to say that it now
covers all eighteen branches and the binders as well as the comparisons.

---

## 4. What is proved, and fired at a witness

`TypeChecker.M.WF.withCheckedLocalDecl` (`Lean4Lean/Verify/Primitive.lean`, no `sorry`)
**[machine-checked]**:

```
protected theorem M.WF.withCheckedLocalDecl {s : VState} {f : Expr → M α} {Q} {name ty bi}
    (hty : ty.FVarsIn (· ∈ c.vlctx.fvars))
    (H : ∀ ty' id (cwf' : c.MLCWF (.vlam id name ty ty' bi c.mlctx)) s', s ≤ s' →
      c.TrExprS ty ty' → c.IsType ty' →
      M.WF (c.withMLC (.vlam id name ty ty' bi c.mlctx) (wf := cwf')) s' (f (.fvar id)) Q) :
    M.WF c s (Lean4Lean.Environment.withCheckedLocalDecl name bi ty f) Q
```

It is the exact difference between `M.WF.withLocalDecl0` (which needs the domain's `TrExprS`
and `IsType` handed to it) and what the four branches can supply (nothing, before the check).
Non-vacuity: the conclusion is about a computation that demonstrably returns `.ok` — all 17
binders of the four branches go through `withCheckedLocalDecl` on real domains in the
build-time self-test — and the hypothesis `H` receives two facts (`c.TrExprS ty ty'`,
`c.IsType ty'`) that are not derivable without it, which is why it is not a restatement of
`withLocalDecl0`.

---

## 5. What is open, with the exact failing step

The `sorry` is metatheory now, not plumbing.  The fifteen closed branches all check a
*structural* recursion, for which `VEnv.reflects_rec2` / `reflects_rec2_tail` /
`reflects_rec2_diag` (`Verify/Primitive.lean:258,274,293`) suffice.  None of the four does.
In dependency order **[source]**:

**(a) A `Condition` reflection lemma — needed by three of the four, missing entirely.**
The `mod`/`div`/`bitwise` equations are stated with `Condition.ite` / `Condition.dite`, i.e.
`@ite`/`@dite` at the *instance* `cond.dec`.  What `Condition.check` establishes is
`cond.dec ≡ fun x y => r.toDec (cond.prop x y) (asBool x y) (proof x y)` together with
`r.ite p Bool.true H ≡ fun α a _ => a` and `r.ite p Bool.false H ≡ fun α _ a => a` (and the
`dite` analogues through `r.ofTrue`/`r.ofFalse`).  Turning that into

> `Condition.natLE.ite α #[a, b] t e ≡ t` when `a ≤ b`, `≡ e` otherwise

goes through `VEnv.HasPrimitives.natBLE` (the branch checks `env.contains ``Nat.ble``, and
`Condition.natLE`'s `asBool` **is** `Nat.ble`).  There is no such lemma anywhere.  Estimated
the largest single reusable piece; write it first, at the `VExpr` level in
`Verify/Primitive.lean`, in the style of `reflects_natBitwiseApp`.

**(b) `Nat.mod` and `Nat.div`: fuel induction.**  Their equations mention `Nat.modCore.go` /
`Nat.div.go`, which the recognizer constrains **only** at `Nat.succ fuel`; the `fuel = 0` case
is unreachable, and staying inside that must be carried as the `Nat.succ x ≤ fuel` invariant
of the induction.  With (a) in hand this is an ordinary strong induction on `fuel`.

**(c) `Nat.gcd`, `Nat.bitwise`: a spec for `unfoldNatWellFounded`.**  This is the deep one and
should be attacked **last**.  The fixpoint equation it establishes is *not* assembled from
`isDefEq` calls — it is read off structural pattern matches against `WellFounded.Nat.fix`'s
`Nat.rec` skeleton, on the results of `whnfCore` and `unfoldDefinition`
(`Primitive.lean`, `unfoldNatWellFounded`: `let .const ``WellFounded.Nat.fix [_,_] := fix`,
`unless (α, motive, f, F, a) == (α', motive', f', F', a')`, `unless ih == .app (.app natRec t) y`).
Any proof has to *reconstruct* `fix α motive f F a ≡ F a (fun y _ => fix α motive f F y)` from
those syntactic checks, which needs `whnfCore.WF` / `unfoldDefinition.WF` in a form that hands
back a defeq witness for the *whole* application, and then an argument that the `Nat.rec`
skeleton it matched really computes the fixpoint.

**(d) `Nat.bitwise`'s field is second order.**  `VEnv.ReflectsNatBitwise`
(`Verify/Typing/Expr.lean:241`) quantifies over every extension `env'` and every `f`, `g` with
`env'.ReflectsBoolBoolBool f g`.  The reflections its equation consumes (`Nat.add`, `Nat.div`,
`Nat.mod`, `Nat.beq` — all four required present by the branch) transfer to `env'` by
`VEnv.ReflectsNatNatNat.mono`, so this is not a blocker, but the induction is on `n + m`, not
on either argument, and the recursive occurrence is at `n / 2`, `m / 2`.

**Ranking:** (a) ≪ (b) < (d) ≪ (c).  A stream that lands (a) and (b) closes half the branch
set and produces the reusable piece; (c) is where the remaining cost lives, and it is the one
place where the honest answer may be to change `unfoldNatWellFounded` to *produce* its
equation by `checkedIsDefEq` rather than by structural matching, so the spec can read it off
instead of reconstructing it.  That is an implementation change with an Arena gate.

---

## 6. C++ kernel comparison — one finding, outside this stream's files

**The C++ kernel has no primitive-definition recognizer at all.**  `grep -rn
'checkPrimitive\|check_primitive' ~/lean4/src` finds nothing **[machine-checked]**; the only
primitive-shape check anywhere in `~/lean4/src/kernel` is `check_eq_type` in `quot.cpp`, run
by `add_quot`.  The `reduceNat` fast paths in `type_checker.cpp:717-730` trust `Nat.add`,
`Nat.mod`, … *by name*.  So a brief that speaks of "the C++ kernel's `checkPrimitiveInductive`
recognising only `Bool` and `Nat`" is describing **our** `checkPrimitiveInductive`
(`Primitive.lean`), which does recognise exactly `Bool` and `Nat`; C++ has no counterpart.
This whole recognizer is already recorded in `divergences.md` as a deliberate strengthening.

**New, undocumented divergence — numeral-size guards on `Nat.pow` and `Nat.shiftLeft`.**
`~/lean4/src/kernel/type_checker.cpp` bounds the numerals its GMP fast paths produce, at
`g_nat_max_size` = 128 MB by default (`LEAN_NAT_MAX_SIZE`), and throws a clean
`kernel_exception` when a result would exceed it — `check_nat_size` at `:298`, applied in
`infer_lit` (`:319`), `reduce_bin_nat_op` for `add`/`sub`/`mul` (`:656`), `reduce_pow`
(`:670`) and `reduce_shiftLeft` (`:687`); `get_count_arg` (`:308`) additionally throws when
`Nat.pow`'s exponent or `Nat.shiftLeft`'s shift does not fit in `unsigned int`.
`Lean4Lean/TypeChecker.lean` has **no** size guard: `reduceBinNatOp` (`:473`) computes
unconditionally, and `reducePow` (`:480`) bounds only the *exponent*, at
`reducePowMaxExp = 1 <<< 24`, and on exceeding it **declines to reduce** (`return none`)
rather than erroring.  Differing inputs **[source]**:

* `Nat.pow 2 (2^25)` — C++ computes a 4 MB literal (`1 > 128MB / 2^25 = 4` is false);
  lean4lean returns `none` from `reducePow`, falls through to unfolding `Nat.pow`'s
  definition, and grinds through 2^25 unary steps on multi-megabyte numerals.  *C++ succeeds
  in milliseconds; lean4lean effectively hangs.*
* `Nat.pow 2 (2^31)` — C++ throws "refused to evaluate `Nat.pow`"; lean4lean hangs as above.
* `Nat.shiftLeft 1 (2^40)` — C++ throws; lean4lean asks GMP for a 128 GB integer.
* `Nat.mul` of two 100 MB literals, or a source literal above 128 MB — C++ throws; lean4lean
  computes / accepts.

`Lean4Lean/TypeChecker.lean` is not this stream's file, so nothing was changed there.  The
entry has been added to `divergences.md`; whether to *fix* it (mirror `check_nat_size`, which
would also remove the `reducePowMaxExp` hang) is a decision for whoever owns that file.

---

## 7. Pick up first

> **UPDATE (this session).**  §5's **(a)** and **(b)** are now **proved**, in
> `Lean4Lean/Verify/Primitive.lean`: `VEnv.reflects_condApp` /
> `reflects_condApp_natLE` / `ReflectsCondApp.natLE_le` (the `Condition` reflection lemma,
> with a `condApp` shape that serves `ite` and `dite` alike) and `VEnv.reflects_fuel_go` /
> `reflects_fuel_mod` / `reflects_fuel_div` (the fuel induction, one induction parametrised
> for both).  See `docs/handoff-adddecl.md` §5.
>
> What is left of them is **plumbing, not mathematics**: instantiating the two
> `withCheckedLocalDecl` binders and β-reducing through `Reflection.ite`'s four-fold λ, to
> turn the recognizer's checked equations into `reflects_condApp`'s `hsel` and
> `reflects_fuel_go`'s `hgo`.  The tools for exactly that (`IsDefEqU.inst0`,
> `IsDefEqU.beta'`, `IsDefEqU.app_congr_fn'`, `IsDefEqU.app2_congr_fn`) are in the same file.
> **That is the next task.**  The list below is otherwise unchanged; item 1 is done.


1. **(a) of §5** — the `Condition` reflection lemma.  It is the only piece all of `mod`, `div`
   and `bitwise` need, it is self-contained at the `VExpr` level, and it belongs in
   `Verify/Primitive.lean` next to `reflects_natBitwiseApp`.
2. Then **(b)**, `mod` and `div`, which are the same proof twice.
3. Do **not** re-audit the statement (§2) and do **not** re-derive the bug-4 diagnosis (§3);
   both are settled.  In particular the `Boundaries.lean` note that used to say these four
   "still compare terms neither side of which has been type-checked" is **out of date** and
   has been rewritten.
4. Before touching `unfoldNatWellFounded`'s spec, decide (c)'s implementation question: read
   the equation off structural matches, or make the recognizer produce it with
   `checkedIsDefEq`.  The second is cheaper to verify and costs an Arena run.
