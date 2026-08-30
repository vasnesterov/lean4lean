# Is there a proof of `False` behind the pre-fix primitive-recognizer defect?

**Assignment** (issue #39, user's comment): *"Please give the complete proof of `False` that is
accepted by lean4lean (old version, before forking)"* — i.e. produce a declaration sequence that
pre-fix `Lean4Lean.addDecl` accepts and from which `False` is derivable, **or** show that the
pre-fix gate makes that impossible.

## Verdict: (B). There is no such witness via this defect.

**The pre-fix gate does not pin `Nat.gcd`'s reduction *behaviour*, but it does pin its *values*.**
Every declaration named `Nat.gcd` that the pre-fix `checkPrimitiveDef` accepts satisfies, as true
propositions of the theory,

```
∀ m,   v 0 m       = m
∀ n m, v (n+1) m   = v (m % (n+1)) (n+1)          -- `%` = the environment's own, gated, `Nat.mod`
```

and those two recurrences determine the function: `∀ a b, v a b = Nat.gcd a b`. The same holds for
`Nat.bitwise`. So the equations `reduceNat` asserts by name-dispatch are **true** of any accepted
declaration, and the route to `False` — which is real, and machine-checked below — has nothing to
carry.

**What was broken is the recognizer's postcondition, not the theory.** `VEnv.HasPrimitives`
demands an `IsDefEqU` — *definitional* reduction at numerals — and `badGcd` is stuck, so
`checkPrimitiveDef.WF.rest` was a false statement. That blocks `kernel_sound` for such an
environment. It does not make the kernel admit `False`. **The word "soundness" in issue #39's
title is not earned, and the negative here should retract it.**

A negative is not a proof of impossibility by exhaustion: see *Scope* below for exactly which
links are machine-checked and which are read off source.

## Code state

Rows were measured at **`5b5845b`** (= `f743c46^`), the last commit before the measure fix. The
`Nat.gcd` / `Nat.bitwise` gate logic there is the **same logic** as at the fork point `e0e3f6b`
and at `digama0/master`: the branches differ only in `isDefEq`/`inferType` versus
`checkedIsDefEq`/`checkType` (and, in `unfoldNatWellFounded`, a `defeq1` under an `.arrow`
pseudo-binder versus a `withCheckedLocalDecl`). The *checks made* — the unfolder, and the two
`gcd'` equations — are identical, so the argument below covers all three states.

**Both readings of "old version, before forking" were measured.** The whole table below was
produced twice, once in a worktree at `5b5845b` and once in a worktree at the fork point
`e0e3f6b`, and the two outputs are **identical row for row**.

Instrument: `scripts/primitive-false-audit.lean` (this stream), run with
`lake env lean scripts/primitive-false-audit.lean` in a worktree at the commit under test.
Companion: `scripts/primitive-wf-refutation.lean` (the earlier stream's before/after table).

## Machine-checked: the escape route around `reduceNat` is real

`Lean4Lean/TypeChecker.lean:514` reduces a two-argument application of the *constant named*
`Nat.gcd` at two numerals to the value of the **real** `Nat.gcd`. Nothing the recognizer records
is consulted. The name dispatch is escaped by aliasing, and this is measured, not argued —
`Nat.gcd`'s own value is `fun m n => Nat.gcd._unary ⟨m, n⟩`, and comparing two *constants* at
arity 0 never enters `reduceNat`:

```
kernel: (Nat.gcd = gcdAlias) by rfl : true
kernel: Nat.gcd 4 6 = 2        by rfl : true
kernel: gcdAlias 4 6 = 2       by rfl : true
```

So **if** a body disagreeing with gcd could be declared under the name `Nat.gcd`, `False` would
follow in four declarations and no cleverness:

```lean
def myAux    : Nat → Nat → Nat := <the disagreeing closed value>   -- ordinary def, no gate
def Nat.gcd  : Nat → Nat → Nat := <the same closed value>          -- must pass checkPrimitiveDef
theorem e1 : Nat.gcd = myAux    := rfl   -- delta on both sides; reduceNat does not fire
theorem e2 : Nat.gcd 4 6 = 2    := rfl   -- reduceNat: the real gcd
theorem e3 : myAux   4 6 = 3    := rfl   -- delta: the declared body
example : False := absurd ((congrFun (congrFun e1 4) 6).symm.trans e2 |>.symm.trans e3) (by decide)
```

The whole question is therefore the second line, and only the second line.

## Machine-checked: no disagreeing body got through

Pre-fix (`5b5845b`), `Environment.checkPrimitiveDef` asked whether it would accept each body
*under the name* `Nat.gcd`, alongside what the Lean kernel makes of that body at `4, 6`:

```
Nat.gcd 4 6: ACCEPTED | =2(gcd): true  | =3(wrong): false
badGcd  4 6: ACCEPTED | =2(gcd): false | =3(wrong): false     <- gcd's body, unevaluable measure
bigGcd  4 6: ACCEPTED | =2(gcd): true  | =3(wrong): false     <- gcd's body, measure 2*m+7
w1      4 6: rejected | =2(gcd): false | =3(wrong): true      <- wrong base case
w2      4 6: rejected | =2(gcd): false | =4(wrong): true      <- extra +1 on the recursive call
w3      1 5: rejected | =1(gcd): false | =2(wrong): true      <- wrong second recursive argument
s1      4 6: rejected | =2(gcd): true  | =3(wrong): false     <- right values, structural recursion

Nat.bitwise : ACCEPTED    badBitwise : ACCEPTED    wb (swapped bit test) : rejected
```

Read the rows this way. The two `ACCEPTED` non-standard rows (`badGcd`, `bigGcd`) both have
**gcd's own body**; the measure is the only thing that varies, and varying it can only make the
definition *stuck* (`badGcd`) or give it *more fuel* (`bigGcd`) — never a different value, because
`WellFounded.Nat.fix.go`'s fuel-zero case is `(Nat.not_succ_le_zero _ hfuel).elim`, a stuck
`False.elim`, and it is unreachable anyway. Every row whose *body* disagrees with gcd is rejected.

## Read off source: why that is not luck

Write `v` for the accepted declaration's value, and let the recognizer's own names be as in
`unfoldNatWellFounded`. `Nat.gcd.eq_def` is
`∀ m n, m.gcd n = ite (m = 0) n ((n % m).gcd m)`, so with `fvs = #[m, n]` the unfolder's `rhs` is

    rhs(m,n)  =  ite (m = 0) [inst] n (v (n % m) m)

and `gcd'` is `fun m n => rhs(m,n)`. Five facts, all present pre-fix:

* **(P1)** `v m n ≡ WellFounded.Nat.fix h F a₀(m,n)` — the unfolder reaches `fix` by
  `whnfCore`/`unfoldDefinition`/`whnfCore` on `v m n`, and those are sound reductions. (Post-fix
  this same conversion is additionally *checked*; the fix's commit calls that accept-set neutral.)
* **(P2)** `rhs(m,n) ≡ F a₀(m,n) (fun y _ => fix h F y)` — the unfolder's last
  `isDefEq rhs rhs'`. This is the **only** constraint the pre-fix gate places on `F`.
* **(P3)** `fix h F a = F a (fun y _ => fix h F y)` — `WellFounded.Nat.fix_eq`, a Lean theorem
  with no side conditions. (In a from-scratch environment `WellFounded.Nat.fix` is itself
  attacker-supplied, since it is not in `Environment.primitives`; the unfolder's structural
  checks nevertheless pin `fix a ≡ go (eager (h a + 1)) a _`, `eager x ≡ ite (Nat.beq x x) x x`,
  and `go (t+1) x _ ≡ F x (fun y _ => go t y _)`, from which `go_congr` — its fuel-zero case
  discharged by `h x < 0` — and then `fix_eq` follow. This is the least mechanised link.)
* **(P4)** `rhs(0, m) ≡ m` and `rhs(n+1, m) ≡ v (Nat.mod m (n+1)) (n+1)` — the branch's two
  `gcd'` equations. They look vacuous, and against `v` they nearly are; what they actually pin is
  the *conditional and the instances*: that `ite` selects then/else at `instDecidableEqNat 0 0`
  and `instDecidableEqNat (n+1) 0`, and that the `HMod.hMod`/`Nat.instMod` in `eq_def`'s body is
  the raw `Nat.mod`.
* **(P5)** `Nat.mod` is the real mod: its name is in `Environment.primitives`, so it can only
  enter the environment through its own branch, which pins it definitionally at numerals by the
  `Nat.modCore.go` fuel recurrence.

(P1)+(P2)+(P3) give `∀ m n, v m n = rhs(m,n)` propositionally; with (P4) at `(0,m)` and
`(n+1,m)` that is exactly

    ∀ m,   v 0 m     = m
    ∀ n m, v (n+1) m = v (Nat.mod m (n+1)) (n+1)

and with (P5) those are the real gcd recurrences. **Machine-checked** (in
`scripts/primitive-false-audit.lean`, no `sorry`):

```lean
theorem gcd_unique (g : Nat → Nat → Nat)
    (h0 : ∀ m, g 0 m = m) (hs : ∀ n m, g (n+1) m = g (m % (n+1)) (n+1)) :
    ∀ a b, g a b = Nat.gcd a b
```

`Nat.bitwise` runs the same way: the branch's single equation `bitwise' f n m ≡ e` puts the
recursion in the shape of `e`, built from the gated `Nat.add`/`Nat.div`/`Nat.mod`/`Nat.beq` and a
`Condition.natEq`/`Condition.bool` whose `ite` selection and `Nat.beq` reflection are checked; the
companion theorem is

```lean
theorem bitwise_unique (g : (Bool → Bool → Bool) → Nat → Nat → Nat)
    (hg : ∀ f n m, g f n m = <Nat.bitwise's body with g in the recursion>) :
    ∀ f n m, g f n m = Nat.bitwise f n m
```

**Where the measure freedom actually lives, then**: `h` controls only the *fuel*, and the fuel can
only be adequate (right value), too small (stuck at `False.elim`), or unevaluable (stuck at
`Nat.eager`). None of the three is a wrong value. That is why the defect degrades exactly one
thing — the `IsDefEqU` `HasPrimitives` demands — and nothing else.

## The other `reduceNat` entries: none is weaker

`Nat.add`, `pred`, `sub`, `mul`, `pow`, `beq`, `ble`, `shiftLeft`, `shiftRight` are pinned by
direct definitional recurrences on `v` itself, under genuine `withLocalDecl` binders — non-vacuous,
and by substitution they pin the function at every numeral *definitionally*, which is strictly more
than gcd got. `mod` and `div` are pinned by their `go` fuel recurrences in the same style.
`land`/`lor`/`xor` require `v` to be **syntactically** `Nat.bitwise <op>` for the environment's
(gated) `Nat.bitwise`, plus a `Bool` truth table for `<op>`. `Nat.succ` is a constructor of the
`Nat` that `checkPrimitiveInductive` pins structurally. None of the thirteen goes through
`unfoldNatWellFounded`, so none had this defect.

## An adjacent finding: two gates that constrain no value at all

`Char.ofNat` and `String.ofList` are in `Environment.primitives` and are **name-dispatched** —
`Lean4Lean.Expr.strLitToConstructor` expands a `String` literal into
`String.ofList [Char.ofNat c₁, …]` and `TypeChecker.tryStringLitExpansion` uses that expansion
inside `isDefEq`. Their branches check the *declared type*, syntactically, and **nothing about the
value**. Measured, at `5b5845b` and unchanged on current `master`:

```
recognizer, constant-function Char.ofNat  : ACCEPTED     -- fun _ => ⟨0, _⟩
recognizer, constant-function String.ofList : ACCEPTED   -- fun _ => ""
```

**This is not a route to `False`**, and the reason is worth stating because it is the same reason
the gcd answer is (B): the literal rule is *defined through* these constants, so any total
interpretation of them validates it. With a constant `Char.ofNat`, `'a'` and `'b'` denote the same
character — and every way of telling two characters apart goes back through `Char.ofNat`, so the
resulting theory is degenerate, not inconsistent. What it does produce is a **non-transitive
conversion** in the checker: `"a" ≡ String.ofList ['b'] ≡ "b"` while the literal-vs-literal
comparison answers `false`. That is incompleteness, not unsoundness. Recorded here rather than as
an issue: it is a gap in *our* recognizer, which `ORCHESTRATOR.md` says is ordinary work in
progress.

## Scope: what is measured, what is argued

**Measured** (kernel and recognizer, not the elaborator): every row of both tables above; the
aliasing fact that escapes `reduceNat`; `gcd_unique` and `bitwise_unique` as Lean proofs with no
`sorry`.

**Read off source, not machine-checked**: (P1)–(P5) and the reduction of the gate to those five
facts; the claim that `WellFounded.Nat.fix.go`'s fuel-zero case is unreachable; the
`Char.ofNat`/`String.ofList` consistency argument; the survey of the other thirteen branches.

**Not audited here.** At the fork point and on `digama0/master` the branch uses `isDefEq` on terms
that have not been type-checked (`v.type`, and both sides of the unfolder's comparisons). That is a
*separate*, already-recorded defect (`bugs-found.md`: a `Nat.pred` declared with type
`(fun _ : NoSuchType => Nat → Nat) NoSuchValue` was accepted, poisoning the `EquivManager`), fixed
in this repo by `213634c`/`043a4c8`. Whether a poisoned `EquivManager` can be steered into
accepting a *later* comparison in the same `M.run` is a different question from this one and was
not investigated. If someone wants a `False` out of the pre-fork checker, **that** is where to
look, not at the measure.

**"No witness" is not evidence of truth.** What carries the verdict is the argument from (P1)–(P5),
not the seven rejected rows; the rows are its non-vacuity check.

## Reproducing

```sh
git worktree add /tmp/prefix-wt f743c46^        # or e0e3f6b for the fork point
mkdir -p /tmp/prefix-wt/.lake && cp -al .lake/packages /tmp/prefix-wt/.lake/packages
cd /tmp/prefix-wt && lake build Lean4Lean.Primitive
cp <repo>/scripts/primitive-false-audit.lean scripts/
lake env lean scripts/primitive-false-audit.lean
```

On current `master` the two `badGcd`/`badBitwise` rows are expected to read `rejected` instead of
`ACCEPTED` — that is the measure fix, and it is the table `scripts/primitive-wf-refutation.lean`
documents. **Not measured by this stream**: `Lean4Lean/Primitive.lean` was being edited by another
stream throughout this round, so the script was only ever built and run in the two worktrees.

## What I would pick up first

The `EquivManager`-poisoning question in *Scope*, above. It is the only place left where the
pre-fork checker is weaker than this repo's in a way this audit did not close.
