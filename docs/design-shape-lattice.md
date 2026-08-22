# Options: removing `.type`-as-universe from the shape lattice

Status: **options memo, no code written.** Requested before authorising any change to
`Lean4Lean/Experimental/ShapeLogRel.lean` (6100 lines). WIP for the `indTy`
parameterisation is parked at `scratchpad/ShapeLogRel.indTy-wip4.lean`, not in the tree.

## The defect, stated once

`abbrev Shape.type : Shape n := .sort true` (`:68`) is used throughout as if it were *the*
universe of types. It is not: it is the universe of `Sort`-valued types, and it excludes
`Prop`. That was invisible while every shape classified by a sort happened to be
`Sort`-valued. Parameterising `ShapeS.indTy` on its sort — so that a `Prop`-valued inductive
can be described at all — makes `.indTy false` exist, and every use of `.type` that meant
"is a type" becomes a false claim.

Seven sites carry it. Six are lemmas or signatures and are already understood:
`HasTypeU.bot`, `HasType.toType`, `HasType.isType`, `HasTypePi.toType`, the four `LogRel`
fields, and the `WShape.HasDom` family. The seventh is the cause, and it is in the
defining equations of `Shape.hasType` (`:2493`):

```lean
def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .bot,   .forallE a b => hasType.core hasType b a fun _ => .type
  …
  | _+1, .lam f, .forallE a b =>
    hasType.core hasType b a (fun _ => .type) && hasType.core hasType f a (ShapeFun.app b)
```

`hasType.core … G` means "every codomain `y ∈ b` satisfies `y.HasType (G x)`". Both clauses
write `fun _ => .type` because there is no way to write *"`fun _ =>` whatever sort this Π
has"* — the target `.forallE a b` does not carry its own sort, and `.type` is what you write
when the lattice cannot say what you mean.

**The `.bot` clause is the one that matters.** It says a proof can inhabit `∀ x, P x` only
when every `P x` is `Sort`-valued — so a proof of a `Prop`-valued Π cannot be typed at its
own shape. That is precisely the case the `indTy` parameterisation exists to enable. Any
option that fixes `.lam` but not `.bot` is not a candidate.

---

## Option 4 (not on the original list): quantify over `Bool` by disjunction

**The change.** `r : Bool` is *finite*, so the existential the clause wants is already
writable in a `Bool`-valued function — quantify outside the `core` call rather than inside
`G`:

```lean
  | _+1, .bot, .forallE a b =>
    hasType.core hasType b a (fun _ => .sort false) ||
    hasType.core hasType b a (fun _ => .sort true)
```

and the same for the first conjunct of the `.lam` clause. Quantifying outside `core` is what
gives *one* sort for the whole codomain family, which is the correct reading — a Π-type's
codomains share a level.

**Cost.** Two clauses. No datatype change, no `Prop` change, no lattice change,
no `hasType.core` signature change. The lemma layer still moves to `IsType` — but that is
the change already approved, and `HasTypePi`/`HasTypeLam` are `def`s returning `Prop`, so
they can write `∃ r, HasTypePi b a r` directly with no trick at all.

**Does it fix `.bot`?** Yes — that is the clause it is written for.

**What could go wrong.**
- *Termination.* `hasType` recurses on `n` (the `Shape n` argument to `core` is one level
  down). Two `core` calls at the same `n` should be accepted, but this is the one thing I
  have not compiled and it is the whole option. **Verify first, before anything else.**
- *Cost of `decide`.* The clause evaluates `core` twice, duplicating the domain check, which
  does not depend on `G`. Semantically irrelevant, ~2× on that clause. Nothing currently
  `decide`s `HasType` (see Option 3), so this is likely unobservable.
- *Proof churn.* Every proof that unfolds these two clauses by `simp [hasType]` now sees a
  disjunction. Confined to `HasType.unfold` / `unfold_iff` / `lift` — a handful of sites.

---

## Option 1: `.forallE` carries its sort

**The change.** `| forallE : Shape → List (Shape × Shape) → ShapeS Shape` gains a `Bool`, so
the clause can write `fun _ => .sort r`.

**Cost.** `forallE` appears **322 times** in the file. Every construction site must decide
which sort to supply, and unlike `indTy` — where the answer is a property of the declaration
— the answer here is a property of the *codomains*, i.e. exactly what the clause was trying
to compute. Several construction sites will not have it to hand.

**Does it fix `.bot`?** Yes.

**What could go wrong.** The redundancy is the real risk: the sort is now stored *and*
derivable, so every lemma relating them needs a consistency side-condition, and `Compat` /
`LE` / `join` on `.forallE` must decide whether to compare the stored sorts. Get that wrong
and you have two notions of a Π-type's sort that can disagree — a strictly worse failure
mode than the current one, because it is silent. This is the most invasive option and the
one most likely to introduce a *new* wrong idea rather than remove one.

---

## Option 2: a "some sort" element in the lattice

**The change.** Add `.sortAny` (or generalise `.sort`'s `Bool` to `Option Bool`) so the
lattice can express what `IsType` expresses, and write `fun _ => .sortAny`.

**Cost.** Smaller than Option 1 at construction sites — `.sortAny` appears only in the two
clauses — but it changes what a `Shape` *is*.

**Does it fix `.bot`?** Yes.

**What could go wrong — and this is the objection.** `.sortAny` is not the shape of any term:
nothing is *of type* `.sortAny`. It is a query, not a value, smuggled into the value
datatype. Concretely, the lattice operations have no good answer for it:
- `LE`: is `.sort true ≤ .sortAny`? If yes, `.sortAny` is a join of `.sort true` and
  `.sort false` — but those are *incomparable* today and their `join` is `.bot`
  (`:764`, the `if r = r' then .sort r else .bot` clause). Adding a real join above them
  changes the lattice's shape, and `join`'s existing `.bot` answer becomes wrong.
- `Compat`: `.sortAny` is compatible with both booleans, so `Compat` stops being transitive
  on sorts.

Both are silent semantic changes to operations that many proofs depend on. **This option
does not stay a lattice**, which was the question asked, and I would not take it.

---

## Option 3: `hasType` becomes `Prop`-valued

**The change.** Then `∃ r, …` is writable directly and no lattice change is needed.

**Is `Bool`-valuedness load-bearing, or convenience?** A real answer: **load-bearing, but
narrowly.**
- There is **no `Decidable` instance for `HasType`** anywhere in the file, and nothing
  `decide`s it. (`DecidableRel` instances exist for `≤` on `Shape`/`WShape`/`ShapeFun`, and
  for `NonZero`/`ListNonZero` — none for `HasType`.) So decidability is *not* the reason.
- The reason is definitional computation. Five negations are proved by `nofun`
  (`:2909, :2911, :2913, :2915, :2917`), e.g.
  `theorem WShape.HasType.lam_isType : ¬HasType (WShape.lam f hf) (.sort r) := nofun`.
  These work because `hasType` *reduces* to `false` and `HasType` unfolds to `… = true`.
  Under a `Prop`-valued definition they become case analyses.
- Similarly `HasType.lift` (`:2550`) opens with `rw [← Bool.eq_iff_iff]`, and `hasType.core`
  is built from `List.all`/`List.any`.

**Does it fix `.bot`?** Yes.

**Cost.** Rewriting `hasType` and `hasType.core` as inductive/`Prop` definitions, plus the
five `nofun` proofs and the `Bool.eq_iff_iff` sites. Moderate — smaller than Option 1,
larger than Option 4.

**What could go wrong.** The `nofun` proofs are the tell: they are cheap *because* the
function computes, and there may be more places where `simp [hasType]` silently relies on
reduction that a grep for `nofun` will not find. That is an unbounded-tail risk of exactly
the kind this item has produced five times.

---

## Ranked recommendation

1. **Option 4 — quantify by disjunction.** Obviously right if it compiles. It is two clauses,
   changes no datatype, no lattice, and no evaluation strategy, and it fixes the `.bot`
   clause, which is the one that blocks the goal. The single question is whether the
   termination checker accepts two `core` calls; that is a five-minute check and it should be
   done before this memo is acted on either way, because a positive answer removes the need
   to choose among 1–3 at all.
2. **Option 3 — `Prop`-valued `hasType`.** The principled fallback if Option 4 fails. Its
   cost is now measured rather than guessed: no decidability dependence, five `nofun` proofs,
   a handful of `Bool.eq_iff_iff` sites.
3. **Option 1 — `.forallE` carries its sort.** Works, but 322 construction sites and it
   stores a fact that is also derivable, which invites silent disagreement.
4. **Option 2 — "some sort" element.** *Not a candidate.* It puts a query into the value
   datatype and breaks `join` and `Compat` on sorts.

**Plainly: Option 4 is obviously right if the termination check passes, and I would not
choose between the others until it has been tried.**

## Caveat on scope

If the scouting pass finds a shorter route to `sort_inv` that does not go through
`ShapeLogRel` adequacy, none of this needs doing. The `.bot`-clause finding is worth keeping
regardless — it is a true statement that the model is currently too strong, independent of
which route is taken.

---

## Result (appended after the check; the memo above is the pre-check snapshot)

**Termination passes, at zero cost.** `Shape.hasType` elaborates with two `hasType.core`
calls at the same `n`, with no `termination_by`, no `decreasing_by`, no annotation of any
kind. Evidence: zero errors anywhere in the definition's range — a termination failure is
reported at the `def` line, and there is nothing there. Run on the pristine file, so the
result cannot be confounded with the `indTy` fallout.

**Fallout: 8 error instances across 6 lines**, all in `Shape.HasType.unfold` and
`Shape.HasType.unfold_iff`. `Shape.HasType.lift` and `Shape.HasType.toType` both stayed
green.

**Options 1-3 are moot.** No datatype change, no lattice change, no `Prop`-valued
reformulation is needed.

### But: landing Option 4 *alone* is semantically vacuous

Discovered while repairing the 8 instances, and it changes when the change is worth making.

`Shape.HasType.toType` — `HasType m (.sort r) → HasType m .type` — **remains true on the
pristine file, and stayed green through the clause change**. That is the whole story: applying
it pointwise to the codomains turns `core (fun _ => .sort false)` into
`core (fun _ => .sort true)`, so

```
core (fun _ => .sort false) || core (fun _ => .sort true)   ≡   core (fun _ => .sort true)
```

The disjunction collapses to exactly the clause it replaced. The model is *not* made less
strong; proofs of `Prop`-valued Pi-types are still excluded, because `toType` is what excludes
them and `toType` is still there.

`toType` only becomes false once `ShapeS.indTy` carries its sort — that is precisely the
seventh-face finding. **So Option 4 buys nothing until the `indTy` parameterisation lands,
and it is not a self-contained improvement.**

### Consequence for sequencing

The 8 repairs must go one of two ways, and neither is free standing alone:

- **Weaken `Shape.HasTypeU.bot`'s premise to `∃ r, HasType x (.sort r)`** and
  `Shape.HasTypeLam`'s first conjunct to `∃ r, HasTypePi b a r`. This is the right end state
  — it makes `HasTypeU` mirror the new clauses exactly, checked constructor by constructor —
  but it is part of the held `IsType` migration.
- **Or add a collapse lemma** proving the disjunction equals its `true` disjunct via `toType`,
  and repair the proofs with it. Minimal and honest, but that lemma is false the moment
  `indTy` is parameterised, so it is written to be deleted.

**Recommendation: do not land Option 4 standalone.** Land it as the first step of the
`indTy`/`IsType` migration, where the first repair route is the correct one and costs nothing
extra. If the scouting pass retires the `ShapeLogRel` route, Option 4 need never be landed
at all.

### Carried forward: the reduction-reliance tax

Any change to `hasType`'s clauses costs proof repair proportional to how many proofs depend on
the function *reducing*. `unfold_iff` closes cases with `cases n <;> rfl`; five negations
elsewhere are `nofun` (`WShape.HasType.lam_isType` and neighbours). Both work only because
`hasType` computes. This is a property of the file, not of those sites — worth knowing before
costing any future clause change.

---

## `IsType.common` is false — machine-checked counterexample

`WShape.IsType.common` — "two compatible classifying shapes share a sort" —

```lean
theorem WShape.IsType.common {a a' : WShape n} (hC : a.Compat a')
    (h : a.IsType) (h' : a'.IsType) : ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r)
```

**is false.** It was approved twice — first at `Shape` as "a derived fact, not a change to any
statement", then moved to `WShape` on the argument that the `.forallE` case needs
`ShapeFun.WF`'s `∃ y, (.bot, y) ∈ f`. Neither placement rescues it: `WF` is simply too weak.

The witness, at `n = 2`, with `b = b' = .sort true`:

```lean
cxF  = [(⊥, ⊥), (.sort true,  .indTy false)]     cxA  = .forallE b cxF
cxF' = [(⊥, ⊥), (.indTy true, .indTy true )]     cxA' = .forallE b cxF'
```

Checked by computation: `Shape.Compat cxA cxA' = true`; `cxA` is classified by `.sort false`
and *not* `.sort true`; `cxA'` by `.sort true` and *not* `.sort false`. `Shape.WF cxA` and
`Shape.WF cxA'` both hold. So both are legitimate `WShape`s, they are compatible, each is
classified by a sort, and no sort classifies both.

**Why it survives `Compat`.** `ShapeFun.Compat R f f' = f.all fun (x, y) => f'.all fun
(x', y') => R x x' → R y y'` — the obligation on *values* is guarded by the *keys*. The only
pair that would force `Compat (.indTy false) (.indTy true)` (i.e. `false = true`) has keys
`.sort true` and `.indTy true`, which are different constructors and therefore incompatible,
so the implication never fires. Every other pair routes through `⊥`, which is compatible with
everything.

**Both suspected blockers were checked and are satisfied.** `ShapeFun.WF`'s join-closure holds
(every key pair joins to a key already in the family) and its monotonicity clause holds (the
only non-trivial obligation is `⊥ ≤ k → ⊥ ≤ value`, and `⊥` is bottom). Do not expect `WF` to
be where a proof attempt dies; it isn't.

**The general fact, which outlives this lemma:** `Compat` on `.forallE` shapes does not
constrain the codomains' universe *at all* when the domains disagree. Two Pi-shapes can be
compatible while one is `Prop`-valued and the other `Type`-valued. This is a real gap in the
shape lattice, not an artifact of `IsType` — it was invisible only because `.type` forced
every classifying shape to `true`, leaving nothing to disagree about. The `ShapeS.indTy`
parameterisation did not introduce it; it exposed it.

The Lean witness (`cx_refutes`, sorry-free, with the four `decide`-checked clauses as a live
regression test on `Compat`/`WF`/`hasType`) lands with the `indTy` migration — it needs
`ShapeS.indTy`'s boolean parameter and so cannot compile against the pre-migration tree. It is
carried in the migration WIP under `section CounterexampleProbe`.

## `WShape.HasType.join` is false as well

Suspected while investigating option (b) for `join`, then confirmed by lifting the same
witness one level. With `jF = [(⊥, ⊥)] : ShapeFun 2`:

```lean
jM  = .forallE cxA  jF        jM' = .forallE cxA' jF        -- : Shape 3
```

Checked by computation: `Shape.Compat jM jM' = true`; `hasType jM (.sort true) = true`;
`hasType jM' (.sort true) = true`; and **`hasType (Shape.join jM jM') (.sort true) = false`**.
Both are well-formed. So two compatible shapes, both classified by `.sort true`, whose join is
not — refuting

```lean
theorem WShape.HasType.join (hJ : m₁.Compat m₂) (h1 : m₁.HasType a) (h2 : m₂.HasType a) :
    (m₁.join m₂).HasType a
```

`j_refutes` is the machine-checked witness (sorry-free), carried alongside `cx_refutes`.

**The mechanism, stated once for both refutations.** A Pi-shape's *shared codomain sort*
constrains the family's **values**, never its **domains**. `jM` and `jM'` share the codomain
sort `true`, but their domains are `cxA` and `cxA'` — compatible, and sharing no sort. The
joined domain `cxA.join cxA'` therefore admits nothing: `hasType (.bot : Shape 2)
(Shape.join cxA cxA') = false`, so `HasDom` fails for the joined family and no sort classifies
the join.

This is also exactly why option (b) — reproving `join` by threading its shared `a` down through
`go_dom` — cannot work. The shared `a` is the *codomain* sort; the obstruction is in the
*domains*, which it never reaches. There is no vantage change available, and the failure is
structural rather than a proof looking at the wrong thing.

**Consequence.** The question is no longer how to prove `join`, or what to weaken its
conclusion to. It is which `HasDom` / `HasTypePi` / `HasTypeLam` joins are *true*, with the six
consumers of the current ones re-derived from that. Note that `go_lam` calls `go_dom` with
`.rfl` — the *same* domain on both sides — so the same-domain case is unaffected and is
probably where the salvageable statement lives.

## No `HasType` join is true, and `HasDom`'s escape hatch does not help

Two further passes, both negative, both settled by kernel computation.

**Pass 1 — `WShape.HasTypeLam.join` is false, so `go_lam` does not survive either.** `go_lam`
calls `go_dom` with `.rfl` and so never needs the false domain fact *directly*, but it recurses
into `join` at the lambda-family's **values**, and those may themselves be `.forallE` shapes.
Embedding the witness there reproduces the obstruction one level in. With
`lB = [(⊥, .sort true)]`, `lF = [(⊥, jM)]`, `lF' = [(⊥, jM')]`:

```
hasType jM  (lB.app ⊥) = true
hasType jM' (lB.app ⊥) = true
hasType (jM.join jM') (lB.app ⊥) = false          -- `lam_join_fails`
```

`ShapeFun.join` merges the two bot-keyed entries by joining their values, so
`HasTypeLam (lF.join lF') a lB` would have to make the third `true`. **Conclusion: no
`HasType` join in the family is true — not `join`, not `go_pi`, not `go_lam`.**

**Pass 2 — `HasDom`'s `∃`-with-`≤` does not absorb the failure.** The hypothesis was that
`HasDom`'s witness need only be `≤` the joined key, so a bot-keyed element could discharge it.
It cannot: the witness must still satisfy `x'.HasType a` at the **joined** domain. With
`f = f' = jF = [(⊥, ⊥)]` the only candidate is `⊥` itself, and

```
hasType (⊥ : Shape 2) cxA  = true
hasType (⊥ : Shape 2) cxA' = true
hasType (⊥ : Shape 2) (cxA.join cxA') = false     -- `hasDom_escape_fails`
```

**The `≤` relaxation is on the key, never on the type**, so it cannot absorb a failure that is
about the type. `HasDom.join` is false for the same reason everything else is.

### Where this leaves the join layer

Every join lemma in the `HasType` family is false: `HasType.join`, `HasDom.join`,
`HasTypePi.join`, `HasTypeLam.join`, and the `mono_l`-wrappers `HasType.join'`,
`HasDom.join'`, `TShape.HasType.join`, `TShape.HasType.join'` that inherit from them. Neither
of the two structural hopes — restricting to equal domains, or leaning on `HasDom`'s `≤` —
survives contact.

The single sentence that explains all of it: **`Shape.join` is not a join in the typed sense.**
It is a join on *shapes*, and `hasType` is not closed under it — two shapes can both be
classified while their join is classified by nothing. Any lemma asserting that joining
preserves typing is asking `Shape.join` to be something it isn't.

## What the consumers need: an `LE_Interp`-relative hypothesis, not a `WF`-relative one

Reading the seven call sites for what they *require* (rather than what they call) gives a
better answer than the join layer's refutation suggested.

| site | call | what it needs |
|---|---|---|
| `ShapeLogRel:4255` | `hdom.join cf ca_w hdom'` | `HasDom.join` at **different** domains |
| `ShapeLogRel:4300` | `hdom.join cf ca_w hdom2` | same |
| `ShapeLogRel:4340` | `h4.isType.join ac a4.isType` | the **heterogeneous** join `join_het` |
| `ShapeLogRel:4770` | `hT1.isType.join' jb_x hT2.isType` | `join'` at a joined type |
| `ShapeLogRel:4771` | `(…).join' (jf.app_l x) (…)` | same |
| `Adequacy:74`, `:217` | `hta₁.join' hj hta'` | `join'` at a joined type |

Every one of these is false **about arbitrary well-formed shapes** — that is what the
refutations establish. But every one of them occurs under `LE_Interp.compat_join`:

```lean
theorem LE_Interp.compat_join (hρ : ρ'.LE ρ) (H1 : LE_Interp ρ' m₁ M) (H2 : LE_Interp ρ m₂ M) :
    m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M
```

— **the same `M`**. So the invariant actually in scope at every call site is *both shapes
realize the same term*, and the join lemmas are stated with only `Compat`, which is strictly
weaker.

`cxA` and `cxA'` are arbitrary well-formed shapes with no term behind them: one is a Pi-shape
whose codomains are `Prop`-valued, the other's are `Type`-valued. If no single term can be
realized by both, they never arise at these call sites and the refutations, while correct,
do not apply to the situations the proofs are in.

**So the missing hypothesis is `LE_Interp`-relative, not `WF`-relative.** That is a hypothesis
with a test — check whether `cxA` and `cxA'` can co-realize a term — and it is the next thing
to settle. `WF` was never going to be the right strengthening; it constrains shapes in
isolation, and the obstruction is about two shapes being *jointly* realizable.

## The co-realizability test: positive, and it ties the repair to the migration

**Can `cxA` and `cxA'` realize the same term?** No — *provided* `LE_Interp.Const.indTy` carries
the inductive's universe. That proviso is the whole content of the answer.

`.indTy` shapes arise from exactly one place, `LE_Interp.Const.indTy`:

```lean
| indTy : Params.classify c = some (.indTy rargs.length) →
    m ≤ (WShape.indTy : WShape (n+1)).T → Const rargs m
```

For `cxA` and `cxA'` to realize a common `.forallE B F`, `LE_Interp.forallE` would require
`LE_Interp (ρ.push (.sort true)) (.indTy false) F` and
`LE_Interp (ρ.push (.indTy true)) (.indTy true) F`. Both must factor through `Const.indTy` at
`F`'s head constant `I`. If that rule's boolean is `r_I` — a function of `I` — then
`.indTy false ≤ .indTy r_I` and `.indTy true ≤ .indTy r_I`, and since `LE` on `.indTy` is
equality of the boolean, `r_I` would have to be both. Contradiction: **they cannot co-realize.**

**But nothing currently makes `r_I` a function of `I`.** `Classification.indTy` carries only an
arity:

```lean
inductive Classification where
  | ctor (arity : Nat) | etaCtor (params args : Nat)
  | symb (arity : Nat)  | indTy (arity : Nat)
```

so `classify` does not know whether an inductive is `Prop`- or `Type`-valued, and `Const.indTy`
has no way to pin its boolean.

**The repair is therefore: `Classification.indTy` gains the universe** (or `Const.indTy`
consults the declaration, which `ParamsExtra.ctor_ty` already exposes via `D.lvl`). And
`Const.indTy` is *already* one of the migration's open sites -- it is a live error, since
`WShape.indTy` now takes the boolean it never had. So this is not additional work: it is work
already in the queue, and **doing it correctly is exactly what makes the `LE_Interp`-relative
invariant true.**

That closes the loop. The join family is repairable, the missing hypothesis is
`LE_Interp`-relative as suspected, and the fact that makes it hold is the same fact the
`indTy` parameterisation exists to record.

---

## Session update: the `indTy` parameterisation lands `hu0`, and `proofIrrel` is now false

Measured on a fresh build of the WIP pair (`scratchpad/{SExpr,ShapeLogRel}.indTy-wip19.lean`,
which must be restored together):

| | error instances | distinct error lines |
|---|---|---|
| WIP as inherited (fresh `SExpr.olean`) | 181 | 132 |
| WIP at handoff | **9** | **9** |

The earlier "144 instances / 105 lines" figure was taken against a stale `SExpr.olean`; it is
not comparable. Rebuild `Lean4Lean.Experimental.SExpr` before measuring `ShapeLogRel.lean`.

### `CtorBundle.hu0` is repaired — the migration's stated purpose is met

`hu0 : u ≠ .zero` is gone. In its place:

```lean
hrel : rel = true ↔ u ≠ .zero
```

This is not an invented hypothesis. It is `ParamsExtra.ctor_ty`'s existing
`(rel = true ↔ D.lvl ≠ .zero)`, now readable off the head constant because
`Classification.indTy` carries the boolean. `u` is the sort of `CtorBundle.rhs`, whose head is
`I` applied to its arguments, and `imax x y = .zero ↔ y = .zero`, so `u ≠ .zero` says exactly
that the inductive's result universe is not `Prop`.

`LE_Interp.build_spine`, `hu0`'s only consumer, is **green**. Two changes were needed:

* its telescope helper was strengthened from "propagates `≠ .zero` downwards" to the full
  equivalence `u_body = .zero ↔ u = .zero`. Both directions run the same argument through
  `SLevel.imax_eq_zero` (already an iff) and the `h_imax_defeq` transport; only the forward
  one was previously used, because `hu0` was all that was on offer;
* the head's type-shape is `.sort rel` rather than `.sort true`, with
  `decide (u_body ≠ .zero) = rel` discharged from `hrel`.

`LE_Interp.Const.compat_join`'s `indTy`/`indTy` case now discharges its obligation by
`injection` on `classify c` — the first place in the file where the parameterisation pays for
itself, and the machine-checked half of the co-realizability argument in the section above.

### The `.type`-as-universe migration is complete

`IsType a := ∃ r, HasType a (.sort r)` now reaches every site: `Shape.IsType`,
`WShape.IsType` (restated with `WShape.HasType` rather than `Shape.IsType a.1`, so that
destructuring yields a hypothesis whose head supports dot-notation), a new `TShape.IsType`,
`Valuation.Fits.cons`, `InterpTyped.hsort`, `LE_Interp.sound_app`/`sound_lam`'s hypotheses,
`LR.Subst1`, `LR.SubstWF.cons`, `LR.lift_succ_aux`, `LR.TyDefEq.lift`,
`LRS.PiDefEq.lift_aux`. `WShape.IsType.common`, which is false and had zero consumers, is
deleted; its prose and witness stay.

Helpers introduced, each replacing an idiom that stopped working:

* `WShape.HasType.toIsType` — replaces `HasType.toType`;
* `WShape.HasType.bot_bot` / `TShape.HasType.bot_bot` — `.bot' (.bot' .sort)` no longer
  determines its sort booleans;
* `WShape.IsType.not_lam` / `.not_ctor` — `casesOn'`'s `lam`/`ctor` cases used to close by
  `trivial`, because `trivial` tries `contradiction` and `HasType (.lam ..) .type` *reduced*
  to `false = true`. An existential does not reduce;
* `WShape.indTy_join_indTy`.

### `WShape.HasType.proofIrrel` is FALSE under the parameterisation — machine-checked

The previous handoff read the sort-polymorphic experiment's cluster 2 as "the boolean is
needed, which is what the parameterisation supplies". **That reading is wrong.** Witness
(`proofIrrel_fails`, sorry-free, `rfl`-checked, in `section CounterexampleProbe`), at `n = 1`:

```
a := .indTy false          x := .ctor `Foo` []

Shape.hasType x a      = true     -- clause `.ctor _ _, .indTy _ => true`
Shape.hasType a .prop  = true     -- clause `.indTy r, .sort r' => r = r'`
x ≠ .bot                          -- different constructors
Shape.WF a, Shape.WF x            -- `WF (.indTy _)` is `True`; `WF (.ctor c [])` vacuous
```

The parameterisation gives the shape layer the *ability* to distinguish `Prop`-valued
inductives; it does not *use* it, because `HasTypeU.ctor : HasTypeU (.ctor c l) (.indTy r)`
still fires at every `r`. Nothing inside `proofIrrel` can repair this — the fix has to be at
the `ctor` rule.

So the three-way tension now has **three** refuted resolutions rather than two:

1. `hu0` asserted that (ii) never happens for classified constructors — `Eq.refl` refutes it;
2. the sort-polymorphic rule dropped the distinction — `proofIrrel` refutes it;
3. the parameterisation *records* the distinction without *acting* on it in `HasTypeU.ctor` —
   `proofIrrel_fails` refutes it.

Only denying (i) is left, which is the `Const.ctor` lead. It remains untested and gated.

### What the 9 remaining errors are

Two families, both needing a decision rather than a proof:

* **the join family (7)** — `WShape.HasType.join`'s `go_dom`/`go_pi`, `WShape.HasDom.join`,
  `LE_Interp.compat_join`, `LE_Interp.sound_lam` (×2), `LRS.PiDefEq.join` (×2). `go_dom` dies
  at `ih ha a2.isType b2.isType`, which is `IsType.common` — false. The repair is the
  `LE_Interp`-relative hypothesis, i.e. adding a hypothesis. `sound_lam`'s two are the same
  obstruction from the other side: its `suffices` yields `(b.app x).IsType` per `x`, and
  `HasTypeLam.iff` wants one sort for the whole codomain family;
* **`proofIrrel` (2, one a knock-on)** — the section above.

### Downstream

`ShapeLogRelAdequacy.lean` consumes `LR.TyDefEq.lift`, `TShape.HasType.proofIrrel`,
`.isType` and the join family, and will need the same `IsType` treatment when the pair lands.
It was not touched.

---

## Session update 2: the `LE_Interp`-relative join repair is refuted; §7 lands `proofIrrel`

Both items were approved and both were taken. One succeeded, one is refuted with a
machine-checked witness. State: **9 error instances at 9 lines** (unchanged in count, but the
composition changed: `proofIrrel` is proved, and one new error is §7's residue).

### The approved join repair is FALSE — `le_interp_common_fails`

The approval rested on: every call site sits under `LE_Interp.compat_join` at the same `M`, so
"both shapes realize the same term" is an invariant already in scope; and the counterexample
shapes cannot co-realize, because both would have to factor through `Const.indTy` at the same
head constant.

The **premise** is now machine-checked: `LE_Interp.Const.compat_join`'s `indTy`/`indTy` case
discharges its obligation by `injection` on `classify c`. The **conclusion** does not follow.

```lean
private theorem le_interp_common_fails :
    ¬ ∀ {n : Nat} {ρ : Valuation} {A : SExpr} {a a' : WShape n},
        LE_Interp ρ a.T A → LE_Interp ρ a'.T A → a.IsType → a'.IsType →
        ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r)
```

sorry-free. The escape is `LE_Interp.bvar : m ≤ ρ i → LE_Interp ρ m (.bvar i)`, which puts no
condition on `ρ` at all. `cxA.Compat cxA'` holds, so `WShape.Compat.iff` hands over an upper
bound — their join — and setting `ρ i` to it makes *both* realize `.bvar i` under the *same*
valuation. The join is classified by no sort.

The `Const.indTy` argument is correct for `.indTy` shapes reached *through `Const`*. It never
reaches `bvar`, where the shape comes from the valuation and nothing forces it through `Const`.

**The defect is that `compat_join` quantifies over an arbitrary `ρ` with no well-formedness
hypothesis** — the same shape of defect as `SExpr.IsDefEq.strong`'s missing `Ctx.WF` and
`VEnv.Params.pat_wf`'s missing `OnCtx`, now on *valuations* rather than contexts. PLAN.md
already states the rule; valuations are its third instance. Note `ρ i := cxA.join cxA'` is a
shape that has **no type at all**; `Valuation.Fits` never produces one, but `compat_join` does
not ask for `Fits`.

### What is true instead

```lean
theorem WShape.IsType.common_of_le {a a' z : WShape n}
    (le1 : a ≤ z) (le2 : a' ≤ z) (hz : z.IsType) (h : a.IsType) (h' : a'.IsType) :
    ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r)
```

Proved, three lines of `HasType.retype`. `Compat a a'` says *some* upper bound exists; what
the join family needs is a **classified** one. So the open question is not "is
co-realizability enough" — it is not — but **can each call site produce a classified upper
bound, and from where?** `a.join a'` is circular. The non-circular candidates all live in
`Valuation.Fits`, whose `cons` field already carries exactly "any shape realizing `A` has a
classified upper bound realizing `A`". Threading `Fits` (or a weaker "typed valuation"
predicate) into `compat_join` is the next thing to cost, and it is a hypothesis on `ρ`, not on
the shapes.

### §7: `proofIrrel` is proved

Three edits, and nothing else in the file broke:

* `Shape.hasType`'s `| _+1, .ctor _ _, .indTy _ => true` became `| _+1, .ctor _ _, .indTy r => r`;
* `Shape.HasTypeU.ctor` and `WShape.HasTypeU.ctor` gated to `.indTy true`;
* `Shape.HasType.indTy_false_bot` / `WShape.HasType.indTy_false_bot` — `.indTy false`
  classifies only `.bot` — and `proofIrrel`'s new `indTy` case is one line of it.

`proofIrrel_gated` is the regression test. The three-way tension is now resolved in the shape
layer: three resolutions refuted (each machine-checked), the fourth — denying (i) — works.

### §7's residue, and its measured cost

`LE_Interp.build_spine` builds a constructor application's shape as
`WShape.ctor' c rargs.reverse`, pinned by `LE_Interp.Matches.app`. For a `Prop`-valued
inductive that shape must be `.bot`. `WShape.ctor'`'s existing `.bot` fallback is guarded by
`IsStruct c`, not by `Prop`-ness, and `Classification.ctor` does not carry the boolean, so the
guard cannot be written. The remaining change is `Classification.ctor (arity) (rel)` and
`.etaCtor (params args) (rel)`, then one more disjunct in `ctor'`'s `dif`.

Measured by probe (run, then reverted):

| | cost |
|---|---|
| `SExpr.lean` | **2 edits, compiles clean** — the inductive + `Classification.arity`, plus restating `Pattern.WF`'s `.const` clause as `if top then cl c = some (.symb n) else ∃ r, cl c = some (.ctor n r)` |
| `ShapeLogRel.lean` | **107 error instances at 60 lines**, *before* `ctor'`'s guard is touched |
| `ctor'`'s guard | unmeasured; 59 occurrences, and the `.bot`-branch discharges in `Matches.matches_inter`, `Const.compat_join` and `unique` use `head_wf` + `IsStruct` and will stop working |

The earlier estimate — "one more disjunct in an existing `dif`" — was wrong by an order of
magnitude. The disjunct is one line; the boolean it tests costs 107 instances to introduce.
