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

---

## Session update 3: both cheap routes costed, both closed

Two questions were asked before any lines were written. Both are answered negative, and both
answers are specific.

### 1. Threading `Fits` into `compat_join` does not reach the call sites

Of the eight join-family error sites, **five have no valuation in scope at all** — not "no
`Fits`", no `ρ`:

| site | enclosing declaration | `ρ`? | `Fits`? |
|---|---|---|---|
| `go_dom`, `go_pi` (2) | `WShape.HasType.join` | no | no |
| `WShape.HasDom.join` (1) | derived from `go_dom` | no | no |
| `h4.isType.join ac a4.isType` (1) | `LE_Interp.compat_join` | yes | **no** |
| `(hi3 x h).isType`, `hT1.isType.join'` (2) | `LE_Interp.sound_lam` | yes | **no**\* |
| `htB₁.join hC_b htB₂`, unsolved (2) | `LRS.PiDefEq.join` | no | no |

\* `sound_lam`'s single caller, `strongSoundS:5770`, does have `W : Fits`, so `sound_lam` and
`sound_forallE` could take one. Nothing else can.

`WShape.HasType.join` / `HasDom.join` are shape-lattice lemmas with no `ρ` in their
statements. `LRS.PiDefEq.join`'s consumer is `LogRel.join_ty`, a **field of the abstract
`LogRel` structure**, parameterised by `Γ` and `n` only — there is no valuation to thread,
ever. And adding `Fits` to `compat_join` would push into `LE_Interp.compat` / `.join'` and
thence into `LE_Interp.subst` and `LE_Interp.inst`, iff-statements about substitution with no
`Fits` and no caller that has one.

**So the hypothesis has to be the classified upper bound itself, carried as an argument.** One
encouraging structural fact (checked against the definitions, *not* machine-checked): a
classified upper bound propagates downwards. If `z.IsType`, `m₁ ≤ z`, `m₂ ≤ z` with
`m₁ = .forallE a b`, `m₂ = .forallE a' b'`, then `forallE_le` gives `z = .forallE za zf` with
`a ≤ za`, `a' ≤ za`, and `z.IsType` unfolds to `HasTypePi zf za r`, whose `HasDom zf za` gives
`za.IsType` via `HasDom.isType`. So `za` is a classified upper bound for the *domains* —
exactly what `go_dom` needs — and `zf`'s values serve one level further down. A single
`∃ z, m₁ ≤ z ∧ m₂ ≤ z ∧ z.IsType` at the top may suffice for the whole family.

If it does, the obligation lands on `LogRel.join_ty`'s three consumers — `PiDefEq.join`, the
`LRS` instance's own `join_ty`, and `ShapeLogRelAdequacy:89`. **`Adequacy:89` is where the real
data is, and it should be costed first**: if `Adequacy` cannot produce a classified upper
bound, the whole chain is dead and nothing above it is worth writing.

### 2. §7's residue: the bundle route is closed, and so is a second one

**(i) `rel` from `CtorBundle.hclI` instead of `Classification.ctor`.** No. `rel` *is* in scope
at `build_spine`'s failing site — the bundle is right there. But the boolean is needed at a
**computation**, not a proof obligation: the shape is `WShape.ctor' c_a rargs_a.reverse`,
pinned by `Matches.app`'s index, and `ctor'` is a `def` whose `dif` guard must be decidable
from `c` alone. A `CtorBundle` exists only as a hypothesis inside `IsDefEqStrong.const` /
`StrongSoundCore.const`; `Matches` and `ctor'` are elaborated with `[Params]` only. No fact can
make a computed term `.bot`. Nor can the site dodge by choosing a different type-shape `a` for
`apps_realize`: `a` must satisfy both `(.ctor' c l).HasType a` (which, after §7's gating and
`WShape.indTy_le`, forces `a = .indTy true`) and `LE_Interp ρ a.T T` (which the `Const.indTy`
chain gives only at `.indTy rel`).

**(ii) Relax `Matches.app`'s index from `= .ctor' c' rargs'.reverse` to `≤`.** No — this
refutes `LE_Interp.Matches.unique`, which recovers `c'` and `rargs'` *from* the index shape.
Analysed, not machine-checked; stating it needs the datatype change first.

### The disjunct is not analogous to the one already in the `dif`

> The existing `.bot` fallback is **information-preserving**. A `Prop`-ness fallback would be
> **information-destroying**.

`WShape.ctor'`'s `.bot` branch fires exactly when `IsStruct c ∧ ¬ ListNonZero l`, and
`ListNonZero l` is `∃ x ∈ l, ¬ x ≤ .bot` — so it fires **only when every argument is already
`≤ .bot`**. Nothing is lost: `rargs'` is still recoverable (it is all `.bot`), which is why
`matches_inter`, `Const.compat_join` and `unique` survive today. A disjunct keyed on
`Prop`-ness fires with *arbitrary* arguments, and those three lose the recovery. They do not
merely "stop working"; `unique` looks **false**.

So the earlier estimate was wrong twice over: the disjunct is one line, the boolean it tests
costs 107 instances, *and* the disjunct is not the same kind of thing as the one beside it.

### The fork §7's residue actually presents

- **(α)** `ctor'` falls back to `.bot` for `Prop`-valued inductives ⇒ `Matches.unique` (and
  probably `matches_inter`) must be restated, or is false.
- **(β)** `Pattern.WF` requires `rel = true` at constructor leaves, so a `Prop`-valued
  inductive's ι-rule is simply not a `Pattern`. This is the resolution the `CtorBundle`
  docstring already anticipated, and it may be right: for a `Prop`-valued inductive the major
  premise is a proof, `proofIrrel` gives it shape `.bot`, and the whole redex is `.bot` — the
  shape model does not need the rule. It is also the "small elimination" fact PLAN.md already
  lists as a missing `Params` axiom for `NormalEq.parRed`.

---

## Session update 4: `Adequacy:89` clears, but by the term's universe; §7's (β) is refuted

### Join family — `Adequacy:89` costed, and the answer is positive

A common **classified upper bound** is *not* producible there. `InterpTyped.hsort` /
`hsort'` yield a bound *per shape*, and joining the two to get a single one needs
`LE_Interp.join'` = `compat_join.2`, one of the eight broken sites. Circular.

**But a common sort is producible, and by a better route.** `InterpTyped.hsort'` gives, for
each shape realizing `A`, an upper bound classified at `.sort (U ≠ .zero)` — and that boolean
is a function of `U`, **the universe `A` lives at**, not of the shape. So the two bounds carry
the *same* sort, and `HasType.retype` pulls the classification back down each separately. No
join, no circularity:

```lean
theorem LE_Interp.common_sort {ρ A U} {a a' : WShape n}
    (H : ∀ {b}, LE_Interp ρ b A → InterpTyped ρ b A (.sort U))
    (h : LE_Interp ρ a.T A) (h' : LE_Interp ρ a'.T A)
    (ha : a.IsType) (ha' : a'.IsType) :
    ∃ r, a.HasType (.sort r) ∧ a'.HasType (.sort r)
```

**Proved**, sorry-free, in the parked file next to `InterpTyped.hsort`.

`Adequacy:89` has every hypothesis: `HA : IsDefEqStrong Γ A A' (.sort u)` fixes `u`;
`(LE_Interp.soundS HA W.fits).2` *is* the `H` (already used three times in the same proof);
`hA₁` and `ha'` realize the same `A`; `hp.isType` and `ht.isType` are the two `IsType`s. So if
`LogRel.join_ty`'s two `IsType` hypotheses become `m₁.HasType (.sort r) → m₂.HasType (.sort r)`
at a **shared** `r`, `Adequacy:89` discharges it — "strengthen a hypothesis the caller already
has".

**So the chain is not dead — but the `∃ z` framing was wrong, mine included. The common sort
comes from the term's universe, not from the shapes and not from an upper bound.**

#### What is still open, and it is not at `Adequacy`

A shared sort *at the top* does not reach `go_dom` — diagnosis sentence 1 again: a Pi-shape's
shared codomain sort constrains the family's values, never its domains. `go_dom` needs the two
**domains** to share a sort, and the domains correspond to the domain term `B₁`, whose own
universe fixes their boolean. The fact must be re-supplied at every level from the accompanying
term, not propagated from the level above.

`join_ty`'s other consumer, `LRS.PiDefEq.join`, sits at the `LogRel` layer where the shape↔term
link is `TyDefEq`, not `LE_Interp`, so `common_sort` does not apply. `ValTyPi2` *does* carry the
domain term and its universe (`Γ ⊢ B₁ ≡ B₂ : .sort u`), so the information is present; what is
missing is a `LogRel` field

```
ty_sort : TyDefEq A B m → m.IsType → Γ ⊢ A ≡ B : .sort u → m.HasType (.sort (u ≠ .zero))
```

plausible (checked by hand at `.bot`, `.sort`, `.forallE`, `.indTy`) but a **new obligation**,
and essentially the substance of `sort_inv` itself. That is the next thing to cost, at `LRS`'s
`join_ty` (`forallE` case), before any propagation is written.

### §7 — (β) is refuted at `Eq`

(β)'s premise was PLAN.md's *small elimination* fact: the major premise is a proof, so the
whole redex is a proof and has shape `.bot`.

**`Eq` is a `Prop` that large-eliminates.** `@Eq.rec`'s motive is `Sort u_1`, not `Prop`, so

```lean
private theorem eq_large_eliminates :
    Eq.rec (motive := fun (b : Nat) (_ : (0:Nat) = b) => Nat) 7 (rfl : (0:Nat) = 0) = 7 := rfl
```

is a `Nat`, not a proof. `proofIrrel` does not apply and the redex's shape is not `.bot`. Small
elimination covers `Acc.rec` and `Quot.lift`-over-a-`Prop`; it does **not** cover the
subsingleton eliminators, and `Eq` is the one that started this.

The consequence is the failure mode that is worst to detect. Under (β),
`Params.pat_wf : Pat p r → p.WF classify` together with `ParamsExtra.extra_pat` (every
`env.defeqs df` must be covered by some `Pat p r`) makes **`ParamsExtra` unsatisfiable for any
environment containing `Eq`** — every real one, since `Eq` is in `stdPrelude`. Nothing in the
tree would notice: there is no `ParamsExtra` instance, so every downstream result would go
silently vacuous. `ParamsExtra`'s own docstring records that this project has already been
burned by exactly that once.

### Where §7's fork now stands

- **(α)** `ctor'` falls back to `.bot` for Prop-valued inductives — 107 instances *plus*
  restating `Matches.unique`, which looks false under it.
- **(β)** refuted, above.
- **(γ)** *observed, not proposed, not tested.* The tension at `Eq.refl` is between the
  **shape** (`.ctor`, needed so the ι-rule's pattern has a `.ctor` leaf) and the **typing**
  (`HasType (.ctor ..) (.indTy false)`, which §7 had to kill for `proofIrrel`). Only
  `LE_Interp.const`'s `HasType` premise — reached through `apps_realize`'s `mty` — ties them
  together. Decoupling them there would let `Eq.refl` keep its `.ctor` shape without being
  classified by a Prop-valued inductive. Cost unknown: `strongSoundS`'s `proofIrrel` case uses
  `TShape.HasType.proofIrrel` on exactly that premise. Do not act on it without testing.

---

## Session update 5: (γ) refuted — all three routes closed; `ty_sort` costed and not circular

### §7 — (γ) is refuted, and the fork is closed

(γ) was: move `LE_Interp.const`'s `m'.HasType a` premise, so `Eq.refl` could keep its `.ctor`
shape without being classified by a Prop-valued inductive.

Probed by actually removing the premise: **36 errors, all mechanical arity fixes except one**,
at `strongSoundS`'s `const` case, which builds `InterpTyped ρ m (.const c ls) A` with that
premise *literally* as the `HasType` field —

```lean
exact .mk b3 (.const b1 b2 .rfl b4 b5 b6 b7) b5 b4   -- `b4` appears twice
```

— and there is nothing else to put there. And the reason is not about where the premise sits:

```lean
private theorem ctor_not_prop_typed (a : Shape 1) (h : Shape.hasType piX a = true) :
    Shape.hasType a (Shape.prop (n := 1)) = false
```

**Proved.** No shape both classifies a `.ctor` and is itself Prop-valued, so `InterpTyped`'s
slot cannot be filled for `Eq.refl` at its natural shape *wherever the premise lives*.

**All three routes are closed.** §7's residue is a design problem, and its sharpest statement:

> §7 makes `proofIrrel` true by ruling that a `.ctor` shape is never classified by a
> Prop-valued inductive. But `Eq.refl` must **have** a `.ctor` shape (its ι-rule's pattern
> needs a `.ctor` leaf, and `Eq` large-eliminates so that rule cannot be dropped), and it must
> **be typed** (`InterpTyped` demands a classifying shape for every realized term). Those two
> are now inconsistent for one and the same term, and no relocation of a premise reconciles
> them — the obstruction is `ctor_not_prop_typed`, which mentions neither `LE_Interp` nor
> `Params`.

Anything that resolves it must give up one of: `proofIrrel` at Prop-valued inductives; the
`.ctor` leaf in ι-patterns; or `InterpTyped`'s totality on realized terms.

### Join family — `ty_sort` costed. Not circular, and the universe is not needed.

**Circularity check, negative.** I called `ty_sort` "essentially the substance of `sort_inv`";
that was too pessimistic. `sort_inv` needs the *level* (`u ≈ v`); the shape model needs only
the *boolean* `decide (u ≠ .zero)`, and the boolean falls out of a `SoundEq` between sorts via
`LE_Interp.le_sort`, whose whole proof is a two-case induction on `LE_Interp`. The technique is
already used in `build_spine`'s `imax` argument.

**The universe is not needed either.** A universe-carrying `ty_sort` applied twice at `LRS`'s
`join_ty` `forallE` case leaves `decide (u ≠ 0)` against `decide (u' ≠ 0)`. Dropping it removes
the problem:

```
join_sort : m₁.Compat m₂ → TyDefEq A B m₁ → TyDefEq A B m₂ → m₁.IsType → m₂.IsType →
            ∃ r, m₁.HasType (.sort r) ∧ m₂.HasType (.sort r)
```

`IsType.common` relativised to `TyDefEq` at a common `A B` — the same move `common_sort` makes
one layer down. `join_ty` already has `hC`, so the caller supplies nothing new.

**Why it should go through**, and the half that is machine-checked:

```lean
theorem Shape.IsType.common_of_not_forallE {n} {a a' : Shape (n+1)} {r r'}
    (hC : Shape.Compat a a' = true) (hr : HasType a (.sort r)) (hr' : HasType a' (.sort r'))
    (hne : ∀ (b : Shape n) f (b' : Shape n) f', ¬(a = .forallE b f ∧ a' = .forallE b' f')) :
    ∃ r, HasType a (.sort r) ∧ HasType a' (.sort r)
```

**Proved.** `Compat` alone pins the sort in 35 of the 36 constructor pairs; `cx_refutes` is
confined to `forallE`/`forallE`. There, `ValTyPi2` supplies what `Compat` cannot: both
`PiDefEq`s carry `IH.TyDefEq (F₁.inst a) (F₂.inst a) (fᵢ.app p)` over the *same* `F₁ F₂`, so
the recursion at `n` applies to corresponding codomain values — take the bot-keyed element
`ShapeFun.WF` guarantees. Two sub-cases: a non-`.bot` value pins `rᵢ`; all-`.bot` makes
`HasTypePi fᵢ bᵢ r` hold for every `r`.

Estimate: one recursion on `n`, 35 of 36 cases `Compat`-closed, plus the two-sub-case argument
at `forallE`. 40–80 lines. Not machine-checked as a whole; `common_of_not_forallE` is.

---

## Session update 6: `join_sort` refuted; `ParamsExtra.extra_pat` was unsatisfiable and is now peeled

### `join_sort` is FALSE — refuted before it was built

Approved at 40–80 lines. Tested first, and the test refutes it: `join_sort_fails`, sorry-free.

`cx_refutes`'s two shapes both satisfy `LRS.TyDefEq` for **one and the same `A B`**, are
`Compat`, are each classified by a sort, and share none. The `ValTyPi2` witness is built with
`A = B = ∀ (_ : Sort 0), Sort 0`: the term-level fields are reflexivity at `.sort .zero`, and
`PiDefEq`'s two components land in `LRS.TyDefEq` at a `.bot`-or-`.indTy` shape, where the
clause is `True`.

The mechanism is `piDefEq_cannot_see`, also machine-checked — `PiDefEq` constrains a family
**pointwise in the key**, and at every key typed at `cxB` at most one of the two families has
a non-`.bot` value:

| `p` | `cxF.app p` | `cxF'.app p` |
|---|---|---|
| `⊥` | `⊥` | `⊥` |
| `.sort true` | `.indTy false` | `⊥` |
| `.indTy true` | `⊥` | `.indTy true` |

So the disagreeing values sit at keys the other family does not reach, and the relativisation
is vacuous at exactly the one constructor pair where `common_of_not_forallE` said it was
needed. That is the first diagnosis sentence one layer up.

**Every relativisation of `IsType.common` tried so far is now refuted**: `Compat`-only
(`cx_refutes`), `LE_Interp`-relative (`le_interp_common_fails`), `TyDefEq`-relative
(`join_sort_fails`). What is *not* refuted is `common_sort` — the sort read off the **term's
universe** — which is proved.

### `SExpr.ParamsExtra.extra_pat` was unsatisfiable

Reported by the Params stream, machine-checked, and confirmed against this tree. The field
asked for `p.MatchesS` on the **unpeeled** `df.lhs`; `Pattern.MatchesS.not_lam` (twenty lines
above it in the same file) says a pattern never matches a `lam`, and `SExpr.mk` and
`SExpr.instL` are both structural on `lam`. Every real rule shape has binders.

> **No `ParamsExtra` instance existed for any real environment, and `LE_Interp.strongSoundS`
> carries `[ParamsExtra]` — so it, and everything downstream of it, was vacuous.**

This is PLAN's original "`extra_pat` is unsatisfiable" entry. The mainline `VEnv.Params`
version was cured by λ-peeling (`Pat.extra_delta` / `_quot` / `_iota` in
`Theory/Typing/PatternRules.lean`); this copy never was. The field now mirrors the mainline,
with `Δ`, `L`, `R` and the check clauses discharged over `Δ.reverse ++ Γ`.

Two regression tests land with it, stated as conditionals on a hypothetical unpeeled field so
they cannot rot: `unpeeled_extra_pat_unsatisfiable` (any `lam`-headed lhs gives `False`) and
`iota_lhs_lam` (every ι-rule's lhs *is* `lam`-headed). Both `[propext, Quot.sound]`, no
`sorryAx`. `iota_lhs_lam` is proved from `Theory/Inductive/Decl.lean` alone, so
`Experimental/SExpr.lean` still does not import `PatternRules.lean`.

**Cost, measured.** `SExpr.lean` compiles clean. `ShapeLogRel.lean` gains exactly **2 errors,
both in `strongSoundS`'s `extra` case** — honest ones: both sides are now `mkLams Δ _` and the
matched redex is the body. Running the existing argument under `Δ` needs (a) a congruence
"`LE_Interp` respects the body of a `.lam`" (short — the binder is shared by both sides), and
(b) the two IHs and `W` transported under the telescope, needing `StrongSound` inversion
through `lam`. Neither is written; this is reported rather than absorbed.

---

## Session update 7: §7's residue is a design problem with no exit

Three exits were scoped; all three are now closed, two of them machine-checked this session.
This section states the problem at its sharpest, then inventories what a redesign would have
to change. **It is not a proposal.**

### The tension, minimally

Three properties. Each is stated as precisely as its witness states it.

**(i) `Eq.refl` has a `.ctor` shape.** `LE_Interp.Matches.app`'s index is
`WShape.ctor' c' rargs'.reverse`, and `Pattern.WF`'s `.const` clause demands a non-top
constant leaf be `classify`-ed `.ctor`. `Eq.rec`'s ι-rule must be a `Pattern`, because
`ParamsExtra.extra_pat` demands every `env.defeqs` rule be covered by some `Pat p r` and
`Params.pat_wf` demands `p.WF classify`. And the rule cannot simply be dropped:
`eq_large_eliminates` (proved) shows `@Eq.rec`'s motive is `Sort u_1`, so
`Eq.rec (motive := fun b _ => Nat) 7 rfl` is a `Nat` — not a proof, and its ι-redex is not
one either.

**(ii) `Eq`'s type-shape is `.indTy false`.** `Classification.indTy` carries `rel`, and
`ParamsExtra.ctor_ty` ties `rel = true ↔ D.lvl ≠ .zero`. `D.lvl` is the block's common result
universe, and it is `.zero` for `Eq`. This is a fact about the environment, not a design
choice.

**(iii) `proofIrrel`.** `WShape.HasType.proofIrrel (ha : HasType a .prop) (hx : HasType x a) :
x = .bot` — everything at a `Prop` has shape `.bot`.

The three are inconsistent, and the obstruction mentions neither `LE_Interp` nor `Params`:

```lean
private theorem ctor_not_prop_typed (a : Shape 1) (h : Shape.hasType piX a = true) :
    Shape.hasType a (Shape.prop (n := 1)) = false
```

**Proved.** No shape both classifies a `.ctor` and is itself `Prop`-valued. So `Eq.refl`
cannot simultaneously *have* a `.ctor` shape and *be typed* at its own type.

### The two exits, refuted

**Exit 1 — give up `proofIrrel` at Prop-valued inductives. FALSE.**
`exit1_bvar_separates` + `exit1_witness`, proved, and they need **no `Params` instance and no
environment**. `strongSoundS`'s `proofIrrel` case must show
`LE_Interp ρ m h ↔ LE_Interp ρ m h'` for two proofs of the same `Prop`; two proof *variables*
are the sharpest instance, because `LE_Interp.bvar` reads the shape straight off the
valuation, so the two sides see `ρ 0` and `ρ 1` and separate the moment those differ and
`m ≰ .bot`. `Valuation.Fits.cons` pushes `x` with `x.HasType a` for an `a` realizing the
variable's type; when that type is a Prop-valued inductive, §7's gating forces `x = .bot`
(`indTy_false_bot`) and both entries collapse. Exit 1 removes exactly that, `Fits` then admits
a non-`.bot` proof shape, and the lemma applies. Cost if taken anyway: 1 case in
`strongSoundS`, 1 use at `Adequacy:428` — and it fails **false and loud**, killing the
adequacy route to `sort_inv`.

**Exit 2 — give up the `.ctor` leaf in ι-patterns. Both forms closed.**
(β) — `Pattern.WF` demands `rel = true` at ctor leaves — is refuted by `eq_large_eliminates`
above, and its failure mode is **vacuous**: `ParamsExtra` becomes unsatisfiable for every
environment containing `Eq`, with no instance in the tree to notice.
(α) — keep the rule, give the leaf a `.bot` shape — is refuted by
`toy_unique_fails`. `Matches.unique`'s `app` case recovers `c'` and `rargs'` *from* the leaf
shape (`head_wf` → `classify c' = .ctor` → `IsStruct c' = false` → `ctor'` takes its `.ctor`
branch → `WShape.ctor.inj` + `List.reverse_inj`), so it rests on the leaf being **injective**.
`ctor'_inj_of_not_struct` proves that injectivity holds today and why; `ToyMatches`, a
miniature of the `app`/`var` interaction parameterised by the leaf function, then shows
injective leaf ⇒ uniqueness (`toy_unique_of_inj`) and collapsing leaf ⇒ **uniqueness is
false**. Measured cost had it been taken: 2 edits in `SExpr.lean`, **107 error instances at 60
lines** in `ShapeLogRel.lean` *before* `ctor'`'s guard is touched, and then `unique`.

**Exit 3 — give up `InterpTyped`'s totality — degenerates to Exit 1.** The blunt form costs
+21 errors, and the failures (`True.bot_r'`, `True.ty_forallE_inv`) name what the field is
*for*: `InterpTyped`'s classification is what lets the model **destructure** a shape.
`sound_app` uses it to learn a function's shape is a `.forallE` before applying it. So the
interpretation needs a classifying shape only for terms it destructures — and every
non-`proofIrrel` consumer sits at a `.forallE` or `.sort` type-shape, while a term whose type
is a Prop-valued inductive is never applied and never a binder's domain. The targeted
exemption therefore never fires at those sites and costs exactly `proofIrrel`'s input.

### Which of the three is least load-bearing

Not (ii): it is a fact about `Eq`, not a choice.

Not (iii), and this is worth stating carefully, because it looks like the negotiable one.
`proofIrrel` is not an extra constraint bolted onto the model — **it *is* the model's
treatment of proofs.** The shape lattice has no representation of proof content; collapsing
every proof to `.bot` is what makes proof irrelevance hold in it, and `strongSoundS` needs
that at exactly one case. Give it up and the case is false, as Exit 1 shows.

**(i) is the least load-bearing, but not in the way (α) and (β) tried.** What the model needs
from a constructor leaf is not that the *shape* be `.ctor` — it is that the matched argument
list be **recoverable**. Today those are the same thing, because
`LE_Interp.Matches.app`'s index *is* `WShape.ctor' c' rargs'.reverse`: the shape is the only
record of `rargs'`. `unique` then reads the arguments back out of it, which is why a
`.bot` leaf destroys the lemma rather than merely complicating it.

    The shape is doing double duty: it is both the term's semantic shape and the pattern
    matcher's bookkeeping. §7 forces those two roles apart, and the model has no way to
    separate them.

### What a redesign would have to change — inventory, not proposal

| component | verdict | reach |
|---|---|---|
| `Shape`, `Shape.hasType` | **gains a case; already done** | §7's gating (`.ctor _ _, .indTy r => r`) is applied and `proofIrrel` is proved. Nothing further needed here. |
| `Pattern.WF` | **unchanged** | must keep demanding a `.ctor` leaf, or `Eq.rec`'s rule stops being a pattern — that is (β), refuted. |
| `LE_Interp.const` / `InterpTyped` | **unchanged** | Exit 3 degenerates to Exit 1; the classification is load-bearing for destructuring. |
| `Classification.ctor` / `.etaCtor` | **gains a field** | the Prop-ness guard must be decidable from the name, so the boolean has to live in `classify`. **Measured: 2 edits in `SExpr.lean` (clean) + 107 instances at 60 lines in `ShapeLogRel.lean`.** |
| `LE_Interp.Matches` | **changes shape** | its index must carry the matched arguments *independently of the leaf shape*, so a proof-valued leaf can be `.bot` without losing `rargs'`. Reaches `Matches` itself and `matches_inter`, `compat_join`, `unique`, `mono_l`, `arity`, `head_wf`, `head_wf_eq`, `lift`, `of_matchesS`, plus `Const.pat`, `build_spine` and `RHS.of_applyS`. **≈12–15 declarations.** |

So the cost *to know* is: the 107-instance `Classification` change, plus re-indexing
`LE_Interp.Matches` across ≈12–15 declarations. Neither number is a guess — the first is
measured, the second is a count of the consumers.

### Do the other two groups survive it?

**The join family: independent.** Its obstruction is `IsType.common` at `forallE`/`forallE` —
about the *domains* of Pi-shapes — and has nothing to do with `.ctor` leaves or `proofIrrel`.
Three relativisations are *refuted* — `Compat`-only (`cx_refutes`), `LE_Interp`-relative
(`le_interp_common_fails`), `TyDefEq`-relative (`join_sort_fails`). A fourth, the
classified-upper-bound form `common_of_le`, is **proved but not producible**: obtaining the
single upper bound at a call site needs `LE_Interp.join'`, which is `compat_join.2` and so one
of the broken sites — circular. The survivor that is both true *and* producible is
`common_sort`, which reads the sort off the **term's universe**. A §7 redesign neither helps
nor hurts any of this.

**The λ-peel: independent, and survives.** It is about `extra_pat`'s statement shape and
`SExpr.mkLams`, and touches `MatchesS`, not `Matches`. Its two residual errors, in
`strongSoundS`'s `extra` case, are about λ-telescopes.

**The per-leaf level lists: not invalidated, and overlapping.** Its one open obligation is
that `LE_Interp.Const.pat` binds its level map existentially, so `Const` cannot record it —
and closing that means `LE_Interp.Const` and `LE_Interp.Matches` indexed by `LPath`. **That is
the same re-indexing the §7 redesign needs**, for the same reason: `Const`/`Matches` carry
less than the model needs, and the shape is being asked to make up the difference. The two
would be done together, and the per-leaf obligation would likely close as a side effect.

---

## Session update 8: per-leaf level lists — the second `ParamsExtra` vacuity

The λ-peel (update 6) was **not enough**. `ParamsExtra` was still unsatisfiable, so
`strongSoundS` was still vacuous.

`Pattern.MatchesS` recorded a *single* `List SLevel` for a whole match — its `app` rule kept
the function side's list and discarded the argument side's — where the `VExpr`-side `Matches`
records one per leaf. Its docstring called that deliberate and priced it at one consequence:
`applyS` ignoring an `RHS.fixed`'s `LPath`. **There was a second, and it was fatal.**
`Check.defeqsS` also dropped the two `LPath`s of a `Check.level x i y j` clause and read
*both* indices out of the one list. On the `VExpr` side that clause relates the **recursor**
leaf's list to the **constructor** leaf's — which is what makes `iotaLevelPairs`' `(i+1, i)`
true, since `selfLvls` is the block's parameters shifted by one when `isLE` prepends a fresh
elimination universe, so both sides evaluate to `ls.getD (i+1)`. Read out of one list it
degenerated to `ls.getD (i+1) = ls.getD i`, relating the elimination universe to a block
parameter — and `extra_pat` quantifies over every `ls` of the right length. **False for any
large eliminator with a universe parameter: `List`, `Prod`, `Sum`, `Sigma`.**

Fixed. `MatchesS`, `RHS.applyS` and `Check.defeqsS` carry `p.LPath → List SLevel`;
`LE_Interp.RHS` gained the `LPath` index; `LE_Interp.Const` dropped its shared `ls`;
`Const.pat` binds the map; `build_spine` reads the head leaf via `Pattern.LPath.head`.

**Measured:** `SExpr.lean` **4 edits, compiles clean**. `ShapeLogRel.lean` **+1 error over
baseline**. The intermediate counts are worth recording because they are almost entirely
cascade — **318 → 26 → 16 → 12**. The 318 was *one* root failure: Lean drops an unused
`variable`, so `LE_Interp.Const` silently lost its `ls` and `LE_Interp` stopped elaborating,
taking two hundred lines with it. Do not read an early count on this refactor as a cost.

The one obligation left is the `Const.pat` level-map gap described in update 7.

### The rule this leaves behind

> **A deferral must never be stated as "the cost is X". State it as "the cost includes X; not
> audited for others."**

A stale docstring can be caught by checking it against the code. A complete-*looking* partial
deferral gives the reader no signal that anything is missing, so it survives every check — and
this one concealed an unsatisfiable class through a whole session that was explicitly hunting
unsatisfiable classes.

---

## Session update 9: the re-indexing, scoped — 28 rows, and the earlier ≈12–15 was an undercount

### Row zero: the statement is sufficient, and it is checked

"The index carries the matched arguments independently of the leaf shape" **is** sufficient for
`Matches.unique`. `ToyMatchesR` and `toy_unique_of_record` (both proved) put the matched datum
in the *index* and leave the shape as `leaf rec`, still free to collapse; uniqueness then holds
**for any `leaf`, injective or not** — `toy_unique_of_record_bot` instantiates it at exactly
the collapsing leaf that `toy_unique_fails` refutes. So `unique` stops needing leaf
injectivity, which was the obstruction. Row zero clears.

### The record type

`MArg n`, level-indexed like `Shape`: `.shape (x : WShape n) : MArg n` for a `var` position,
`.ctor (c : Name) (l : List (MArg n)) : MArg (n+1)` for an `app` position, with
`MArg.toShape : MArg n → WShape n` derived.

Two things constrain it, and both were found by checking rather than assuming:

**It must carry shapes, not just term-level data.** `Matches.var`'s index entry *is* the
argument shape and `unique`'s induction needs it. A names-and-levels-only record — which would
have been term-determined, and so automatically shared between two interpretations — does not
close the induction.

**`Const`'s index must move too.** Leaving `Const` on shapes and having `Const.pat` bind the
record existentially re-introduces the collapse one level up, at `Const.compat_join`'s
`pat`/`pat` case — the same gap as the per-leaf `lsm`, for the same reason. That is what makes
this one change rather than two. It is also where the earlier count went wrong: **≈12–15
counted `Matches`' consumers and missed that `Const` consumes the index**, and therefore needs
an order, a join and a lift on it.

One refinement worth having before writing row 3: `matches_inter` relates matches of two
*different* patterns, so `MArg.Compat` must handle the mixed `.shape`/`.ctor` pair;
`compat_join` relates two matches of the *same* pattern, so `MArg.join` is only ever applied to
pattern-aligned pairs. **Compat total, join partial.**

### The rows

`M` mechanical (retype, proof unchanged) · `P` positional (indices move, structure unchanged) ·
`S` structural (needs a new argument or definition).

| # | | row |
|---|---|---|
| | | **A — the record type (new)** |
| 1 | S | `MArg` + `MArg.toShape` |
| 2 | M | `MArg.lift` and its `lift_lift`/`lift_self` |
| 3 | S | `MArg.LE` and order lemmas |
| 4 | S | `MArg.Compat` — **total**, incl. the mixed pair |
| 5 | S | `MArg.join` on pattern-aligned pairs + `Join.mk` |
| 6 | S | `toShape` monotone; commutes with `lift`, `join` |
| | | **B — `Matches` re-indexed** |
| 7 | S | `LE_Interp.Matches` (inductive) |
| 8 | M | `varN_const_head` |
| 9–11 | P | `arity`, `head_wf`, `head_wf_eq` |
| 12 | S | `mono_l` (needs `MArg.LE`) |
| 13 | S | `matches_inter` (needs total `Compat`) |
| 14 | S | `compat_join` (needs `join`) |
| 15 | M | `unique` — **gets shorter**; the `ctor'`-injectivity step goes |
| 16 | M | `lift` |
| 17 | P | `of_matchesS` |
| | | **C — `Const` re-indexed** |
| 18 | S | `LE_Interp.Const` (inductive) |
| 19 | P | `mono` |
| 20 | S | `mono_l` (needs `MArg.LE`) |
| 21 | M | `lift` |
| 22–23 | P | `closed`, `compat_mismatch` |
| 24 | S | `compat_join` — **where update 8's open obligation closes** |
| | | **D — consumers** |
| 25 | P | `LE_Interp.const` and the lemmas casing on it |
| 26 | P | `apps_realize` / `apps_realize_inv` |
| 27 | S | `build_spine` — builds the record from the `MatchesS` |
| 28 | P | `strongSoundS`'s `pat` and `extra` cases |

**28 rows: 9 structural, 8 positional, 6 mechanical**, plus group A being a small lattice.
`Shape`'s own LE/Compat/join API in this file runs ~200 lines; `MArg`'s has no
`forallE`/`lam`/`sort` cases, so ~80–120.

### What it buys, and what it does not

**Buys both problems.** §7's `.ctor`-leaf obstruction — the leaf may collapse to `.bot` for a
Prop-valued head without `unique` noticing — and update 8's open obligation, which closes at
row 24 because `Const` finally records what it needs.

**Still required on top, for §7:** `Classification.ctor`/`.etaCtor` gain the boolean,
separately measured at 2 edits in `SExpr.lean` and **107 instances at 60 lines** in
`ShapeLogRel.lean`.

**Does not touch** the join family (its obstruction is about Pi-shape *domains*) or the λ-peel
(which lives on `MatchesS`). Both survive unchanged.
