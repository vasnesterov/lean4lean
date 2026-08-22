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
