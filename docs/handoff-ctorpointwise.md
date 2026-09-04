# handoff: ctorpointwise

Round scope: one lemma (pointwise strengthening of `RestoreData.ctor`) and one
consequence (`TrIndDeclN.trCtorsLen`). Owned files: this file and
`Lean4Lean/Verify/Inductive/CtorPointwise.lean`.

## 1. Priors (written BEFORE the first measurement, so they can be scored)

Written from the brief alone; nothing in the repo has been read yet this round
except `CLAUDE.md`, `git status`, `git log -5`, and `ls scripts docs`.

P1. The brief's characterisation is right in *shape*: `RestoreData.ctor` is an
    existential `∀ C ∈ T.ctors, ∃ c ∈ t.ctors, …`. **~75%.** The brief's numbers
    have been exact all session, and this is close to a number (a field name at a
    line range).

P2. `trCtorsLen` is NOT already derivable — i.e. this round is not a
    fourth "already done". **~55% not-done / 45% already-done.** Four
    assignments this session were already discharged, and the brief itself flags
    the risk, which is evidence the base rate is high. I lean slightly to
    not-done only because a *length* field is unusual to have lying around
    without the pointwise lemma the brief says is missing.

P3. If mkRestore builds the restored ctor list by a `List.map` over the original
    ctors, the index correspondence is true by construction and this round is
    bookkeeping, not mathematics. **~55%** that it is a plain `map`.

P4. Chief technical risk: **existential → pointwise needs a canonical choice**,
    and if mkRestore uses `filterMap`, `append`, or reorders (e.g. puts nested
    auxiliary ctors somewhere), then the *length equation as stated may be
    false* and the honest deliverable is a different correspondence (a
    `Forall₂`/`Pairwise` over a permutation, or a length inequality).
    **~25%** that the naive `length = length` needs weakening.

P5. Second risk, the one I expect to actually cost time: even with an index-wise
    `map`, `TrIndDeclN.trCtors` needs *translation* of each ctor type, which
    `trType` (a sibling open field, not mine) supplies. So `trCtorsLen` should
    be provable WITHOUT `trType`, and if I find myself needing `trType` I have
    mis-scoped. **~70%** that trCtorsLen is trType-independent.

P6. Vacuity: my arity-0 witness at `ntreeAux` will be at real risk of leaning on
    `ntreeAux_trIndDeclN` (which already discharges all three fields by hand).
    I predict I will need to *deliberately* route around it, and that the
    general route will fire. **~60%** the general route fires without a
    block-specific lemma.

P7. Round-close census 13 / NOT BUILT 0 will hold; the likeliest way to break it
    is a name collision with a concurrent `TrType*.lean` stream. **~85%** clean.

Blind-spot self-check I am explicitly guarding against: my prior P3/P4 both
assume the constructor list is the thing that is built. If `mkRestore` instead
*restores* by recursion on a witness structure, "index-wise" may not even
typecheck as a statement, and the right lemma is about the witness, not the
list. I will run `shape.lean` on the actual definition before writing anything.

## 2. Measurements (appended one line per script call, as made)

M1 (source read, `Verify/Inductive/NestedRestore.lean:283-285`). **P1 CONFIRMED
exactly.** The field is

    ctor : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → ∀ t, r.types[j]? = some t →
      ∀ C ∈ T.ctors, ∃ c ∈ t.ctors, c.name = C.name

one-directional, existential, no length and no index. Its siblings `len`
(`r.types.length = D.types.length`) and `name` (index-wise!) are *not*
existential — so `ctor` is the odd one out in its own group, which is evidence
the pointwise form is what was intended and just was not needed yet.

M1a (same read, an immediate complication the brief did not mention). `ctor`
relates `D.types[j]` to **`r.types[j]`** — the *elaborated* list on the
`Result` — whereas `TrIndDeclN.trCtorsLen` relates `D.types[j]` to
**`types[j]`**, the *user's* `List Lean.InductiveType`. So a pointwise `ctor`
does not by itself reach `trCtorsLen`: a second link `types[j] ↔ r.types[j]`
for `j < types.length` is needed. Whether that link exists is now the question.

M2 (`scripts/exists.lean`, 440 built modules, 6 watched). All five present and
clean:
  Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_built — arity 14, cone 2061; hole false; sorryAx false; watched: none of 6
  Lean4Lean.ElimNestedInductive.Result.RestoreData.ctor — arity 13, cone 560; hole false; sorryAx false; watched: none of 6
  Lean4Lean.ElimNestedInductive.Result.RestoreData.len — arity 6, cone 52; hole false; sorryAx false; watched: none of 6
  Lean4Lean.ElimNestedInductive.Result.RestoreData.name — arity 11, cone 551; hole false; sorryAx false; watched: none of 6
  Lean4Lean.TrIndDeclN.trCtorsLen — arity 15, cone 552; hole false; sorryAx false; watched: none of 6

M3 (source read, `Verify/Inductive/TrIndDeclNProducer.lean:47-123`). The hook is
already cut for me: `trIndDeclN_of_ownId` / `trIndDeclN_of_restoreData` carry
`hclen` as a *named explicit hypothesis* of exactly `trCtorsLen`'s statement. So
"derive `trCtorsLen`" = "discharge `hclen` from `RestoreData`", and no edit to
any producer is needed — a standalone theorem in my own file suffices. This is
good news for scope and confirms P5's independence claim in *form*: `hclen` sits
beside `hty`, not under it.

M4 (`scripts/shape.lean`, HEADS="Lean.InductiveType.ctors Lean4Lean.VIndType.ctors List.length", 440 modules).
32 constants conclude something mentioning all three heads, 7 of them structure
fields. **Nothing in the tree concludes a free-standing
`t.ctors.length = T.ctors.length` for the nested case**: the only `trCtorsLen`s
are the two structure FIELDS (`TrIndDecl.trCtorsLen` — the *non*-nested relation
— and `TrIndDeclN.trCtorsLen` itself). So P2's not-done branch holds: this is
not a fifth "already done". Two names to check before concluding anything,
though, both in `Verify/Inductive/TrIndDeclNCtorOwn.lean`:
`Lean4Lean.ElimNestedInductive.Result.name_and_ctor_prefix_of_run` (arity 18)
and `Lean4Lean.ElimNestedInductive.Result.ctor_prefix_of_run` (arity 26).

M5 (source read, `Verify/Inductive/TrIndDeclNCtorOwn.lean:198-292`). **THE
BRIEF'S DIRECTION IS BACKWARDS, and this is the round's main finding.**
`Lean4Lean.ElimNestedInductive.Result.ctor_prefix_of_run` proves
`RestoreData.ctor`'s prefix half **from** `TrIndDeclN`, and its proof uses
`htr.trCtorsLen` by name:

    have hqlt : q < u.ctors.length := by
      rw [htr.trCtorsLen j u T hu hT]; exact List.getElem?_eq_some_iff.1 hq |>.1

So `trCtorsLen` is *upstream* of `RestoreData.ctor`, not downstream of it.
Deriving `trCtorsLen` from a strengthened `RestoreData.ctor` would re-close
exactly the kind of cycle `docs/vacuity-ledger.md` rows 80a/91c were about —
this time with `trCtorsLen` as the repeated edge. The file even says so in
prose: the escape from the 80a/91c circle *was* to route through `trCtorsLen`
and `ctorName_own` precisely because they mention no `R`.

Consequence for the assignment: brief item (a)'s stop condition ("the `ctor`
field is not what blocks it") is met, subject to one check — whether any
*general* route establishes `RestoreData.ctor` without a `TrIndDeclN` in hand.
If not, the pointwise strengthening is not merely unhelpful, it is unusable.
Measuring that next.

M6 (`scripts/users.lean`). 
  Lean4Lean.ElimNestedInductive.Result.RestoreData.ctor — DIRECT 5 in 4 modules; TRANSITIVE 49 in 11 modules
  Lean4Lean.TrIndDeclN.trCtorsLen — DIRECT 3 in 3 modules (TrIndDeclNCtorOwn, RunIdentity, InductR); TRANSITIVE 14 in 6 modules
  Lean4Lean.ElimNestedInductive.Result.RestoreData.mk — DIRECT 9 in 6 modules; TRANSITIVE 36 in 9 modules
`trCtorsLen`'s three direct users include `Verify/Inductive/RunIdentity.lean`,
which the brief did not mention; checking it next in case it already supplies
what I was sent for.

M7 (`scripts/shape.lean`, HEADS="Lean4Lean.ElimNestedInductive.Result.RestoreData",
440 modules). 63 constants, 14 of them fields. **Every declaration that
*concludes* a `RestoreData` bundle is block-specific and arity-0**:
`NestedWit.nfnResult_restoreData`, `nfnResult_restoreData_junk`,
`nfnResult_restoreData_junkArgs`, `nfnResult_restoreData_badD`,
`nfnResultBadHead_restoreData`, plus `nfnResult_restoreData_of_occursN`
(arity 2) and `HypTrim2.restoreData_refuted_at_badTypes` (arity 4, a refutation).
There is **no general theorem concluding `r.RestoreData types D K as`**;
everything else named `RestoreData.*` *consumes* the bundle.

Verdict (a) is therefore settled twice over: `RestoreData.ctor` is (i) proved
only downstream of `trCtorsLen` in the general case, and (ii) never established
generally at all. A pointwise strengthening of it would be an unusable premise
for `trCtorsLen`, and using it would rebuild the 80a/91c cycle.

M8 (source read, `Verify/Inductive/NestedRunInvariant.lean:217-644`). **P3 was
right about the mechanism and wrong about the location.** The index-wise
correspondence *is* by construction — but it lives in `nameSkel` /
`RunSkelExtends` / `run_prefix`, not in `mkRestore`. `run_prefix` already
delivers

    t.ctors.map (·.name) = u.ctors.map (·.name)

between the checker's output member `t = r.types[j]` and its input member
`u = types[j]` on the prefix. A *map* equation is index-wise and gives a length
equation for free. So the pointwise strengthening of `ctor` is cheap — in the
direction `TrIndDeclN ⟹ pointwise ctor`, which is the direction the tree has.

M9 (source read, `Verify/Environment/InductR.lean:238-239`). `auxRecName types k
= appendIndexAfter' (mkRecName (types.headD default).name) (k+1)`. Combined with
a field-by-field read of `RestoreData`, **`types` occurs in the bundle only
through `types.length` and `(types.headD default).name`** — never through
`types[j].ctors`. That is a structural proof that the *whole* bundle, not merely
its `ctor` field, is independent of `trCtorsLen`. I will machine-check it as a
transport lemma plus a refutation rather than assert it.

M10 (`scripts/shape.lean`, HEADS="Lean4Lean.TrIndDecl"). 28 constants, 7 fields.
The *non*-nested `TrIndDecl` has no general producer either — only arity-0
concrete witnesses (`trIndDecl_eq`, `R10.Wit.trIndDecl_wit`,
`R113a.trIndDecl_declLE`) and the bridge `TrIndDecl.toN` (arity 8), which
consumes one. So "the translation exists" is open across the board, and
`trCtorsLen`'s real supplier is a `List InductiveType → VInductDecl'`
construction that does not exist in the tree. `trCtorsLen` is not "the cheapest
of the three open fields waiting on one lemma"; it is the bookkeeping *component*
of the same missing construction that owes `trType` and `trCtors`.

M11 (LSP diagnostics on the authored file, `Lean4Lean/Verify/Inductive/CtorPointwise.lean`,
288 lines). Zero errors, zero warnings. `#print axioms` on the three headline
results: all `[propext, Classical.choice, Quot.sound]`.

## 3. Priors scored

P1 (ctor field is existential, 75%) — **right**, verbatim (M1).
P2 (not already done, 55%) — **right** (M4, M7); nothing concludes `trCtorsLen`.
P3 (index-wise by construction via a `List.map`, 55%) — **half right, and the
    half I got wrong is the interesting one.** The correspondence *is* a `map`
    equation, but it is in `ElimNestedInductive.nameSkel`/`run_prefix`, not in
    `mkRestore`. I inherited the brief's location and did not question it. (M8)
P4 (length equation might need weakening, 25%) — **wrong**; the length equation
    between checker output and `D` is true and easy. What was wrong was the
    *direction*, which I did not have on my risk list at all.
P5 (trCtorsLen is trType-independent, 70%) — **right in form** (M3: `hclen` sits
    beside `hty` as a sibling hypothesis of the producer), and *misleading in
    substance*: they are independent as hypotheses but owed by the same absent
    construction (M10).
P6 (general route fires at ntreeAux without a block-specific lemma, 60%) —
    **right**; §4 goes through §2 with `ntreeAux_trIndDeclN` supplying only the
    `TrIndDeclN` hypothesis.
P7 (census clean, 85%) — see §5.

**The blind spot, named.** Every one of my seven priors was about the *content*
of the lemma — is it true, is it a map, does the length hold. Not one asked
**which way the existing tree already runs the implication**, and that is the
only thing that mattered: `ctor_prefix_of_run` had already been proved *from*
`trCtorsLen` three commits earlier, in a file whose own docstring says so. The
brief's calibration note warned that its *attributions* were unreliable; my
priors treated that warning as being about which file something lives in, and it
was really about which direction an arrow points. A prior list that asked "what
does the tree already derive from this?" before "is this true?" would have found
the answer in one `grep`.

## 4. Delivered (all in `Lean4Lean/Verify/Inductive/CtorPointwise.lean`)

M12 (`scripts/exists.lean`, 442 built modules, 6 watched). Every one: `own value
is a hole: false`, `cone reaches sorryAx: false`, `watched declarations in cone:
none of 6`.

  Lean4Lean.ElimNestedInductive.nameSkel_prefix — arity 8, cone 664
  Lean4Lean.trIndDeclN_ctorPointwise — arity 19, cone 713
  Lean4Lean.trIndDeclN_ctorPointwise_of_run — arity 24, cone 5797
  Lean4Lean.trIndDeclN_ctor_exists — arity 21, cone 745
  Lean4Lean.ElimNestedInductive.Result.RestoreData.congr_types — arity 9, cone 809
  Lean4Lean.trCtorsLen_not_of_restoreData — arity 0, cone 3779
  Lean4Lean.InductiveDeclExamples.ntreeAux_ctorPointwise — arity 0, cone 5970

Also present, an abstraction check rather than a result:
`Lean4Lean.ElimNestedInductive.nameSkel_prefix_covers_run`.

What each one is:

* `nameSkel_prefix` — `run_prefix`'s body with `run` abstracted to the bare
  skeleton equation `nameSkel rtypes = nameSkel types ++ tail`. Strictly more
  general; `nameSkel_prefix_covers_run` records that `run_prefix`'s hypothesis is
  an instance, so this is a generalisation and not a second proof.
* **`trIndDeclN_ctorPointwise`** — the commissioned lemma, in the direction that
  exists: from `TrIndDeclN` + a skeleton extension, on the prefix,
  `t.ctors.length = T.ctors.length` **and** `∀ q c C, t.ctors[q]? = some c →
  T.ctors[q]? = some C → c.name = C.name`. Both halves the brief asked for.
* `trIndDeclN_ctorPointwise_of_run` — the same at `run`, i.e. the exact hypothesis
  set of `Result.ctor_prefix_of_run`.
* `trIndDeclN_ctor_exists` — `ctor_prefix_of_run`'s existential conclusion,
  derived from the pointwise one, so §2 *subsumes* the existing lemma.
* `RestoreData.congr_types` — the invariance: `RestoreData` sees `types` only
  through `types.length` and `(types.headD default).name`.
* **`trCtorsLen_not_of_restoreData`** — `¬ ∀ r types D K as, RestoreData … →
  trCtorsLen`. The commissioned route is refuted, not merely declined.
* `ntreeAux_ctorPointwise` — §5's witness.

## 5. Round close

* whole-tree `lake build`: **green**, 1628 jobs, "Build completed successfully".
  A concurrent stream's `Lean4Lean.Verify.Inductive.TrTypeProducer` built in the
  same run; no name collision with this file.
* `scripts/sorry-census-all.lean`: on disk 469; population 445; **BUILT 445, in
  population but NOT BUILT 0**; **HOLES 13** (pass A 13, pass B 0). No
  collision/duplicate line in the output.
* guards: `guard 1: Axioms.lean declares exactly the 24 frozen axioms ✓`;
  `guard 2: kernel_sound axioms within whitelist ✓ (proof INCOMPLETE: sorryAx
  present)`; `guard 3: checker cone implementation gaps within frozen list (2/2
  remaining) ✓`.
* section-variable warnings **in this repo: zero**. The only
  `linter.unusedSectionVars` warning in the build is
  `Foundation/FirstOrder/SetTheory/Z.lean:35`, in the pinned dependency.
* frozen files untouched; no state-changing git; `docs/vacuity-ledger.md` not
  touched.

## 6. What remains for `trCtorsLen`, and for `trCtors`

**`trCtorsLen`.** Not blocked on `RestoreData.ctor` (refuted above). Its supplier
must be whatever *constructs* `D : VInductDecl'` from the user's
`types : List InductiveType`, because it is the only thing in the picture that can
see `types[j].ctors` and `D.types[j].ctors` at once. No such construction exists
in the tree (M10). Once it does, and if it builds `D.types[j].ctors` as a
`List.map` over `types[j].ctors`, `trCtorsLen` is `List.length_map` — genuinely
cheap, but *after* that construction, not before it. Any brief that prices
`trCtorsLen` separately from `trType`/`trCtors` is pricing three views of one
obligation.

**`trCtors`** (explicitly not attempted). It needs
`TrIndCtorR env₁ Us D R j c C` for the `q`-th constructor at each user member,
i.e. a `TrExprS` between `c.type : Expr` and the restored abstract constructor
type. Names are worthless for it; §2's index-wise name correspondence supplies
the *indexing* only. Its three visible sub-obligations, from the ntreeAux witness
that discharges it by hand: (i) the staged environment `env₁` must hold the
block's own type constants (`addIndTypesC D K = some env₁`, already a premise);
(ii) a `TrExprS` bridge per constructor type, of which the tree has exactly two
concrete instances (`tr_ntreeNodeType`, and `nfnNode`'s in
`Verify/Environment/InductR.lean`), both hand-built from `exprOf%` data; (iii)
the `R.ctorName C.name = c.name` half, which is where `OwnId.ctorName` and hence
rows 80a/91c's cycle live. (ii) is the real cost and it is the same missing
`Expr → VExpr` translation construction as `trType`'s.
