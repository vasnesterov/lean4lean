# Handoff: the stratified route to `IsDefEqU.sort_inv`

Written at a boundary, for a fresh reader with no context. Everything below is either
machine-checked (names given, axioms given) or explicitly marked as analysis.

**Target:** `Lean4Lean.VEnv.IsDefEqU.sort_inv` and its family in
`Lean4Lean/Theory/Typing/Injectivity.lean`. **Still open.** Five sorry-free files have landed
on this route and none of them moves the target statement. That is the accurate summary; do
not read the volume of landed work as progress on the goal.

---

## 0. Read this first, or you will re-derive a wrong conclusion

Two days of work in this tree concluded that sort-confluence, Π-injectivity and universe
uniqueness are one inseparable induction — that the circularity is *mathematical*. **That
conclusion is wrong, and it is wrong in a way that is invisible from inside the tree**,
because every definition, proof and dependency here is consistent with it.

The truth, settled by reading eleven lines of the reference
(`~/lean-type-theory/axioms.tex:30–41`):

- **Carneiro's conversion judgment is three-place**, `Γ ⊢ e ≡ e'`. Of its eleven rules
  **exactly one** — application — mentions a type, and there `Γ ⊢ e ≡ e' : α` is stated at
  `:41` to *abbreviate* `Γ ⊢ e ≡ e' ∧ Γ ⊢ e : α ∧ Γ ⊢ e' : α`. `symm` and `trans` carry no
  type. The λ and ∀ congruences carry no type. The conversion rule (`:19`) belongs to the
  **typing** judgment, not to `≡`.
- **`VEnv.IsDefEq` makes the type an index**, so every rule shares it: `trans` demands one
  `A` for both halves, `lamDF` one level and one codomain. `IsDefEqU` — the reference's
  actual judgment — is *derived*, the opposite direction.

**Consequence, and this is the whole finding:** composing two `IsDefEqU` facts is a theorem
here (`IsDefEq.uniqU`) where the reference has a rule. That is why `UniqueTyping.lean` must
export `trans_l`, `trans_r`, `transU_*`, `of_l`, `of_r`, `defeqU_*` — **a family with no
counterpart in the reference** — and why `ChurchRosser.lean` uses that family in 23 of its 85
declarations, including every backbone lemma. The same pressure forces `NormalEq`'s
constructors to carry *shared* type data (its `appDF` demands one `.forallE A B` typing both
functions) where the reference's `≡ₚ` congruences (`unique.tex:113–118`) carry none.

**So the Π-injectivity dependency in the confluence development is an artifact of this
tree's port, not of the mathematics.** The reference's proof never incurs it.

Mechanically checked, not read off prose: `Theory/Typing/RawDefEq.lean` transcribes the
reference's judgment as `VEnv.IsDefEqRaw` and erases into it (`IsDefEq.raw`, axioms
`[propext]` only, no injectivity, no unique typing). In that proof **the conversion rule
`defeqDF` erases to nothing** — its case is `exact ih2`. In the three-place presentation the
conversion rule has no content. That is the sharpest available demonstration that the port
added content rather than transcribing it.

**General rule this yields, and it recurred:** *when a question is about whether something is
necessary, the tree can only tell you what it currently does; necessity has to be checked
against the specification it claims to implement.* `CLAUDE.md` lists
`~/lean-type-theory/` as the spec blueprint. Open it early.

---

## 1. What is proved

All axiom lists below are from `#print axioms`, taken at handoff time. `Quot.sound` and
`propext` are standard; the whitelist in `Verify/Axioms.lean` governs what ultimately
matters. **Nothing here uses `sorryAx`** except where explicitly noted, and nothing uses
`native_decide`/`bv_decide` (checked, not assumed).

| Name | File | Axioms |
|---|---|---|
| `VEnv.WF.defeq_isDeclRule` | `Typing/DeclRules.lean` | `propext, Quot.sound` |
| `VEnv.WF.instL_lhs_ne_sort` | `Typing/DeclRules.lean` | `propext, Quot.sound` |
| `VEnv.WF.instL_lhs_ne_forallE` | `Typing/DeclRules.lean` | `propext, Quot.sound` |
| `VEnv.HasTypeStrong.sort_type` | `Typing/SortUniq.lean` | `propext, Quot.sound` |
| `VEnv.sort_not_proof` | `Typing/SortUniq.lean` | `propext, Classical.choice, Quot.sound` |
| `VEnv.IsDefEq.raw` | `Typing/RawDefEq.lean` | `propext` |
| `VEnv.Stratified.mono` | `Typing/Stratified.lean` | `propext` |
| `VEnv.IsDefEqN.zero_iff` | `Typing/Stratified.lean` | `propext` |
| `VEnv.IsDefEqStrong.stratifyN` | `Typing/Stratified.lean` | `propext, Quot.sound` |
| `VEnv.IsDefEq.stratifyN` | `Typing/Stratified.lean` | `propext, Quot.sound` |
| `VEnv.Stratified.weakN` | `Typing/Stratified.lean` | `propext, Quot.sound` |
| `VEnv.Stratified.instN` | `Typing/Stratified.lean` | `propext, Quot.sound` |
| `VEnv.IsDefEqN.inst0` | `Typing/Stratified.lean` | `propext, Quot.sound` |

One deliberate exception: `VEnv.WF.sortUniq` (`Typing/SortUniqFacts.lean`) has no literal
`sorry` but reports `sorryAx`, because it derives `SortUniq` *from* `sort_inv` + `uniq`. It
exists only as an upper bound on the strength of the `SortUniq` hypothesis — evidence the
reduction in `SortUniq.lean` smuggles in nothing extra. It is **not** evidence `SortUniq`
holds.

### What the pieces are

- **`DeclRules.lean`** — every definitional-equality rule of a `VEnv.WF` environment is a
  δ-rule, the quotient rule, or an ι-rule; hence no rule's `lhs` is a `.sort` or a
  `.forallE`. This is the "⊆" direction the tree lacked. *Overlaps
  `Typing/PatternRules.lean`'s richer `VEnv.RuleShape`*; kept small only because
  `Injectivity.lean` cannot afford `PatternRules`' import cone. If consolidating, keep
  `RuleShape` and delete `VDefEq.IsDeclRule`.
- **`SortUniq.lean`** — `VEnv.SortUniq`, universe uniqueness
  (`Γ ⊢ e : .sort u → Γ ⊢ e : .sort v → u ≈ v`), stated as a hypothesis, plus
  `sort_not_proof` which closes `sort_inv`'s `proofIrrel` case *given* it.
- **`RawDefEq.lean`** — the reference's three-place judgment, plus the erasure. §0 above.
- **`Stratified.lean`** — Carneiro's `⊢ₙ` alternation index (`unique.tex:10–15`) as one
  inductive with a `Bool` discriminator, all four of the reference's "n-provability basics",
  `≡₀ = syntactic equality` (`thm:0dinv`, the base case), and weakening + substitution at
  the index.

---

## 2. What is stated but open

`Injectivity.lean` has **six** sorried declarations. `IsDefEqU.forallE_inv` is derived
in-file and carries no `sorry` of its own.

| Statement | Blocked on |
|---|---|
| `IsDefEqU.sort_inv` | **two labelled holes inside the induction**: `trans` (normalisation) and `proofIrrel` (`SortUniq`). Nine of eleven cases close; `extra` is discharged by `DeclRules`. |
| `IsDefEqU.forallE_inv_stratified` | `trans`, plus `SortUniq` in its **structural** cases (`forallEDF`, `symm`) — its conclusion pairs a conversion at level `u` with a stratified typing at that same `u`, and nothing aligns them. |
| `IsDefEqU.sort_forallE_inv` | same family |
| `IsDefEqU.const_app_inv` | same family (untouched) |
| `IsDefEqU.const_forallE_inv` | **two labelled holes**, the same two as `sort_inv`. Eleven of thirteen cases close. |
| `IsDefEqU.const_sort_inv` | same; skeleton not written, identical modulo `instL_lhs_ne_sort` |

**Everything reduces to two primitives:** normalisation (the `trans` case) and universe
uniqueness (`SortUniq`). Given `SortUniq`, the whole family collapses to `trans` alone.

**`SortUniq` is the highest-value target in the tree** — four independent consumers: this
syntactic cone, `Theory/SetModel/`'s `LevelAssign.srt_sound`, any confluence development, and
`IsDefEq.uniq`. Nothing in the tree exhibits one.

---

## 3. Tried and failed, with the failing step

This is the expensive half. Each entry says where it broke.

- **Confluence via `ChurchRosser.lean`.** Structurally circular *as the file stands*: it
  imports `Injectivity` and its backbone rests on the `UniqueTyping` family. **Not circular
  in the mathematics** — see §0.
- **"Restrict the goal to sorts and the dependency goes away."** No. The dependency lives in
  `NormalEq`'s *definition* (shared type data across both sides), so it survives any
  restriction of the conclusion. Separately, the minimal strengthening that closes `trans` —
  `IsDefEqStrong Γ e₁ e₂ A → (e₁ ≫* .sort u → ∃ w, u ≈ w ∧ e₂ ≫* .sort w)` — is **not closed
  under its own induction**: its `appDF` case needs `f'` to reduce to a λ whenever `f` does,
  dragging in Π-shape.
- **"The uniqueness family evaporates at the stratified index."** Half true and the wrong
  half. The **83** retyping uses (`trans_l/r`, `transU_l/r`, `of_l/r`, `defeqU_l/r`) do
  evaporate — each is "move a conversion to a type" or "compose at different types", and at
  the index `trans`/`conv` are rules. The **26** `uniq`/`uniqU` uses do **not**; they become
  the *induction hypothesis* (`unique.tex:64` says so outright). *That relocation, not their
  disappearance, is what breaks the circularity.* The counterexample that catches the wrong
  version: `≡ₚ → ≡`'s app case still needs a shared function type.
- **The experimental shape model** (`Lean4Lean/Experimental/`) never supplied these. Treat
  everything there as unproved. `SExpr.ParamsExtra.extra_pat` is unsatisfiable as stated.
- **A set-model route** is blocked on the same two cases: `LevelAssign` needs universe
  uniqueness, which is strictly more than `sort_inv`.
- **`extra` was never the obstacle**, for any statement in the family. `DeclRules` closes it
  mechanically. Do not spend effort there.
- **Rule-freeness (`RuleFreeHead`) is weaker than it looks.** It discharges exactly the
  `extra` case, and only on the `lhs` side — the mirrored case needs
  `DeclRules.instL_lhs_ne_forallE`. Disjointness is in `sort_inv`'s equivalence class, not
  cheaper.

---

## 4. The estimate, and why it moved both ways

`thm:utype` at the index was estimated at **111 lines** (re-index `UniqueTyping.lean`'s
`IsDefEq.uniq`). It then moved to **3–4×**, then back to **~2.4×**. Both moves were on
evidence and the history is more informative than the number.

- **Up:** building into it surfaced two devices the estimate omitted — a substitution lemma
  at the index, and a core/conversion separation. The second was a *definition change*, not
  an addition, which is what made the route look structural.
- **Down, and this is the consequential part:** the **core/conversion separation is not
  needed**. `thm:utype`'s double induction can peel conversions on the second derivation with
  a nested induction under a subject-shape generalisation — exactly how
  `HasType.app_inv` (`Strong.lean`) inverts an application without one. `HasTypeStrong` has
  the separation for convenience. The definition-change item is struck.
- **Substitution + weakening came in at 116 lines, under the 120–200 estimated**, and it is
  the piece that *propagates*: all 35 of `ChurchRosser.lean`'s `instN`/`weakN`-using
  declarations draw on it. It is paid once, and it is paid.

A derived figure also corrected: §§3–4 was re-read as **3000–6000 lines** on the assumption
that the substrate cost recurs per declaration. **It does not.** Back to **1500–2500**.

Measured, not estimated, on `ChurchRosser.lean` with comments stripped: 86 declarations;
83 retyping uses; 26 `uniq`/`uniqU` uses; 52 `instN` and 73 `weakN` uses across 35
declarations.

---

## 5. Traps

All the same shape: **something that reads right, typechecks, and is wrong.** Five found in
one session. Structural instruments held (import graphs, arity checks, elaborated
references, fully qualified names); textual ones did not.

1. **Arity.** `forallE_inv` names two unrelated families. Of 44 textual hits in
   `ChurchRosser.lean` only **12** are the injectivity one; the other 30 are the
   one-argument family in `Typing/Lemmas.lean` (`HasType.forallE_inv`, `IsType.sort_inv` —
   the latter only says "the level is `WF U`"). A plain grep overcounts ~3.5×. An earlier
   report of "20+ sites" was inflated this way.
2. **Namespace collision.** `Lean4Lean.VEnv.Params` (`ChurchRosser.lean:12`, the mainline
   class, **no instance**) and `Lean4Lean.Params` (`Experimental/SExpr.lean:787`, different
   fields) are different classes. `Experimental/ParamsInstance.lean`'s `paramsOfWF`
   instantiates the **second**. Two contradictory-sounding claims in this repo are both true
   of different classes. **Standing rule: a claim about whether something is instantiated
   must carry its namespace, or it is not a claim.**
3. **Case-pattern implicits.** `Stratified.bvar` has one more implicit than `IsDefEq.bvar`
   (the index `n`), so the pattern `| @bvar _ i ty h =>` copied from the `IsDefEq.instN`
   template silently binds `h` to the *index* and leaves the `Lookup` inaccessible. It
   typechecks — `h : Nat` — and fails several inference steps later. **Copying a case pattern
   between two judgments requires counting implicits, not matching names.**
4. **Two head notions.** `VExpr.headConst?` **peels λ**; `VExpr.spineHead` (added in
   `Injectivity.lean`) does not. `headConst?` is right for `extra` (a rule's lhs is
   λ-abstracted) and *wrong* for `beta`, where the spine head is a `.lam` and `headConst?`
   looks straight through it.
5. **Index arithmetic.** `Stratified.instN`'s conclusion must be written `m + n`, never
   `n + m`. `Nat.add` recurses on its second argument, so only `m + (n+1)` reduces to
   `(m+n)+1` — which is what lets the conversion rules (all concluding at a successor)
   unify. `n + m` does not reduce and the proof does not go through.

**Standing warning, hit twice:** *wherever the reference relies on typing and conversion
being separate judgments, this tree needs a combined statement.* Root cause: `HasType e A` is
*defined* as `IsDefEq e e A`. Instances so far — (a) the type index makes `IsDefEqU`
composition a theorem not a rule (§0); (b) the reference's basics (3) and (4) cannot be two
lemmas here, because in `IsDefEqStrong` a conversion rule's typing premises are diagonal
instances of the conversion judgment itself, so a split induction has nothing to feed
`appDF`, `beta`, `eta` or `proofIrrel`. Expect more in §§3–4; reach for a combined statement
before proving two lemmas that cannot see each other's induction hypotheses.

---

## 6. One deviation from the reference — do not let this get absorbed

`Stratified`'s `rfl` is **unconditional**; the reference's reflexivity rule
(`axioms.tex:31`) requires `Γ ⊢ e : α`.

Why: it makes `≡₀` *exactly* syntactic equality, which is the reference's own stipulation for
level 0, and it repairs a genuine gap. Carneiro states monotonicity as "(2) follows from
(1)", but **at `m = 0` it does not**: `⊢₀ α ≡ β` is `α = β` with no typing content, while
`⊢₁ α ≡ β` through a typing-guarded `refl` would demand `Γ ⊢₀ α : γ`, which need not hold for
an ill-typed `α`. Unconditional `rfl` closes it and changes nothing about well-typed terms,
since `rfl` relates a term only to itself.

This is flagged in `Stratified.lean`'s module docstring as a deviation. Keep it flagged.

---

## 7. Where to pick up

1. **`thm:utype` at the index** (`unique.tex:40–53`). Needs: the `DefInv` predicate
   (`unique.tex:30–35`, three clauses); level-`n` congruence helpers — each needs an `n = 0`
   branch through `IsDefEqN.zero_iff`, because conversion rules live at `n+1` while
   `thm:utype`'s conclusion is at `n`; then the double induction, using
   `IsDefEqN.inst0` for the `app` case (already built). Do **not** add a core/conversion
   separation; nested induction under a subject-shape generalisation suffices (§4).
   Note the reference's `thm:utype` needs **no numeric measure** — the repo's 111-line
   `IsDefEq.uniq` is long only because it also manufactures stratified sort witnesses.
2. **A `VEnv.Params` analogue** — *check the namespace, there are two classes by that name*
   (trap 2). Its `pat_wf` is semantic and needs `forallE_inv`; at the index that stops being
   circular for the same reason `uniq` does.

The direction proved is the one the target needs: `sort_inv` follows from "definitional
inversion at every `n`" plus `IsDefEqU.stratifyN` alone. The converse
(`IsDefEqN n → IsDefEqU`) is the reference's regularity upgrade, needs `uniq`, and is **not**
required — do not spend effort on it before something asks.

**Useful prior traces** (this project has three times re-derived what it had already
answered): `docs/research-injectivity.md` §§2–3 maps `unique.tex` onto the repo
table-by-table; `docs/research-sort-inv.md` prices the alternatives;
`docs/research-forallE-inv.md` §9 explains the level-descent machinery in `Strong.lean`.
Grep `docs/` before deep-diving any dependency.
