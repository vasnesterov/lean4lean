import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.DeclRules

/-!
# Structural inversion principles we cannot prove yet

Six statements, in two families.

## Sorts and Π-types

`sort_inv`, `forallE_inv_stratified`, `forallE_inv`, `sort_forallE_inv` — the original four.
`forallE_inv` is *derived* from the stratified form here.

**Do not plan against `Experimental/Reflect/Capstone.lean`.**  An earlier version of this
docstring said Capstone "now proves `forallE_inv` directly, relative to a `Params`
instance", and that the arrow would reverse once an instance landed.  That route is closed:
the `Params`-style side condition its main result carries is *provably unsatisfiable*, so
everything it exports is vacuously true.  Its proof *shapes* are still worth reading —
`sort_uniq_of_hasType` and `forallE_inv_stratified_params` name the real obligations
correctly — but nothing there is available as a proof.  Treat every statement under
`Lean4Lean/Experimental/` as unproved regardless of how it reads.

## Constant applications — three different facts, and they are not interchangeable

`docs/design-inductive.md`'s ledger entry **I13 records only the first of these**, under the
name `const_forallE_inv`, while five consumers across two streams need the second or the
third.  Distinguishing them is the point of this section; see `docs/research-const-inv.md`
§1.

* **(A) Disjointness** — a rule-free constant application is not a Π, and is not a sort.
  `const_forallE_inv` and `const_sort_inv` below.  **Three independent consumers, found by
  three streams separately:** `pat_major_not_pi` (ledger I14); this file's own inversion
  targets; and the set model's block-freeness lemma, whose base cases are exactly these two.
  The sort half went unstated in this tree until the third consumer asked for it — a missing
  statement is worse than an open one, because an open one is visible in a `sorry` count and
  a missing one is invisible until someone needs it.
* **(B) Injectivity** — two applications of the *same* constant force their level and
  argument lists to agree.  `const_app_inv` below.  Consumers:
  `Verify/TypeChecker/WHNF.lean`'s `reduceRecursor.WF` quotient branch and its `Quot.ind`
  arm (both need `Quot α r ≡ Quot α' r' → α ≡ α'`), and `TrProj.uniq` / `TrProj.defeqDFC`
  (`Verify/Typing/Lemmas.lean`).
* **(C) Rigidity** — a term definitionally equal to a constant application reduces to one
  with the same head, so its components can be read back in the smaller context.  Consumer:
  `TrProj.weak'_inv` (`Verify/Typing/Lemmas.lean`, see the route traced in its docstring).
  **Deliberately not stated here.**  Its only faithful formulation mentions weak-head
  reduction, which lives in `Theory/Typing/HeadReduction.lean` — downstream of this file and
  gated on `Params`.  Writing a reduction-free approximation is how one gets a fourth wrong
  statement; it should be stated where the reduction relation is in scope.

### Why (B) carries two side conditions

Both are load-bearing, and **both are machine-checked in
`Theory/Typing/ConstInvWitness.lean`** — as regression tests, not prose, so that dropping
either one makes that file prove `False`.

* `RuleFreeHead` — without it, a constant whose value is a constant function identifies all
  its arguments (`w1`).  This is the condition the ledger already records.
* `IsType` on the application — without it, `IsDefEq.proofIrrel` identifies *any* two
  applications that land in a proposition, **with no reduction and with no rule in the
  environment at all** (`w2`).  `RuleFreeHead` does not repair this, which is why the
  ledger's single condition is not enough.

Both consumers' sites satisfy `IsType` for free: they use the fact at the *type* of a term.

A fourth fact — no-confusion between *distinct* rule-free constants — is not stated because
no consumer has asked for it; (B) is same-head only.
-/

namespace Lean4Lean

/-- The head constant of an application spine, under any number of leading lambdas.

Spelled out here rather than reusing `PatternDecode.lean`'s `peelLams`/`spine` so that this
file keeps a short import list; the λ-peeling matters because a rule with parameters stores
its left-hand side λ-abstracted (`Theory/Quot.lean`'s `quotDefEq`, `VInductDecl'.iotaRule`),
while a δ-rule's is the bare `.const c (VLevel.params _)`. -/
def VExpr.headConst? : VExpr → Option Lean.Name
  | .const c _ => some c
  | .app f _ => f.headConst?
  | .lam _ b => b.headConst?
  | _ => none

/-- The head of an application spine, **without** peeling λ — unlike `headConst?`, which
does.  `headConst?` is the right instrument for `extra` (a rule's lhs is λ-abstracted);
`spineHead` is the right one for `beta`, where the spine head is a `.lam` and `headConst?`
would look straight through it. -/
def VExpr.spineHead : VExpr → VExpr
  | .app f _ => VExpr.spineHead f
  | e => e

theorem VExpr.spineHead_mkApp : ∀ (as : List VExpr) (f : VExpr),
    VExpr.spineHead (f.mkApp as) = VExpr.spineHead f
  | [], _ => rfl
  | a :: as, f => VExpr.spineHead_mkApp as (.app f a)

theorem VExpr.headConst?_instL : ∀ (e : VExpr) (ls : List VLevel),
    (e.instL ls).headConst? = e.headConst?
  | .const _ _, _ | .bvar _, _ | .sort _, _ | .forallE _ _, _ => rfl
  | .app f _, ls => VExpr.headConst?_instL f ls
  | .lam _ b, ls => VExpr.headConst?_instL b ls

theorem VExpr.headConst?_mkApp : ∀ (as : List VExpr) (f : VExpr),
    (f.mkApp as).headConst? = f.headConst?
  | [], _ => rfl
  | a :: as, f => VExpr.headConst?_mkApp as (.app f a)

namespace VEnv

/-- `c` heads no definitional-equality rule of `env`.

For an environment built by declarations this holds of every inductive type former, every
constructor, and of `Quot` — the rules are δ-rules headed by a `def`'s name, ι-rules headed
by a recursor, and `quotDefEq` headed by `Quot.lift` (`Theory/Typing/PatternRules.lean`'s
`Pat`).  Deriving it from `VEnv.WF` is ledger item M2 and needs the `VEnv.Sig` invariant. -/
def RuleFreeHead (env : VEnv) (c : Lean.Name) : Prop :=
  ∀ df, env.defeqs df → VExpr.headConst? df.lhs ≠ some c

/-- **NOT PROVED.**  `sort_inv` is still `sorry`-backed; what has changed is that the
`sorry` is now *two labelled holes inside the induction* rather than one opaque hole, so
`#print axioms Lean4Lean.VEnv.IsDefEqU.sort_inv` still reports `sorryAx`.

The proof below is the induction on `IsDefEqStrong` written out.  Nine of its eleven cases
close; the two that remain are the whole residual content of `sort_inv`:

* **`trans`** — `Γ ⊢ .sort u ≡ e ≡ .sort v` with `e` arbitrary.  Closing it means knowing
  that a term convertible with a sort *reduces* to a sort: a confluence or normalisation
  statement.  Carneiro (`~/lean-type-theory/unique.tex` §Church–Rosser) breaks the loop by
  indexing conversion with the number of alternations against typing and re-running the
  whole κ-reduction development at each index; `HasTypeStratified` is **not** that index —
  its `defeq` premise carries a full, unstratified `IsDefEq`.

  **Is the circularity mathematical or merely architectural?**  `ChurchRosser.lean` imports
  this file, but that alone would only mean the general case is entangled.  Traced on the
  definitions — its proof bodies are not reliable, the file has live `sorry`s — the answer
  is **mathematical: a sort-only confluence is not independent.**

  - `ParRed` (`ChurchRosser.lean:566`) *is* layerable.  Its constructors carry no typing
    hypotheses at all; the one side condition, `extra`'s `r.2.OK (IsDefEqU …)`, needs only
    `Pattern`/`Pat` and `IsDefEqU`.  And the whole rule/reduction cone —
    `Theory/Typing/{Pattern, PatternDecode, DeltaUnique, PatternRules}.lean` — imports
    neither this file nor `UniqueTyping` (checked on the import graph, not by name search).
    So the reduction relation could be relocated below this file at no mathematical cost.
  - **`NormalEq` cannot.**  It is the relation that absorbs `proofIrrel` and `eta`, which a
    conversion `Γ ⊢ .sort u ≡ e` may use at any depth, so no sort-only development escapes
    it — and its constructors demand *shared* type data between the two sides:
    `appDF` (`:141`) asks for one `.forallE A B` typing **both** functions and one `A`
    typing both arguments; `lamDF` (`:147`) asks for one domain `A` and one level `u`.
    Composing two `NormalEq` facts whose type data came from different derivations — which
    is what `NormalEq.trans`, `ParRed.triangle` and `NormalEq.parRed` do, and they are the
    heart of the confluence argument — therefore requires reconciling two independently
    derived Π types.  That is `IsDefEqU.forallE_inv` together with `IsDefEq.uniq`, and one
    level of it is `VEnv.SortUniq`.
  - The same shows up if one tries to bypass `NormalEq` and strengthen this induction
    directly.  The statement that closes `trans` is
    `IsDefEqStrong Γ e₁ e₂ A → (e₁ ≫* .sort u → ∃ w, u ≈ w ∧ e₂ ≫* .sort w)` (plus its
    mirror).  It is *not closed under its own induction*: in the `appDF` case, `f a ≫* .sort u`
    propagates to `f' a'` only if `f'` reduces to a λ whenever `f` does, so the sort shape
    drags in the λ/Π shape — which is Π-injectivity.  Its `eta` case needs `.sort` / `.forallE`
    disjointness (`sort_forallE_inv`, below) and its `proofIrrel` case needs `SortUniq`.

  So this is a **joint development, not a layering fix**: sort-confluence, Π-injectivity and
  universe uniqueness are one induction — *in this tree*.  **They are not in the reference,
  and the difference is one definition.**  Carneiro's conversion judgment
  (`~/lean-type-theory/axioms.tex:30–41`) is **three-place**, `Γ ⊢ e ≡ e'`; of its eleven
  rules exactly one — application — mentions a type, and there `Γ ⊢ e ≡ e' : α` is stated
  at `:41` to *abbreviate* a conjunction.  `symm`, `trans`, and the λ and ∀ congruences
  carry no type.  `IsDefEq` here makes the type an *index*, so `trans` demands one `A` for
  both halves and `lamDF` one level and one codomain.  That is what makes composing
  `IsDefEqU` facts a theorem (`uniqU`) rather than a rule, which is what puts the
  `UniqueTyping` family in 23 backbone declarations, and what forces `NormalEq`'s
  constructors to carry shared type data where the reference's `≡ₚ` congruences
  (`unique.tex:113–118`) carry none.  **So the Π-injectivity dependency above is an
  artifact of this tree's port, not of the mathematics.**  The reference's proof never
  incurs it; `Theory/Typing/RawDefEq.lean` transcribes its judgment and erases into it
  (`IsDefEq.raw`, no injectivity, no unique typing — `defeqDF` erases to nothing).

  What is *not* missing: Carneiro's separated typing judgment is already here.
  `HasTypeStrong` and `HasTypeStratified` (`Strong.lean`) have **exactly one** constructor
  mentioning conversion — `defeq` — and `HasTypeStratified` already carries the index.  The
  single missing ingredient for `⊢_n` is that `defeq`'s conversion premise be drawn from a
  *stratified* conversion relation rather than from the full unstratified `IsDefEq`.  Two numbers for whoever prices it.  Of
  `ChurchRosser.lean`'s 85 declarations, 6 use `IsDefEqU.forallE_inv`/`sort_inv` directly
  and 23 use the `UniqueTyping` family (`uniq`, `uniqU`, `trans_l/r`, `of_l/r`,
  `defeqU_*`, `transU_*`) — and those 23 are the backbone: `NormalEq.{symm,trans,defeq,parRed}`,
  `ParRed.{defeq,triangle}`, `CRDefEq.{defeq,trans}`, `IsDefEq.church_rosser`.  And beware
  the name search: of 44 textual `forallE_inv` hits in that file only 12 are this one; the
  other 30 are the unrelated one-argument family in `Theory/Typing/Lemmas.lean`
  (`HasType.forallE_inv`, `IsType.forallE_inv`), which is available upstream.  Arity is the
  only thing that distinguishes them, and a plain grep overcounts by about 3.5×.

* **`proofIrrel`** — `Γ ⊢ p : .sort .zero`, `Γ ⊢ .sort u : p`, `Γ ⊢ .sort v : p`.
  Refuting the hypothesis means showing a sort is never a proof.  **This case is closed
  outright by `VEnv.sort_not_proof` (`Theory/Typing/SortUniq.lean`), given `VEnv.SortUniq` —
  universe uniqueness, `Γ ⊢ e : .sort u → Γ ⊢ e : .sort v → u ≈ v`.**  It is *not* closable
  without it: even the step that reads `p ≡ .sort u.succ` off the second premise fails,
  because its induction's `defeq` case holds the equation `A ≡ B` at the level the
  derivation chose and the inductive hypothesis at the level `A` was separately found to
  inhabit, and retyping either to the other is exactly universe uniqueness.  (An earlier
  version of this docstring called that step routine.  It is not; the residual goal is
  machine-witnessed in `HasTypeStrong.sort_type`, whose `huniq` argument is used precisely
  there.)  Carneiro gets universe uniqueness from unique typing *at the previous
  stratification index* (`unique.tex:266`); here nothing supplies it.

The other nine cases really are closed, and in particular:

* **`extra` is not the obstacle.**  It is discharged outright by
  `VEnv.WF.instL_lhs_ne_sort` (`Theory/Typing/DeclRules.lean`): in a `VEnv.WF` environment
  every definitional-equality rule is a δ-rule, the quotient rule, or an ι-rule, and none
  of those has a `.sort` left-hand side.  Recording that mechanically is half the point of
  writing this induction out.
* `beta`, `eta` and every congruence case are vacuous — their left endpoint is an `.app`,
  a `.lam`, a `.bvar`, a `.const` or a `.forallE`, never a `.sort`.

**Net reduction.**  Granted `VEnv.SortUniq`, every open statement in this file's Π/sort
family collapses to the single `trans` case above — i.e. to normalisation.  `SortUniq` is
itself open (nothing in the tree exhibits one), and `Theory/Typing/SortUniqFacts.lean`
checks that it is no stronger than this family, so the two are plausibly a single
obligation rather than two.  Note the stakes: these two cases also block
`Theory/SetModel/`, whose every result is parameterised by a `LevelAssign` that nobody has
constructed. -/
theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := by
  have aux : ∀ {Γ : List VExpr} {e1 e2 A : VExpr}, env.IsDefEqStrong U Γ e1 e2 A →
      ∀ u v : VLevel, e1 = .sort u → e2 = .sort v → u ≈ v := by
    intro Γ e1 e2 A H
    induction H with
    | sortDF _ _ h3 => rintro _ _ ⟨⟩ ⟨⟩; exact h3
    | symm _ ih => rintro u v rfl rfl; exact (ih _ _ rfl rfl).symm
    | defeqDF _ _ _ _ ih => exact ih
    | extra h1 => exact fun u _ h _ => absurd h (henv.instL_lhs_ne_sort h1 _ u)
    | trans _ _ ih1 ih2 =>
      -- OPEN: `Γ ⊢ .sort u ≡ e₂ ≡ .sort v`; needs `e₂` to reduce to a sort.
      rintro u v rfl rfl; sorry
    | proofIrrel h1 h2 h3 ih1 ih2 ih3 =>
      -- OPEN: `Γ ⊢ .sort u, .sort v : p` with `Γ ⊢ p : .sort .zero`; needs
      -- "a sort is not a proof".
      rintro u v rfl rfl; sorry
    | _ => rintro u v ⟨⟩ ⟨⟩
  obtain ⟨_, h1⟩ := h1
  exact aux (h1.strong henv.ordered hΓ) _ _ rfl rfl

/-- **NOT PROVED**, and — unlike `sort_inv` — *not* reducible to the conversion-derivation
content alone.  Attempting the same induction on `IsDefEqStrong` that `sort_inv` uses shows
this statement needs **two independent things**, only one of which `sort_inv` shares:

1. the `trans` content of `sort_inv` — normalisation (see its docstring), and
2. **universe uniqueness** — `Γ ⊢ e : .sort u → Γ ⊢ e : .sort v → u ≈ v`, packaged as
   `VEnv.SortUniq` in `Theory/Typing/SortUniq.lean`.

These are the same two primitives `sort_inv` needs, so the family really is one obligation
and not several.  What is different here is that (2) is needed by the *structural* cases,
not only by `proofIrrel`.

*The two bullets below are analysis of the induction, not a machine-checked impossibility;
the corresponding claim for `sort_inv`'s `proofIrrel` case is machine-witnessed, in
`HasTypeStrong.sort_type`.*  (2) is forced by the *shape* of the conclusion, not by any
particular proof strategy: each
conjunct pairs a conversion `A ≡ A'` (resp. `B ≡ B'`) *at a level* `u` with a
`HasTypeStratified` derivation of `A` (resp. `B`) *at that same level* `u` and *at the index
`n` inherited from the hypothesis `h2`*.  The conversion's level comes from the derivation
being inverted; the stratified derivation's level comes from `h2` via
`HasTypeStratified.forallE_inv'`; nothing upstream of this file aligns them.  Concretely,
even the two easiest cases fail:

* `forallEDF` — the structural case — hands back `Γ ⊢ A ≡ A' : .sort u` and
  `A::Γ ⊢ B ≡ B' : .sort v`, while `h2.forallE_inv'` hands back `Γ ⊢ A : .sort u₀ !! n-1`
  and `A::Γ ⊢ B : .sort v₀ !! n-1`.  Retyping either side at the other's level needs
  `u ≈ u₀` / `v ≈ v₀`.
* `symm` — goal 2 closes (its `B`-side components arrive already paired), but goal 1 needs
  `A`'s stratified derivation at index `n`, and the induction hypothesis supplies `A'`'s at
  index `n'`.

Bumping the index is free (`HasTypeStratified.mono`); aligning the *levels* is not.
`Theory/Typing/Lemmas.lean`'s `HasType.sort_inv` is only "the level is `WF U`", and there is
no universe-uniqueness lemma anywhere upstream: the one in the tree, `IsDefEq.uniq`
(`Theory/Typing/UniqueTyping.lean`), is this lemma's own consumer.  This is the same
"pinning" difficulty that `Experimental/Reflect/Capstone.lean:95–99` describes and that its
`sort_uniq_of_hasType` was built to supply — and that route is closed (see the module
docstring).

So `forallE_inv_stratified` is not provable by induction on the conversion derivation in
isolation.  Closing it needs either a joint induction with `IsDefEq.uniq`, or a route
(a model, or Carneiro's stratified Church–Rosser) that delivers universe uniqueness
independently.

Worth knowing before restating it: **both consumers discard the first conjunct's
`HasTypeStratified` component** — `IsDefEq.uniq` (`UniqueTyping.lean:43`) binds only the
second conjunct, and `forallE_inv` below takes only the `IsDefEq`.  Dropping it would
weaken the statement at no cost to anyone, but it does *not* unblock the proof: the second
conjunct needs exactly the same level alignment for `B`. -/
theorem IsDefEqU.forallE_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry

/-- **Π-injectivity, proved directly rather than through the stratified form.**  Still
`sorry`-backed, but the residual is now **exactly `sort_inv`'s two holes** — `trans` and
`proofIrrel` — and *nothing else*.  Nine of the eleven `IsDefEqStrong` cases close.

**This corrects `forallE_inv_stratified`'s docstring, which is about that statement and not
about this one.**  That docstring says Π-injectivity needs universe uniqueness *in the
structural cases*, `forallEDF` included.  It does — in the *stratified* formulation, whose
conclusion pairs each conversion with a `HasTypeStratified` derivation *at a level chosen by
a different derivation*; aligning those two levels is the universe-uniqueness demand.  The
plain statement carries no such conjunct, so `forallEDF` hands both halves back on the nose
and there is no level to align.  Both consumers of the stratified form already discard the
`HasTypeStratified` components (its own docstring says so); what was not noticed is that
discarding them removes the *obstruction*, not merely the payload.

**The one real difficulty is `symm`, and it is dissolved by strengthening the induction, not
by a new lemma.**  Inverting `.forallE A' B' ≡ .forallE A B` gives the codomain conversion in
context `A'::Γ`, while the goal wants it in `A::Γ` — a context conversion, which is exactly
what blocks `DefInv` clause (2) and `PropConvInv`'s `forallEDF` case elsewhere in the tree.
It is avoidable here: `IsDefEqStrong.forallEDF` carries the codomain conversion **in both
contexts** (`A::Γ ⊢ body ≡ body'` and `A'::Γ ⊢ body ≡ body'`, `Strong.lean:54–55`), so
carrying *both* through the induction makes `symm` close by `IsDefEq.symm` alone.  The extra
conjunct is discarded at the end.

So Π-injectivity is **not** a second obligation beyond `sort_inv`: granted a `trans` case
(normalisation) and "a Π is not a proof", it follows.  See `docs/handoff-injectivity.md`. -/
theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) := by
  have aux : ∀ {Γ : List VExpr} {e1 e2 T : VExpr}, env.IsDefEqStrong U Γ e1 e2 T →
      ∀ A B A' B', e1 = .forallE A B → e2 = .forallE A' B' →
        (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧
        ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧ env.IsDefEq U (A'::Γ) B B' (.sort u) := by
    intro Γ e1 e2 T H
    induction H with
    | forallEDF _ _ h3 h4 h5 =>
      rintro _ _ _ _ ⟨⟩ ⟨⟩
      exact ⟨⟨_, h3.defeq⟩, _, h4.defeq, h5.defeq⟩
    | symm _ ih =>
      rintro A B A' B' rfl rfl
      obtain ⟨⟨u, ha⟩, v, hb1, hb2⟩ := ih A' B' A B rfl rfl
      exact ⟨⟨u, ha.symm⟩, v, hb2.symm, hb1.symm⟩
    | defeqDF _ _ _ _ ih => exact ih
    | extra h1 => exact fun A B _ _ h _ => absurd h (henv.instL_lhs_ne_forallE h1 _ A B)
    | trans _ _ ih1 ih2 =>
      -- OPEN: `Γ ⊢ .forallE A B ≡ e₂ ≡ .forallE A' B'` with `e₂` arbitrary; needs `e₂` to
      -- reduce to a Π.  Identical in content to `sort_inv`'s `trans`.
      rintro A B A' B' rfl rfl; sorry
    | proofIrrel h1 h2 h3 ih1 ih2 ih3 =>
      -- OPEN: `Γ ⊢ .forallE A B, .forallE A' B' : p` with `Γ ⊢ p : .sort .zero`; needs
      -- "a Π is not a proof".  `sort_inv` needs the sort half of the same fact.
      rintro A B A' B' rfl rfl; sorry
    | _ => rintro A B A' B' ⟨⟩ ⟨⟩
  obtain ⟨_, h1⟩ := h1
  obtain ⟨ha, u, hb, -⟩ := aux (h1.strong henv.ordered hΓ) _ _ _ _ rfl rfl
  exact ⟨ha, u, hb⟩

/-- **(A) Disjointness, sort/Π half** — a sort is not a Π.

Written out as the same induction as `sort_inv` and `const_forallE_inv`, for the same reason:
nine of the eleven `IsDefEqStrong` cases close outright, and what is left is the *same two*
labelled holes — `trans` and `proofIrrel`.  Machine-checking that reduction is the point.
Before this, the statement was one opaque `sorry` and the claim that it lives in the same
family as `sort_inv` was prose.

* `extra` closes from `VEnv.WF.instL_lhs_ne_sort` **and** `VEnv.WF.instL_lhs_ne_forallE`
  (`Theory/Typing/DeclRules.lean`): no rule's left-hand side is a sort, and none is a Π.
* every remaining structural case is vacuous on the *shape* of one endpoint.
* `trans` — the arbitrary middle term, exactly `sort_inv`'s hole.
* `proofIrrel` — needs "a sort is not a proof" *or* "a Π is not a proof"; either suffices,
  and the first is `VEnv.sort_not_proof` given `VEnv.SortUniq`.  So this statement's
  `proofIrrel` residual is **not a new obligation**: it is a strictly weaker demand than
  `sort_inv`'s, which needs the sort half specifically. -/
theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      ∀ (u : VLevel) (A B : VExpr),
        (e₁ = .sort u ∧ e₂ = .forallE A B) ∨ (e₂ = .sort u ∧ e₁ = .forallE A B) → False := by
    intro Γ e₁ e₂ T H
    induction H with
    | symm _ ih => exact fun u A B h => ih u A B h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans _ _ ih1 ih2 =>
      -- OPEN: the middle term is arbitrary.  Same hole as `sort_inv`'s `trans`.
      intro u A B h; sorry
    | proofIrrel _ _ _ ih1 ih2 ih3 =>
      -- OPEN: needs "a sort is not a proof" (or "a Π is not a proof"); either closes it.
      intro u A B h; sorry
    | extra h1 =>
      rintro u A B (⟨he, -⟩ | ⟨-, he⟩)
      · exact henv.instL_lhs_ne_sort h1 _ _ he
      · exact henv.instL_lhs_ne_forallE h1 _ _ _ he
    | sortDF _ _ _ => rintro u A B (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | forallEDF _ _ _ _ _ => rintro u A B (⟨hf, -⟩ | ⟨hf, -⟩) <;> exact absurd hf nofun
    | bvar _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro u A B (⟨hf, -⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
  exact fun ⟨_, h⟩ => aux (h.strong henv.ordered hΓ) u A B (.inl ⟨rfl, rfl⟩)

/-- **(B) Injectivity of a constant application.**  See the module docstring for why both
side conditions are needed, and `Theory/Typing/ConstInvWitness.lean` for the machine-checked
witness against each. -/
theorem IsDefEqU.const_app_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls ls' : List VLevel} {as as' : List VExpr}
    (hrigid : RuleFreeHead env c)
    (hty : env.IsType U Γ ((VExpr.const c ls).mkApp as))
    (h : env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) ((VExpr.const c ls').mkApp as')) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) as as' := sorry

/-- **(A) Disjointness** — ledger item I13, and the only one of the three the ledger records.
Consumed by `pat_major_not_pi` (I14).  Needs no `IsType` side condition: `proofIrrel` cannot
identify a term with a Π, because a Π is a type. -/
theorem IsDefEqU.const_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr}
    (hrigid : RuleFreeHead env c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.forallE A B) := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      ∀ (ls : List VLevel) (as A B : _),
        (e₁ = (VExpr.const c ls).mkApp as ∧ e₂ = .forallE A B) ∨
        (e₂ = (VExpr.const c ls).mkApp as ∧ e₁ = .forallE A B) → False := by
    intro Γ e₁ e₂ T H
    induction H with
    | symm _ ih => exact fun ls as A B h => ih ls as A B h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans _ _ ih1 ih2 =>
      -- OPEN: the middle term is arbitrary.  Same hole as `sort_inv`'s `trans`.
      intro ls as A B h; sorry
    | proofIrrel _ _ _ ih1 ih2 ih3 =>
      -- OPEN: needs "a Π is not a proof" — `VEnv.SortUniq`, exactly as `sort_inv` does.
      intro ls as A B h; sorry
    | extra h1 h2 h3 =>
      rintro ls as A B (⟨he, -⟩ | ⟨-, hf⟩)
      · exact hrigid _ h1 (by rw [← VExpr.headConst?_instL, he, VExpr.headConst?_mkApp]; rfl)
      · exact henv.instL_lhs_ne_forallE h1 _ _ _ hf
    | beta _ _ _ _ _ _ _ _ =>
      rintro ls as A B (⟨he, -⟩ | ⟨-, hf⟩)
      · have hs := congrArg VExpr.spineHead he
        rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun
      · exact absurd hf nofun
    | eta _ _ _ _ _ _ _ _ =>
      rintro ls as A B (⟨he, -⟩ | ⟨-, hf⟩)
      · have hs := congrArg VExpr.spineHead he
        rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun
      · exact absurd hf nofun
    | forallEDF _ _ _ _ _ =>
      rintro ls as A B (⟨he, -⟩ | ⟨he, -⟩) <;>
        (have hs := congrArg VExpr.spineHead he
         rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun)
    | bvar _ _ _ | sortDF _ _ _ | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _
    | lamDF _ _ _ _ _ _ _ =>
      rintro ls as A B (⟨_, hf⟩ | ⟨_, hf⟩) <;> exact absurd hf nofun
  exact fun ⟨_, h⟩ => aux (h.strong henv.ordered hΓ) ls as A B (.inl ⟨rfl, rfl⟩)

/-- **(A) Disjointness, sort half** — a rule-free constant application is not a sort.

Stated for the same reason `const_forallE_inv` is, and with the same side condition and the
same absence of an `IsType` one: `proofIrrel` cannot identify a constant application with a
sort, because that would make a sort a proof, which `VEnv.sort_not_proof`
(`Theory/Typing/SortUniq.lean`) refutes given `VEnv.SortUniq`.

**This statement did not exist in the tree until its third consumer asked for it.**  It is
needed by the set model's block-freeness lemma at the same base case that needs
`const_forallE_inv`, and nothing had ever written it down.  It is `sorry` like its sibling;
the point of stating it is that the next consumer finds a statement rather than a gap. -/
theorem IsDefEqU.const_sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel}
    (hrigid : RuleFreeHead env c) :
    ¬ env.IsDefEqU U Γ ((VExpr.const c ls).mkApp as) (.sort u) := by
  have aux : ∀ {Γ : List VExpr} {e₁ e₂ T : VExpr}, env.IsDefEqStrong U Γ e₁ e₂ T →
      ∀ (ls : List VLevel) (as : List VExpr) (u : VLevel),
        (e₁ = (VExpr.const c ls).mkApp as ∧ e₂ = .sort u) ∨
        (e₂ = (VExpr.const c ls).mkApp as ∧ e₁ = .sort u) → False := by
    intro Γ e₁ e₂ T H
    induction H with
    | symm _ ih => exact fun ls as u h => ih ls as u h.symm
    | defeqDF _ _ _ _ ih => exact ih
    | trans _ _ ih1 ih2 =>
      -- OPEN: the middle term is arbitrary.  Same hole as `sort_inv`'s `trans`.
      intro ls as u h; sorry
    | proofIrrel _ _ _ ih1 ih2 ih3 =>
      -- OPEN: needs "a sort is not a proof" — `VEnv.SortUniq`, exactly as `sort_inv` does.
      intro ls as u h; sorry
    | extra h1 =>
      rintro ls as u (⟨he, -⟩ | ⟨-, he⟩)
      · exact hrigid _ h1 (by rw [← VExpr.headConst?_instL, he, VExpr.headConst?_mkApp]; rfl)
      · exact henv.instL_lhs_ne_sort h1 _ _ he
    | constDF _ _ _ _ _ _ _ _ | appDF _ _ _ _ _ _ _ | lamDF _ _ _ _ _ _ _ =>
      rintro ls as u (⟨-, hf⟩ | ⟨-, hf⟩) <;> exact absurd hf nofun
    | sortDF _ _ _ | bvar _ _ _ =>
      rintro ls as u (⟨he, -⟩ | ⟨he, -⟩) <;>
        (have hs := congrArg VExpr.spineHead he
         rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun)
    | forallEDF _ _ _ _ _ | beta _ _ _ _ _ _ _ _ | eta _ _ _ _ _ _ _ _ =>
      rintro ls as u (⟨he, -⟩ | ⟨-, hf⟩)
      · have hs := congrArg VExpr.spineHead he
        rw [VExpr.spineHead_mkApp] at hs; exact absurd hs nofun
      · exact absurd hf nofun
  exact fun ⟨_, h⟩ => aux (h.strong henv.ordered hΓ) ls as u (.inl ⟨rfl, rfl⟩)
