import Lean4Lean.Verify.Inductive.B6

/-!
# `UserBlockR`: `CtorStoresTr` at the **user's own declaration**, at the real restoration

`Verify/Inductive/B6.lean` reached `CtorStoresTr env Us ntreeRTypes ntreeAux ntreeAux.idRestore`:
the *post-elimination* block against *its own* identity restoration.  `docs/handoff-b6.md`
("What remains of Claim B", item 1) asked for the other end — the per-constructor equation at the
**user's** stored constructor type, and its chaining with B6 part 3 so that `CtorStoresTr` holds
at `ntreeSurf` and `ntreeRestore` rather than at `ntreeRTypes` and `idRestore`.  This file is that,
in four layers.

## §1 The general theorem: `ctorTr?` left-inverts reification

A `rfl` at one constructor is not a theorem, so the content is put where it generalises.  There is
no `VExpr → Expr` map anywhere in the tree — the one constant whose type looks like one,
`Meta.instToExprVExpr.toExpr` (`Theory/Meta.lean`), is the **quoting** map (`VExpr.app f a` ↦ the
`Expr` *syntax tree* of that value), which is the opposite job — so §1 builds it: `VLevel.toLevel`,
`VExpr.toExpr`, and

  `VExpr.ctorTr?_toExpr : Us.Nodup → v.lvlWF Us.length →
      ctorTr? Γc Us (v.toExpr Us) Γ = some p → p.1 = v`

**No typing side conditions appear in the conclusion**, and none are assumed: success of `ctorTr?`
already carries them (`ctorTr?_sound`).  Levels are unrestricted — `zero`/`max`/`imax` are in, not
only `param`/`succ`.  The two frictions are both discharged by named lemmas rather than by hand:
the `.bvar` clause by `bvarCtx_find?` (which already says the translation *is* the de Bruijn index,
with no hypothesis on the context), and the level round-trip by `List.Nodup.idxOf_getElem`.

## §2 The bridge: binder annotations, and why the general theorem does not reach the user's type
by itself

`toExpr` has to *choose* binder names and `BinderInfo`s, and it writes `` `x `` and
`BinderInfo.default` everywhere.  Lean's stored type for `NTree.node` writes `` `α ``, `` `a ``, and
`BinderInfo.implicit` on the parameter.  So `exprOf% NTree.node` is **not** syntactically
`(ntreeNode.typeR ntreeAux ntreeRestore 0).toExpr [`u]`, and §1 alone would never have reached the
concrete case.  §2 is the repair, and it is one function and one lemma: `stripBinderData`
(binder names ↦ `` `x ``, `BinderInfo`s ↦ `.default`, `mdata` dropped) and
`ctorTr?_stripBinderData`, which says `ctorTr?` cannot see the difference — as it cannot, since its
`.forallE _ d b _` clause discards both fields and its `.mdata` clause is a pass-through.

That also retires the `mdata` worry **structurally** rather than by inspection of one example.

## §3 The user's block as an instance

`user_is_reification`, by `rfl`:

  `stripBinderData (exprOf% NTree.node) = (ntreeNode.typeR ntreeAux ntreeRestore 0).toExpr [`u]`

*Lean's own stored type for `NTree.node` is the reification of the abstract constructor type at the
real restoration, up to binder annotations.*  That is the sentence this file is for.  The remaining
content of the per-constructor equation is then §1, general.

## §4 The chaining, and what identifies the contracted form

`ntreeΓcU` widens B6's `ntreeΓc` by `List` — B6's table holds only `NTree` and `_nested.List_1`,
and the *user's* constructor type mentions `List`, which the post-elimination one does not.
`List`'s entry `⟨1, ∀ (α : Type u), Type u⟩` is **forced, not chosen**: the `.app` clause's
`AB.1 = q.2` check at `List (NTree α)` compares `List`'s instantiated domain against the inferred
type of `NTree α`, which is `.sort (.succ (.param 0))`.  Then `ntreeAux` is exhibited in
`setRecArgsD` form (`ntreeAux_setRecArgsD`, by `rfl`, so part 3's wrapper is **not** cosmetic and
does not have to be routed around) and `ctorStoresTr_of_ctorTr_setRecArgs constLookupU` gives

  `chain : CtorStoresTr ntreeEnvU [`u] [ntreeSurf] ntreeAux ntreeRestore`

on the user's one-member declaration.  `CtorStoresTr` quantifies over `j` with *both*
`rtypes[j]? = some t` and `D.types[j]? = some T`, so the one-member user list against the two-member
abstract block leaves `j = 1` with no obligation — which is why a `CtorStoresTr` at the user's block
is even statable.

## `noLam_of_ctorTr` is cited nowhere here, and cannot be — a correction

The brief this file was written from claimed the equation closes because "a `.lam`-free output
cannot be a β-redex, so `ctorTr?` produces the contracted form".  **That is not the mechanism, and
`noLam_of_ctorTr` is cited nowhere in this file** — not in the concrete equation, not in the
chaining, and not in §1's general left-inverse either.  It cannot be: `noLam_of_ctorTr` constrains
the **output** (`p.1.noLam`), and §1's `.lam` case has to refute the **input** — `ctorTr?` has no
`.lam` clause at all, so it returns `none` outright.  Knowing the output is `.lam`-free tells you
nothing until you already know what the output is.  **Exclusion is not identification.**

What identifies the contracted `List (NTree α)` is a fact about the *input*: Lean's stored `Expr`
for `NTree.node` **already is** contracted (no `.lam` anywhere), and `ctorTr?` is a structural
recursion with no β-reduction and no contraction step.  `noLam_of_ctorTr` remains a real theorem
doing real work in B6 §4 (the two-stage reader collapse); it is simply not what closes this
equation.

## §5 The control

`ntreeNodeRedexE` is the user's constructor type written with the β-redex
`(fun α => List (NTree α)) α` — the very term `ntreeNode_substC_ne_typeR`
(`Theory/Typing/ConstSubstNested.lean`) says `VExpr.substC` of the auxiliary type would give.  On it
`ctorTr?` returns **`none` outright**, for every table and every level list, because there is no
`.lam` clause.  That is the one place `noLam`'s *content* is genuinely visible here — and it is a
control, not the main proof.

Every lookup premise is discharged at a concrete environment (`constLookupU`, `constLookupU_staged`);
no conjunct of the witness is an implication with an unexhibited antecedent.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 Reification, and the left-inverse theorem

### §1.1 Levels -/

/-- `VLevel → Lean.Level`, the evident structural map back.  `.param i` becomes the *name*
`Us[i]`, which is what `VLevel.ofLevel`'s `.param` clause reads with `List.idxOf`. -/
def VLevel.toLevel (Us : List Name) : VLevel → Lean.Level
  | .zero => .zero
  | .succ u => .succ (u.toLevel Us)
  | .max u v => .max (u.toLevel Us) (v.toLevel Us)
  | .imax u v => .imax (u.toLevel Us) (v.toLevel Us)
  | .param i => .param (Us.getD i .anonymous)

/-- **The level round-trip.**  `Us.Nodup` is what makes `List.idxOf` invert `getElem`, and
`u.WF Us.length` is what puts the index in range; neither is slack. -/
theorem VLevel.ofLevel_toLevel {Us : List Name} (hUs : Us.Nodup) :
    ∀ {u : VLevel}, u.WF Us.length → ofLevel Us (u.toLevel Us) = some u
  | .zero, _ => rfl
  | .succ u, h => by
    simp [toLevel, ofLevel, bind, ofLevel_toLevel hUs (u := u) h]
  | .max u v, h => by
    simp [toLevel, ofLevel, bind, ofLevel_toLevel hUs (u := u) h.1,
      ofLevel_toLevel hUs (u := v) h.2]
  | .imax u v, h => by
    simp [toLevel, ofLevel, bind, ofLevel_toLevel hUs (u := u) h.1,
      ofLevel_toLevel hUs (u := v) h.2]
  | .param i, h => by
    have hi : i < Us.length := h
    rw [toLevel, ← List.getElem_eq_getD (h := hi)]
    simp [ofLevel, hUs.idxOf_getElem i hi, hi]

/-- The list form, for `ctorTr?`'s `.const` clause. -/
theorem VLevel.mapM_ofLevel_toLevel {Us : List Name} (hUs : Us.Nodup) :
    ∀ {us : List VLevel}, (∀ u ∈ us, u.WF Us.length) →
      (us.map (·.toLevel Us)).mapM (ofLevel Us) = some us
  | [], _ => rfl
  | u :: us, h => by
    have h1 := ofLevel_toLevel hUs (h u (.head _))
    have h2 := mapM_ofLevel_toLevel hUs fun a ha => h a (.tail _ ha)
    simp [List.mapM_cons, bind, h1, h2]

/-! ### §1.2 Expressions

`toExpr` must *choose* binder names and `BinderInfo`s — `Expr.forallE` carries both and `VExpr`
carries neither.  It writes `` `x `` and `BinderInfo.default`; §2 is the lemma that says `ctorTr?`
cannot see that choice. -/

/-- `VExpr → Expr`, the evident structural map back.  Total, and defined on `.lam` as well — the
`.lam` clause is not needed by anything below, but leaving it out would make the definition a
statement about the fragment rather than a plain reification. -/
def VExpr.toExpr (Us : List Name) : VExpr → Expr
  | .bvar i => .bvar i
  | .sort u => .sort (u.toLevel Us)
  | .const c us => .const c (us.map (·.toLevel Us))
  | .app f a => .app (f.toExpr Us) (a.toExpr Us)
  | .lam A b => .lam `x (A.toExpr Us) (b.toExpr Us) .default
  | .forallE A b => .forallE `x (A.toExpr Us) (b.toExpr Us) .default

/-- Every level parameter index occurring in the term is `< n`.  This is the *only* side condition
`ctorTr?_toExpr` needs, and it is about levels alone: nothing about typing, nothing about the
context, nothing about the constant table. -/
def VExpr.lvlWF (n : Nat) : VExpr → Prop
  | .bvar _ => True
  | .sort u => u.WF n
  | .const _ us => ∀ u ∈ us, u.WF n
  | .app f a => f.lvlWF n ∧ a.lvlWF n
  | .lam A b => A.lvlWF n ∧ b.lvlWF n
  | .forallE A b => A.lvlWF n ∧ b.lvlWF n

/-- …and it is decidable, so at a concrete block the side condition is discharged by `decide`
rather than by hand. -/
instance VExpr.decidable_lvlWF (n : Nat) : ∀ {v : VExpr}, Decidable (v.lvlWF n)
  | .bvar _ => instDecidableTrue
  | .sort _ => VLevel.decidable_WF
  | .const _ _ => List.decidableBAll _ _
  | .app _ _ | .lam _ _ | .forallE _ _ =>
    @instDecidableAnd _ _ (decidable_lvlWF n) (decidable_lvlWF n)

/-- **§1's THEOREM — `ctorTr?` left-inverts reification on its first component.**

If the inferencer succeeds on the reification of `v`, its translation *is* `v`, in **any** context
`Γ` and at **any** table `Γc`.  Note what is absent from both sides: no `TrExprS`, no `HasType`, no
`ConstLookup`, no `VEnv` at all.  Success of `ctorTr?` already carries the typing content
(`ctorTr?_sound` produces it), so a left-inverse statement needs none of it as a hypothesis.

The `.lam` case is where the brief's reading of the argument fails and is corrected: it is closed by
`ctorTr?` having **no `.lam` clause** — the input is refuted — and *not* by `noLam_of_ctorTr`, which
is about the output.  See the module docstring. -/
theorem VExpr.ctorTr?_toExpr {Γc : Name → Option VConstant} {Us : List Name} (hUs : Us.Nodup) :
    ∀ {v : VExpr}, v.lvlWF Us.length →
      ∀ {Γ : List VExpr} {p : VExpr × VExpr}, ctorTr? Γc Us (v.toExpr Us) Γ = some p → p.1 = v
  | .bvar i, _, Γ, p, h => by
    rw [toExpr, show ctorTr? Γc Us (.bvar i) Γ = (bvarCtx Γ).find? (.inl i) from rfl] at h
    exact (bvarCtx_find? (e := p.1) (A := p.2) (by rw [h])).1
  | .sort u, hv, Γ, p, h => by
    rw [toExpr, show ctorTr? Γc Us (.sort (u.toLevel Us)) Γ
      = (VLevel.ofLevel Us (u.toLevel Us)).map fun u' => (.sort u', .sort (.succ u')) from rfl,
      VLevel.ofLevel_toLevel hUs hv] at h
    cases h; rfl
  | .const c us, hv, Γ, p, h => by
    rw [toExpr] at h
    simp only [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨ci, _, us', hus, h⟩ := h
    rw [VLevel.mapM_ofLevel_toLevel hUs hv] at hus
    cases hus
    split at h
    · cases h; rfl
    · exact absurd h (by simp)
  | .app f a, hv, Γ, p, h => by
    rw [toExpr] at h
    simp only [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨p₁, h₁, q₁, h₂, AB, _, h⟩ := h
    split at h
    · cases h
      rw [ctorTr?_toExpr hUs hv.1 h₁, ctorTr?_toExpr hUs hv.2 h₂]
    · exact absurd h (by simp)
  | .forallE A b, hv, Γ, p, h => by
    rw [toExpr] at h
    simp only [ctorTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p₁, h₁, u, _, q₁, h₂, v, _, h⟩ := h
    cases h
    rw [ctorTr?_toExpr hUs hv.1 h₁, ctorTr?_toExpr hUs hv.2 h₂]
  | .lam A b, _, Γ, p, h => by
    -- `ctorTr?` has **no `.lam` clause**: the *input* is refuted.  `noLam_of_ctorTr` is useless
    -- here — it constrains the output, and we do not yet know what the output is.
    rw [toExpr] at h; simp [ctorTr?] at h

/-! ## §2 The binder-annotation bridge

`toExpr` writes `` `x ``/`BinderInfo.default` at every binder and emits no `mdata`.  Lean's stored
constructor types write real binder names, real `BinderInfo`s, and may carry `mdata`.  So §1 does not
reach a stored type by itself.  The gap is exactly the data `ctorTr?` discards, and this is the
lemma that says so. -/

/-- Normalise away everything `ctorTr?` cannot read: binder names become `` `x ``, `BinderInfo`s
become `.default`, `mdata` is dropped.  Everything else is untouched — in particular **no
β-reduction and no zeta**, so this is not a normaliser in any other sense. -/
def stripBinderData : Expr → Expr
  | .app f a => .app (stripBinderData f) (stripBinderData a)
  | .lam _ d b _ => .lam `x (stripBinderData d) (stripBinderData b) .default
  | .forallE _ d b _ => .forallE `x (stripBinderData d) (stripBinderData b) .default
  | .mdata _ e => stripBinderData e
  | e => e

/-- **The bridge.**  `ctorTr?` is blind to binder annotations and to `mdata`, as an equation and for
every `Γc`, `Us`, `Γ`.  Its `.forallE _ d b _` clause discards the name and the `BinderInfo`; its
`.mdata` clause is a pass-through.  This retires the `mdata` worry *structurally* rather than by
inspecting one example and finding none. -/
theorem ctorTr?_stripBinderData {Γc : Name → Option VConstant} {Us : List Name} :
    ∀ {e : Expr} {Γ : List VExpr}, ctorTr? Γc Us (stripBinderData e) Γ = ctorTr? Γc Us e Γ
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _
  | .lit _, _ | .proj _ _ _, _ => rfl
  | .letE .., _ => rfl
  | .app f a, Γ => by
    rw [stripBinderData]
    simp only [ctorTr?, ctorTr?_stripBinderData (e := f), ctorTr?_stripBinderData (e := a)]
  | .lam .., _ => by rw [stripBinderData]; simp [ctorTr?]
  | .forallE _ d b _, Γ => by
    rw [stripBinderData]
    simp only [ctorTr?, ctorTr?_stripBinderData (e := d)]
    cases ctorTr? Γc Us d Γ with
    | none => rfl
    | some p =>
      simp only [Option.bind_some]
      cases sortOf? p.2 with
      | none => rfl
      | some u => simp only [Option.bind_some, ctorTr?_stripBinderData (e := b)]
  | .mdata _ e, Γ => by rw [stripBinderData, ctorTr?_stripBinderData (e := e)]; rfl

/-! ## §3 The user's block

`ntreeSurf` (`Verify/Inductive/CtorsLenGeneral.lean`) is the **user's** declaration — `type :=
exprOf% NTree`, one constructor `type := exprOf% NTree.node`, both spliced out of the compiled
environment, never transcribed.  It is already inside this file's closure, so no new surface artefact
had to be written for this round. -/

namespace InductiveDeclExamples

/-! ### §3.1 The widened table, and why `List`'s entry is forced

B6's `ntreeΓc` holds exactly `NTree` and `_nested.List_1`.  The **user's** constructor type mentions
`List`, which the post-elimination one does not, so the table has to be widened. -/

/-- The three constants the user's block needs, at `uvars = 1` and stored type
`∀ (α : Type u), Type u`.

`List`'s entry is **forced, not chosen**.  `ctorTr?`'s `.app` clause checks `AB.1 = q.2`: at
`List (NTree α)` it compares `List`'s instantiated domain against the *inferred* type of `NTree α`,
which on this fragment is read off as `.sort (.succ (.param 0))`.  Any other domain and the check
fails and the inferencer returns `none`.  `_nested.List_1` is kept for continuity with B6 (nothing
below reads it, since the user's type does not mention it). -/
def ntreeΓcU : Name → Option VConstant := fun n =>
  if n = ``NTree ∨ n = ``List ∨ n = `_nested.List_1 then
    some { uvars := 1, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))) }
  else none

/-- …and an environment holding exactly it. -/
def ntreeEnvU : VEnv where
  constants := ntreeΓcU
  defeqs _ := False

/-- **The lookup premise, discharged.**  P7's prediction: `fun _ _ h => h` again. -/
theorem constLookupU : ConstLookup ntreeΓcU ntreeEnvU := fun _ _ h => h

/-- …and at every *staged* environment, through `FlipWiring.lean`'s named lemma: every table entry
is already in the pre-block environment, so the block half of the split is never needed. -/
theorem constLookupU_staged {K : List Name} :
    ∀ env₁, ntreeEnvU.addIndTypesC ntreeAux K = some env₁ → ConstLookup ntreeΓcU env₁ :=
  constLookup_staged_of_split fun _ _ hc => .inr hc

/-! ### §3.2 The per-constructor equation, at the user's stored type -/

/-- **THE EQUATION.**  The inferencer, run on Lean's own stored type for `NTree.node`, produces the
abstract constructor type restored at `ntreeRestore` — the *real* restoration, not `idRestore`. -/
theorem ntreeNode_ctorTr?_typeR :
    ∃ t', ctorTr? ntreeΓcU [`u] (exprOf% NTree.node) []
      = some (ntreeNode.typeR ntreeAux ntreeRestore 0, t') := ⟨_, rfl⟩

/-- …and equivalently against `vconst(type_of% @NTree.node)`, i.e. against what `Meta.ofExpr` makes
of the same stored type.  The two agree because `ctorTr?` and `Meta.ofExpr` are the **same
structural recursion** on the fragment `sort/bvar/const/app/forallE/mdata`; `ctorTr?` adds side
conditions but no rewriting — it never β-reduces and never contracts. -/
theorem ntreeNode_ctorTr?_declared :
    ∃ t', ctorTr? ntreeΓcU [`u] (exprOf% NTree.node) []
      = some ((vconst(type_of% @NTree.node)).type, t') := ⟨_, rfl⟩

/-! ### §3.3 …and it is an *instance* of §1, not a parallel `rfl`

This is the sentence the file is for. -/

/-- **Lean's own stored type for `NTree.node` IS the reification of the abstract constructor type at
the real restoration**, up to binder annotations — `toExpr` writes `` `x ``/`.default`, Lean stores
`` `α ``, `` `a `` and `BinderInfo.implicit` on the parameter, and `stripBinderData` is exactly the
difference.  By `rfl`. -/
theorem user_is_reification :
    stripBinderData (exprOf% NTree.node)
      = (ntreeNode.typeR ntreeAux ntreeRestore 0).toExpr [`u] := rfl

/-- …so the equation of §3.2 is a **corollary of §1**, with the block-specific input reduced to
`user_is_reification` and a `lvlWF` check.  Same statement as `ntreeNode_ctorTr?_typeR`, proved
generally. -/
theorem ntreeNode_ctorTr?_typeR_of_general {p : VExpr × VExpr}
    (h : ctorTr? ntreeΓcU [`u] (exprOf% NTree.node) [] = some p) :
    p.1 = ntreeNode.typeR ntreeAux ntreeRestore 0 :=
  VExpr.ctorTr?_toExpr (Γc := ntreeΓcU) (Us := [`u]) (by decide)
    (v := ntreeNode.typeR ntreeAux ntreeRestore 0) (by decide) (Γ := []) (p := p)
    (by rw [← user_is_reification, ctorTr?_stripBinderData]; exact h)

/-! ### §3.4 The chaining with B6 part 3

`ctorStoresTr_of_ctorTr_setRecArgs` (B6 part 3, arity 9, `{R : VIndRestore}` free) concludes at
`H.setRecArgsD D`, and `ntreeAux` is a hand-written structure literal.  P4 asked whether that wrapper
has to be routed around.  It does not. -/

/-- **`ntreeAux` IS exhibited in `setRecArgsD` form**, by `rfl` — so part 3's wrapper is not
cosmetic, and `ctorStoresTr_of_ctorTr_setRecArgs` applies to the block Lean's nested elimination
actually produces without any detour through `ctorStoresTr_of_ctorTr`. -/
theorem ntreeAux_setRecArgsD :
    (surfHeader 1 [.sort (.succ (.param 0))] ntreeRTypes).setRecArgsD (eraseRecArgs ntreeAux)
      = ntreeAux := rfl

/-- **THE HEADLINE.**  `CtorStoresTr` at the **user's own declaration** `[ntreeSurf]` and at the
**real** restoration `ntreeRestore` — not at `ntreeRTypes`, not at `idRestore`.

Reached through B6 part 3 with the one per-constructor input being §3.2's equation.  Note why this is
even statable: `CtorStoresTr` quantifies over `j` with *both* `rtypes[j]? = some t` **and**
`D.types[j]? = some T`, so the one-member user list against the two-member abstract block leaves
`j = 1` with no obligation at all. -/
theorem chain : CtorStoresTr ntreeEnvU [`u] [ntreeSurf] ntreeAux ntreeRestore := by
  rw [← ntreeAux_setRecArgsD]
  refine ctorStoresTr_of_ctorTr_setRecArgs constLookupU ?_
  intro j t T hj hT q c C hc hC
  match j, hj with
  | 0, hj =>
    cases hj
    cases hT
    match q, hc with
    | 0, hc => cases hc; cases hC; exact ⟨rfl, _, rfl⟩
    | (_ + 1), hc => simp [ntreeSurf] at hc
  | (_ + 1), hj => simp [ntreeSurf] at hj

/-! ## §4 The control: the β-redex, on which the inferencer returns `none`

`Theory/Typing/ConstSubstNested.lean`'s `ntreeNode_substC_ne_typeR` says that `VExpr.substC` of the
auxiliary constructor type would produce the **β-redex** `(fun α => List (NTree α)) α` where Lean
stores the contracted `List (NTree α)`.  So the redex is the sharp control: *the same type up to one
β-step*, at the same table, and the inferencer answers differently. -/

/-- The redex, as a domain: `(fun β => List (NTree β)) α`, with `α` the block's parameter. -/
def ntreeNodeRedexDom : Expr :=
  .app (.lam `β (.sort (.succ (.param `u)))
      (.app (.const ``List [.param `u]) (.app (.const ``NTree [.param `u]) (.bvar 0))) .default)
    (.bvar 1)

/-- …and its contraction, which is what Lean actually stores (M1). -/
def ntreeNodeContrDom : Expr :=
  .app (.const ``List [.param `u]) (.app (.const ``NTree [.param `u]) (.bvar 1))

/-- The same two, abstractly.  `Lean.Expr.headBeta` is `@[extern]`/`opaque` all the way down, so the
β-step cannot be stated at the `Expr` level by `rfl`; `VExpr.betaHead` (B6 §1) is pure Lean, so it
can be stated there — and §1/§2 supply the bridge between the two levels. -/
def vRedexDom : VExpr :=
  .app (.lam (.sort (.succ (.param 0)))
      (.app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 0)))) (.bvar 1)

def vContrDom : VExpr :=
  .app (.const ``List [.param 0]) (.app (.const ``NTree [.param 0]) (.bvar 1))

/-- **The two differ by exactly one head-β step**, so the control below is not comparing a
well-formed type with a malformed one. -/
theorem vRedexDom_betaHead : vRedexDom.betaHead = vContrDom := rfl

/-- …and the two `Expr`-level domains are the reifications of those two, up to binder
annotations — §1's `toExpr` and §2's `stripBinderData`, doing the level-crossing. -/
theorem ntreeNodeRedexDom_reify :
    stripBinderData ntreeNodeRedexDom = vRedexDom.toExpr [`u] := rfl

theorem ntreeNodeContrDom_reify :
    stripBinderData ntreeNodeContrDom = vContrDom.toExpr [`u] := rfl

/-- The user's constructor type with the recursive field's domain written as the redex. -/
def ntreeNodeRedexE : Expr :=
  .forallE `α (.sort (.succ (.param `u)))
    (.forallE `a (.bvar 0)
      (.forallE `as ntreeNodeRedexDom
        (.app (.const ``NTree [.param `u]) (.bvar 2)) .default) .default) .implicit

/-- …and with it contracted: this **is** Lean's stored type, up to binder annotations, by `rfl`. -/
def ntreeNodeContrE : Expr :=
  .forallE `α (.sort (.succ (.param `u)))
    (.forallE `a (.bvar 0)
      (.forallE `as ntreeNodeContrDom
        (.app (.const ``NTree [.param `u]) (.bvar 2)) .default) .default) .implicit

theorem ntreeNodeContrE_eq :
    stripBinderData ntreeNodeContrE = stripBinderData (exprOf% NTree.node) := rfl

/-- **THE CONTROL.**  `ctorTr?` returns `none` on the redex form **outright**, for *every* table
`Γc`, *every* level list `Us` and *every* context `Γ` — not "some wrong answer", and not a table
failure.  The reason is structural: `ctorTr?` has no `.lam` clause, so the `.app` clause's first bind
is already `none`.

This is the one place `noLam`'s content is genuinely visible in this file — as a **control**, and
still not as a citation: nothing here uses `noLam_of_ctorTr`, because what is being shown is again a
fact about the *input*. -/
theorem ntreeNodeRedex_ctorTr?_none {Γc : Name → Option VConstant} {Us : List Name}
    {Γ : List VExpr} : ctorTr? Γc Us ntreeNodeRedexE Γ = none := by
  simp [ntreeNodeRedexE, ntreeNodeRedexDom, ctorTr?]

/-- …while on the contracted form at `ntreeΓcU` it **succeeds**, at the restored abstract type.
Same type, one β-step apart, opposite answers. -/
theorem ntreeNodeContr_ctorTr?_some :
    ∃ t', ctorTr? ntreeΓcU [`u] ntreeNodeContrE []
      = some (ntreeNode.typeR ntreeAux ntreeRestore 0, t') := ⟨_, rfl⟩

/-! ## §5 Anti-vacuity: every lookup premise discharged, and one that *cannot* be at `ntreeEnvU`

M13 of `docs/handoff-b6.md` is the standing lesson: an arity-0 witness whose conjuncts are
implications proves nothing until the antecedent is exhibited.  So each premise is checked here, and
one of them turns out to be unsatisfiable — recorded rather than smoothed over. -/

/-- The `ConstLookup` antecedent is satisfiable: here is a constant the table actually holds, and it
is the *new* one, `List`. -/
theorem ntreeΓcU_List :
    ntreeΓcU ``List
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl

theorem ntreeEnvU_constants_List :
    ntreeEnvU.constants ``List
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl

/-- **…and `constLookupU_staged`'s antecedent is NOT satisfiable at `ntreeEnvU`**, by `rfl`.
`VEnv.addConst` fails on a name already present, and `ntreeAux.typeConstsC ntreeK` is exactly
`[(NTree, ⟨1, ∀ (α : Type u), Type u⟩)]` — whose name `ntreeEnvU` already carries.  So
`constLookupU_staged` above, and B6's `constLookup_staged_ntree` at `ntreeEnv` for the same reason,
are **vacuously true as stated**.  Nothing in this file depends on either:
`ctorStoresTr_of_ctorTr_setRecArgs` asks only for `ConstLookup Γc env`, which is `constLookupU`. -/
theorem ntreeEnvU_addIndTypesC_none : ntreeEnvU.addIndTypesC ntreeAux ntreeK = none := rfl

theorem ntreeAux_typeConstsC :
    ntreeAux.typeConstsC ntreeK
      = [(``NTree, ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)] := rfl

/-- The table with `NTree` withheld — the *pre-block* table, which is what a staging statement is
supposed to be about. -/
def ntreeΓcU0 : Name → Option VConstant := fun n =>
  if n = ``List ∨ n = `_nested.List_1 then
    some { uvars := 1, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))) }
  else none

def ntreeEnvU0 : VEnv where
  constants := ntreeΓcU0
  defeqs _ := False

/-- **The antecedent, exhibited.**  Staging really does succeed from the pre-block environment. -/
theorem ntreeEnvU0_addIndTypesC :
    ∃ env₁, ntreeEnvU0.addIndTypesC ntreeAux ntreeK = some env₁ := ⟨_, rfl⟩

/-- **…and the staged lookup, non-vacuously.**  `NTree` arrives from the block
(`ntreeAux.typeConstsC ntreeK`), `List` and `_nested.List_1` from the pre-block environment — which
is `constLookup_staged_of_split`'s disjunction, discharged leaf by leaf. -/
theorem constLookupU0_staged :
    ∀ env₁, ntreeEnvU0.addIndTypesC ntreeAux ntreeK = some env₁ → ConstLookup ntreeΓcU env₁ := by
  refine constLookup_staged_of_split fun c ci hc => ?_
  rw [ntreeΓcU] at hc
  split at hc
  · rename_i h
    cases hc
    rcases h with rfl | rfl | rfl
    · exact .inl (.head _)
    · exact .inr rfl
    · exact .inr rfl
  · exact absurd hc (by simp)

/-- …combined, so the conjunction is an existential and not an implication. -/
theorem constLookupU0_staged_witness :
    ∃ env₁, ntreeEnvU0.addIndTypesC ntreeAux ntreeK = some env₁ ∧ ConstLookup ntreeΓcU env₁ :=
  let ⟨env₁, h⟩ := ntreeEnvU0_addIndTypesC
  ⟨env₁, h, constLookupU0_staged env₁ h⟩

/-! ## §6 The witness -/

/-- **THE WITNESS — arity 0, and every conjunct either an equation or an existential.**

`CtorStoresTr` at the **user's own declaration** and the **real** restoration, the general theorem it
is an instance of, the binder bridge that connects them, and the β-redex control. -/
theorem ntreeSurf_userBlockR_witness :
    -- non-degeneracy: the user's declaration, and a restoration that is not the identity
    ntreeSurf.name = ``NTree ∧ ntreeSurf.ctors.length = 1 ∧
    ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
    ntreeAux.types.length = 2 ∧
    ntreeRestore.tyName 1 = ``List ∧ ntreeAux.idRestore.tyName 1 = `_nested.List_1 ∧
    -- (1) the general theorem: `ctorTr?` left-inverts reification, levels unrestricted, no typing
    -- side condition, any table, any context
    (∀ (Γc : Name → Option VConstant) (Us : List Name), Us.Nodup →
      ∀ (v : VExpr), v.lvlWF Us.length → ∀ (Γ : List VExpr) (p : VExpr × VExpr),
        ctorTr? Γc Us (v.toExpr Us) Γ = some p → p.1 = v) ∧
    -- (2) the binder-annotation bridge, unconditionally
    (∀ (Γc : Name → Option VConstant) (Us : List Name) (e : Expr) (Γ : List VExpr),
      ctorTr? Γc Us (stripBinderData e) Γ = ctorTr? Γc Us e Γ) ∧
    -- (3) LEAN'S OWN STORED TYPE IS THE REIFICATION of the abstract constructor type at the real
    -- restoration, up to binder annotations
    stripBinderData (exprOf% NTree.node)
      = (ntreeNode.typeR ntreeAux ntreeRestore 0).toExpr [`u] ∧
    -- (4) …so the per-constructor equation holds, and holds *through* (1)-(3) rather than by a
    -- second `rfl`
    (∃ t', ctorTr? ntreeΓcU [`u] (exprOf% NTree.node) []
      = some (ntreeNode.typeR ntreeAux ntreeRestore 0, t')) ∧
    (∀ p : VExpr × VExpr, ctorTr? ntreeΓcU [`u] (exprOf% NTree.node) [] = some p →
      p.1 = ntreeNode.typeR ntreeAux ntreeRestore 0) ∧
    -- (5) `ntreeAux` is exhibited in `setRecArgsD` form, so B6 part 3 applies with no detour
    (surfHeader 1 [.sort (.succ (.param 0))] ntreeRTypes).setRecArgsD (eraseRecArgs ntreeAux)
      = ntreeAux ∧
    -- (6) THE HEADLINE: `CtorStoresTr` at `[ntreeSurf]` and `ntreeRestore`, no hypotheses
    CtorStoresTr ntreeEnvU [`u] [ntreeSurf] ntreeAux ntreeRestore ∧
    -- (7) THE CONTROL: the β-redex form, one head-β step away, on which the inferencer returns
    -- `none` for every table, every level list and every context
    vRedexDom.betaHead = vContrDom ∧
    stripBinderData ntreeNodeRedexDom = vRedexDom.toExpr [`u] ∧
    stripBinderData ntreeNodeContrDom = vContrDom.toExpr [`u] ∧
    stripBinderData ntreeNodeContrE = stripBinderData (exprOf% NTree.node) ∧
    (∀ (Γc : Name → Option VConstant) (Us : List Name) (Γ : List VExpr),
      ctorTr? Γc Us ntreeNodeRedexE Γ = none) ∧
    -- (8) ANTI-VACUITY.  The `ConstLookup` premise, discharged at a concrete environment, with the
    -- antecedent exhibited; and the staged form's antecedent, which is UNSATISFIABLE at `ntreeEnvU`
    -- (so `constLookupU_staged` is vacuous as stated — nothing here uses it) but satisfiable at the
    -- pre-block `ntreeEnvU0`, where the staged lookup is proved with the antecedent in hand.
    ConstLookup ntreeΓcU ntreeEnvU ∧
    ntreeEnvU.constants ``List
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ ∧
    ntreeEnvU.addIndTypesC ntreeAux ntreeK = none ∧
    (∃ env₁, ntreeEnvU0.addIndTypesC ntreeAux ntreeK = some env₁ ∧
      ConstLookup ntreeΓcU env₁) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   fun _ _ hUs _ hv _ _ h => VExpr.ctorTr?_toExpr hUs hv h,
   fun _ _ _ _ => ctorTr?_stripBinderData,
   user_is_reification,
   ntreeNode_ctorTr?_typeR,
   fun _ => ntreeNode_ctorTr?_typeR_of_general,
   ntreeAux_setRecArgsD,
   chain,
   vRedexDom_betaHead, ntreeNodeRedexDom_reify, ntreeNodeContrDom_reify, ntreeNodeContrE_eq,
   fun _ _ _ => ntreeNodeRedex_ctorTr?_none,
   constLookupU, ntreeEnvU_constants_List, ntreeEnvU_addIndTypesC_none,
   constLookupU0_staged_witness⟩

end InductiveDeclExamples

/-! ## §7 Axiom audit -/

#print axioms Lean4Lean.VLevel.toLevel
#print axioms Lean4Lean.VLevel.ofLevel_toLevel
#print axioms Lean4Lean.VLevel.mapM_ofLevel_toLevel
#print axioms Lean4Lean.VExpr.toExpr
#print axioms Lean4Lean.VExpr.lvlWF
#print axioms Lean4Lean.VExpr.ctorTr?_toExpr
#print axioms Lean4Lean.stripBinderData
#print axioms Lean4Lean.ctorTr?_stripBinderData
#print axioms Lean4Lean.InductiveDeclExamples.ntreeΓcU
#print axioms Lean4Lean.InductiveDeclExamples.constLookupU
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_ctorTr?_typeR
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_ctorTr?_declared
#print axioms Lean4Lean.InductiveDeclExamples.user_is_reification
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNode_ctorTr?_typeR_of_general
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_setRecArgsD
#print axioms Lean4Lean.InductiveDeclExamples.chain
#print axioms Lean4Lean.InductiveDeclExamples.vRedexDom_betaHead
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNodeRedex_ctorTr?_none
#print axioms Lean4Lean.InductiveDeclExamples.ntreeNodeContr_ctorTr?_some
#print axioms Lean4Lean.InductiveDeclExamples.ntreeEnvU_addIndTypesC_none
#print axioms Lean4Lean.InductiveDeclExamples.constLookupU0_staged_witness
#print axioms Lean4Lean.InductiveDeclExamples.ntreeSurf_userBlockR_witness
