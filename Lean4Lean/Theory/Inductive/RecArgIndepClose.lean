import Lean4Lean.Theory.Inductive.RecArgIndep
import Lean4Lean.Theory.Inductive.NestedHead
import Lean4Lean.Theory.Typing.ShapeIndepStep
import Lean4Lean.Theory.Typing.RigidNodeCircle

/-!
# `VIndRecArg.exists_indep`: the consumer census, the real blocker, and a better witness

`VIndRecArg.exists_indep` (`Theory/Inductive/Decl.lean`:642, `sorry` at :661) is the discharge
obligation for `VIndField.WF.binders_indep`.  `Theory/Inductive/RecArgIndep.lean` already prices
it: the conclusion is transcribed as `VIndRecArg.IndepGoal`, three drop-ins close the regime where
`BindersIndep` already holds, and §7 exhibits the residual case at a non-staged environment.
This file adds what that file does not have, and nothing in it edits `Decl.lean`.

## Nothing edited, nothing assumed: the three measurements this file is built on

* **`exists_indep` has one direct and one transitive user** (`scripts/users.lean`,
  2026-09-03 18:02 UTC), and that user is `VIndRecArg.indepGoal_of_exists_indep` — the
  *faithfulness check* in `RecArgIndep.lean` whose only job is to apply the hole so that
  `IndepGoal` is provably its conclusion.  **No proof in the tree stands on this hole.**
* Every `VIndField.WF.binders_indep` in the tree — 40-odd construction sites across
  `DeclExamples`, `NestedHead`, `NestedBuild`, `IndexedWit`, `ParamRedex`, `MemberRedex`,
  `RestoreBridge`, `ConstSubstNested`, `PreludeWitness` and six `Verify/` witnesses — is
  discharged *directly*: `nofun`, or `bindersIndep_of_binders_nil`-shaped (`ξ = []`), or a real
  syntactic lemma (`NestedBuild.pfnAuxMk_bindersIndep`, `DeclExamples.wMk_BindersIndep`).  Not
  one of them routes through `exists_indep`.
* There is **no refutation** of `exists_indep` in the tree and no equivalent proof of it under
  another name.  The only negation mentioning `BindersIndep` is
  `RecArgIndep.not_bindersIndep_raiRec1`, which negates the clause *at one `r`* — the existential
  may still pick another `r'` — and at an environment `RecArgIndep.rai_not_staged` shows the
  hole's own `henv₀`+`hstage` pair excludes.

So the hole's role is *prospective*: it is what a general proof of `VIndCtor.WF.fields` inside
`addInduct_WF` would call.  Its price should be measured against that, not against a live
consumer.

## §1 The reduction, as an `↔` rather than an implication

`RecArgIndep.indepGoal_of_indepUpgrade` proves `IndepUpgrade → IndepGoal` at the cost of
`VEnv.SortUniq`.  The converse is **free** (§1), because `BindersIndep` reads only `.binders`, so
`IndepGoal ↔ IndepUpgrade` over `SortUniq` — the two differ by exactly the `F.type` conversion
and `SortUniq` is exactly its price.  That makes `IndepUpgrade` *the* smallest sufficient premise:
everything else in the hole's conclusion is recoverable from it and from `pos`'s own clauses.

## §2 The blocker is not `forallE_inv`; it is the two rigidity facts, and they are named

`exists_indep`'s docstring names one open input, `VEnv.IsDefEqU.forallE_inv`.  Walking the actual
obstruction gives a different and *smaller* answer.  For a binder `B ∈ r.binders` to mention the
earlier recursive field `x`, `x` must occur as a subterm of `B`; `B` is syntactically block-free
(`hbind`), and `x`'s type is a block spine `I_j params π`.  Enumerating the positions `x` can
occupy in a well-typed block-free `B`:

* as the head of an application — then `x` is applied, and `x`'s type must convert to a Π;
* as an argument — then the function's type must convert to a Π *with a block-spine domain*, and
  the function is a `bvar` of `Γ` (a parameter, or an earlier field), a `const`, or a `lam`;
* as a Π/λ domain or as `B` itself — then `x`'s type must convert to a sort.

`const` is excluded by staging: `env₀` cannot declare a constant whose type mentions the block,
because `addIndTypes` would then fail on the name clash (this is `RecArgIndep.rai_not_staged`
generalised).  A `lam` domain, a parameter's domain and an earlier field's domain are all
excluded *only if* no block-free type converts to a block spine — and a parameter cannot carry
that domain for a syntactic reason: `VInductDecl'.tyApp` applies **all** the parameters to `I_j`,
so a parameter whose type mentioned `I_j params π` would mention itself.

What survives is exactly: **a block spine is defeq to neither a Π nor a sort.**  Those two
statements are already named in this tree — `VEnv.RigidConstPiDisj` and
`VEnv.RigidConstSortDisj` (`Theory/Typing/RigidNodeCircle.lean`) — and both are guarded by
`VEnv.RuleFreeHead`.  §2 proves the missing bridge: **at a staged environment the block's
constants are rule-free** (`blockConst_ruleFreeHead_of_staged`), so both predicates apply to the
block spines, unconditionally.  `IsDefEqU.forallE_inv` is *not* on this path.

**And the two rigidity facts are false at `Ordered` environments** — machine-checked in this
tree, `VEnv.not_rigidConstPiDisj_rcPiEnv` and `VEnv.not_rigidConstSortDisj_rcSortEnv`
(`Theory/Typing/RigidConstPrice.lean`), at `ordered_rcPiEnv` / `ordered_rcSortEnv`.  Since
`exists_indep` carries `VEnv.Ordered env` and deliberately not `VEnv.WF env` (naming `VEnv.WF`
at this layer is an import cycle, as its docstring says), it cannot simply *have* them.  §2c is
the answer: the refutations work by pointing a two-rule **hub** constant at a rule-free head, and
`defeq_noBlock_of_staged` shows no rule of a staged environment mentions the block on either side
or in its type — freshness, no well-formedness needed.  So the tree's only known refutation route
is closed for block spines, and what is left is a confluence question.

**Why none of this is put into `Decl.lean`** (the "cheap retirement can be a net loss" check, run
rather than assumed).  `RigidConstPiDisj` and `RigidConstSortDisj` are supplied in general by
`RigidShapeUniqNS.constPiDisj` / `.constSortDisj` from `VEnv.WF.rigidShapeUniqNS`, which is itself
a `sorry` (`Theory/Typing/Injectivity.lean`:1046) with **529 transitive users**
(`scripts/users.lean`, 2026-09-03 18:02 UTC).  `Decl.lean`'s cone today is 851 constants whose
*only* hole is `exists_indep` itself (`scripts/exists.lean`, same run).  Discharging the hole
through that route would therefore put a 529-user hole into `Decl.lean`'s cone, and `Decl.lean`
is upstream of `VEnv.WF`: a strict loss, and an import cycle besides.  So the rigidity facts stay
**hypotheses** here, exactly as the three existing drop-ins keep their extra hypothesis, and the
proposed edit to `Decl.lean` is a docstring correction only.

## §3 A strictly better non-vacuity witness: a real nested block, with an earlier recursive field

`RecArgIndep.rai_hyps_all` satisfies all ten hypotheses, but at `uvars = 0`, `params = []`,
`pre = []` — degenerate on three axes at once, and `pre = []` is precisely the axis
`BindersIndep` is about.  §3 satisfies the same ten at
`InductiveDeclExamples.ntreeAux` — `uvars = 1`, `params = [.sort (.succ (.param 0))]`, the
parameterised nested block Lean's own kernel runs nested elimination on — taken at the **second
field of `_nested.List_1.cons`, whose earlier field is recursive**.  So `hpre` is not vacuous,
`bindersIndep_of_pre_norec` does not apply, and the instance sits in the regime the clause was
written for.

**And it records the honest limit of that witness**: `ntreeAux`'s recursive fields all have
`ξ = []`, so it is closed by `exists_indep_of_binders_nil`.  Together with the census above:
**no witness anywhere in this tree needs a binder to move**, and the real nested block does not
either.
-/

namespace Lean4Lean

namespace RecArgIndepClose

open VExpr (mkPi)

/-! ## §1 `IndepGoal ↔ IndepUpgrade`

`RecArgIndep.indepGoal_of_indepUpgrade` is the hard direction and costs `VEnv.SortUniq`.  The
easy direction below costs nothing at all, which is the point: `VIndRecArg.BindersIndep` reads
only the `.binders` field, so the witness telescope of `IndepGoal` *is* an `IndepUpgrade`
witness with no repackaging. -/

/-- **`IndepGoal → IndepUpgrade`, free.**  Not in `RecArgIndep.lean`, which has only the
converse. -/
theorem indepUpgrade_of_indepGoal {env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (h : VIndRecArg.IndepGoal env D Γ pre i F r) : r.IndepUpgrade env D Γ pre i := by
  obtain ⟨r', -, -, -, hnb, -, hindep, htele⟩ := h
  exact ⟨r'.binders, htele, hnb, hindep⟩

/-- **The equivalence.**  `IndepUpgrade` is the smallest sufficient premise for the hole: it
drops the `F.type` conversion, and `VEnv.SortUniq` is exactly the price of putting it back
(`RecArgIndep.isDefEqType_trans_of_sortUniq`).  Stated as an `↔` so that "the hole is the
telescope replacement and nothing else" is a theorem.

The right-to-left hypotheses are all clauses a caller already holds: `hOn` and `hres` are
`VIndField.WF.pos`'s own `OnCtx` and `canonResult` typing, and `hdefeq` is the hole's. -/
theorem indepGoal_iff_indepUpgrade {env : VEnv} {D : VInductDecl'} {Γ : List VExpr}
    {pre : List VIndField} {i : Nat} {F : VIndField} {r : VIndRecArg}
    (henv : VEnv.Ordered env) (hsu : env.SortUniq D.uvars)
    (hΓ : OnCtx Γ (env.IsType D.uvars))
    (hOn : OnCtx (r.binders.reverse ++ Γ) (env.IsType D.uvars))
    (hres : env.HasType D.uvars (r.binders.reverse ++ Γ) (r.canonResult D i) (.sort D.lvl))
    (hdefeq : env.IsDefEqType D.uvars Γ F.type (r.canonType D i)) :
    VIndRecArg.IndepGoal env D Γ pre i F r ↔ r.IndepUpgrade env D Γ pre i :=
  ⟨indepUpgrade_of_indepGoal,
   RecArgIndep.indepGoal_of_indepUpgrade henv hsu hΓ hOn hres hdefeq⟩

/-! ## §2 At a staged environment the block's constants are rule-free -/

/-- `VInductDecl'.typeConsts` and `VInductDecl'.blockNames` list the same names. -/
theorem typeConsts_map_fst (D : VInductDecl') :
    D.typeConsts.map (·.1) = D.blockNames := by
  simp [VInductDecl'.typeConsts, VInductDecl'.blockNames, List.map_map]

/-- **The bridge §2 exists for.**  `VEnv.RuleFreeHead` is a condition on `env.defeqs`, and
`addIndTypes` is `addConst`s only, so it is inherited from `env₀`; and in `env₀` the block's
names are undeclared (`addConstList_fresh`), which is `ruleFreeHead_of_not_contains`'s premise.

This is what lets `VEnv.RigidConstPiDisj` / `VEnv.RigidConstSortDisj` be applied to a block
spine at all: both are guarded by `RuleFreeHead`, and nothing in the tree discharged that guard
for a block constant. -/
theorem blockConst_ruleFreeHead_of_staged {env₀ env : VEnv} {D : VInductDecl'}
    (henv₀ : VEnv.Ordered env₀) (hstage : env₀.addIndTypes D = some env)
    {c : Lean.Name} (hc : c ∈ D.blockNames) : env.RuleFreeHead c := by
  have hfresh : env₀.constants c = none :=
    (VEnv.addConstList_fresh hstage).1 c (by rw [typeConsts_map_fst]; exact hc)
  intro df hdf
  rw [VEnv.addConstList_defeqs hstage] at hdf
  exact VEnv.ruleFreeHead_of_not_contains henv₀ hfresh df hdf

/-- **A block spine is not defeq to a Π** — given `RigidConstPiDisj`, which §2's header explains
is why this is a hypothesis and not a theorem. -/
theorem blockSpine_not_defeq_forallE {env₀ env : VEnv} {D : VInductDecl'}
    (henv₀ : VEnv.Ordered env₀) (hstage : env₀.addIndTypes D = some env)
    (hcp : env.RigidConstPiDisj D.uvars)
    {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {A B : VExpr}
    (hc : c ∈ D.blockNames) (hΓ : OnCtx Γ (env.IsType D.uvars)) :
    ¬ env.IsDefEqU D.uvars Γ ((VExpr.const c ls).mkApp as) (.forallE A B) :=
  hcp hΓ (blockConst_ruleFreeHead_of_staged henv₀ hstage hc)

/-- **A block spine is not defeq to a sort.** -/
theorem blockSpine_not_defeq_sort {env₀ env : VEnv} {D : VInductDecl'}
    (henv₀ : VEnv.Ordered env₀) (hstage : env₀.addIndTypes D = some env)
    (hcs : env.RigidConstSortDisj D.uvars)
    {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel} {as : List VExpr} {u : VLevel}
    (hc : c ∈ D.blockNames) (hΓ : OnCtx Γ (env.IsType D.uvars)) :
    ¬ env.IsDefEqU D.uvars Γ ((VExpr.const c ls).mkApp as) (.sort u) :=
  hcs hΓ (blockConst_ruleFreeHead_of_staged henv₀ hstage hc)

/-! ### §2b The constant route, closed as a theorem

`RecArgIndep.lean` §7.3 observes at *one* witness (`raiCiP_type_hasBlock`) that what makes its
candidate counterexample work is a declared constant whose **type** mentions the block, and that a
staged environment cannot hold one.  The two lemmas below make that a theorem about every staged
environment, which is what the docstring's "nothing in scope can eliminate an `I`" argument needs
and what `rai_not_staged` only supplies at `raiD`.

Note the one thing this does *not* say, and which the docstring does not mention either: the
block's **own** type constants are exempt.  `addIndTypes` adds them left to right, so `Ordered`
lets `I₁`'s stored type mention `I₀`.  That route cannot contribute a binder, because a binder is
required to be *syntactically* block-free (`hbind`), so `.const I₁ _` cannot occur in it at all —
but it is why the statement below is about `env₀`'s constants and not about `env`'s. -/

/-- `ConstsIn` a predicate that avoids `S` gives `NoConsts S`. -/
theorem noConsts_of_constsIn {S : List Lean.Name} {P : Lean.Name → Prop} (hS : ∀ n ∈ S, ¬ P n) :
    ∀ {e : VExpr}, e.ConstsIn P → VExpr.NoConsts S e
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => fun hc => hS c hc h
  | .app .., h | .lam .., h | .forallE .., h =>
    ⟨noConsts_of_constsIn hS h.1, noConsts_of_constsIn hS h.2⟩

/-- **No constant of the pre-block environment has a type mentioning the block.**  Its two
inputs are exactly the hole's `henv₀` and `hstage`: `Ordered.constsInC` says a declared type
mentions only declared constants, and `addConstList_fresh` says the block's names are not among
them. -/
theorem env₀_const_noBlock_of_staged {env₀ env : VEnv} {D : VInductDecl'}
    (henv₀ : VEnv.Ordered env₀) (hstage : env₀.addIndTypes D = some env)
    {c : Lean.Name} {ci : VConstant} (hci : env₀.constants c = some ci) :
    D.NoBlock ci.type := by
  refine noConsts_of_constsIn (fun n hn ⟨ci', hci'⟩ => ?_) (henv₀.constsInC hci)
  have := (VEnv.addConstList_fresh hstage).1 n (by rw [typeConsts_map_fst]; exact hn)
  rw [this] at hci'; exact absurd hci' nofun

/-! ### §2c The strongest form: at a staged environment, no δ-rule mentions the block at all

This is the sharpest fact of the file, and it is what makes §2's residual a *confluence*
question rather than an environment-pathology question.

`Theory/Typing/RigidConstPrice.lean` machine-checks that both premises §2 reduces to are
**false at `Ordered` environments**: `VEnv.not_rigidConstPiDisj_rcPiEnv` and
`VEnv.not_rigidConstSortDisj_rcSortEnv`, at `ordered_rcPiEnv` / `ordered_rcSortEnv`.  Read
naively that is fatal — `exists_indep` has `VEnv.Ordered env` and deliberately *not* `VEnv.WF env`
(its docstring: naming `VEnv.WF` here is an import cycle), so it cannot have the premises §2 asks
for.

But look at how those refutations work.  Each adds a **hub** constant with two δ-rules —
`rcHub ≡ rcRF.{0}` and `rcHub ≡ ∀ (_ : Prop), Prop` — so `rcRF` heads no rule (`RuleFreeHead`
holds) and is still convertible to a Π *through the hub*.  The theorem below says that route is
unavailable for a block constant at a staged environment, for a reason that is pure freshness and
needs no well-formedness: **`addIndTypes` copies `env₀.defeqs` unchanged, and `Ordered env₀` makes
every side of every rule in it mention only `env₀`-declared constants — none of which is a block
name.**  So no rule in `env` mentions the block on *either* side or in its type; a hub cannot be
pointed at `I_j` after the fact, because rules are never added later either.

What is left of §2's residual is therefore: at a staged environment, can the conversion relation
itself — β, η, proof irrelevance and rules that never mention the block — relate a block spine to
a Π or to a sort?  That is the confluence question `VEnv.WF.rigidShapeUniqNS` answers, and the
known counterexample family does not reach it.  **[analysis, not proved]** that it cannot; this
file proves only that the tree's one refutation route is closed. -/

/-- **No defining equation of a staged environment mentions the block** — not on the left, not on
the right, not in its type. -/
theorem defeq_noBlock_of_staged {env₀ env : VEnv} {D : VInductDecl'}
    (henv₀ : VEnv.Ordered env₀) (hstage : env₀.addIndTypes D = some env)
    {df : VDefEq} (hdf : env.defeqs df) :
    D.NoBlock df.lhs ∧ D.NoBlock df.rhs ∧ D.NoBlock df.type := by
  rw [VEnv.addConstList_defeqs hstage] at hdf
  have hfr : ∀ n ∈ D.blockNames, ¬ env₀.contains n := fun n hn ⟨ci', hci'⟩ => by
    have := (VEnv.addConstList_fresh hstage).1 n (by rw [typeConsts_map_fst]; exact hn)
    rw [this] at hci'; exact absurd hci' nofun
  obtain ⟨h1, h2, h3⟩ := henv₀.constsInD hdf
  exact ⟨noConsts_of_constsIn hfr h1, noConsts_of_constsIn hfr h2,
    noConsts_of_constsIn hfr h3⟩

/-! ## §3 All ten hypotheses at a real nested block, with an earlier *recursive* field

`RecArgIndep.rai_hyps_all` is the tree's only joint instance of the hole's ten hypotheses, and it
is degenerate on three axes: `uvars = 0`, `params = []`, `pre = []`.  The last of those is the
axis that matters, because `VIndRecArg.BindersIndep` quantifies over the earlier *recursive*
fields and there are none.

This instance fixes all three.  The block is `InductiveDeclExamples.ntreeAux` — `uvars = 1`,
`params = [.sort (.succ (.param 0))]`, the parameterised nested block whose nested eliminator
Lean's own kernel builds — and the field is the **second** field of `_nested.List_1.cons`, whose
first field is recursive (into `NTree`).  So `hpre` supplies a `VIndField.WF` whose `recArg` is
`some`, and `bindersIndep_of_pre_norec` does not apply here.

`env₀` is `VEnv.empty`, so `henv₀` is `Ordered.empty` and `hstage` is a computation;
`ntreeAux_WF'` holds at *every* environment (`NestedHead.lean`), so `henv` comes from
`VInductDecl'.addIndTypes_ordered` and the six field-level hypotheses come from
`VIndCtor.WF.fields` rather than from re-derivation.

**The honest limit, recorded at the statement as house style asks.**  `ntreeAux`'s recursive
fields all carry `ξ = []` (`ntreeAux_binders_indep` is how `NestedHead.lean` discharges the clause
for all three of them), so this instance is *closed* by
`VIndRecArg.exists_indep_of_binders_nil`, and `nl_binders_nil` below says so.  It is a
strictly better **non-vacuity** witness than `rai_hyps_all`; it is **not** a witness that the
residual case is reachable at a staged environment.  Whether that case is reachable at all is
still open, and §2 says what it turns on. -/

namespace NTreeHyps

open InductiveDeclExamples

/-- The earlier fields of `_nested.List_1.cons`'s second field: one field, and it is recursive. -/
def nlPre : List VIndField := nlistCons.fields.take 1

/-- …recorded, so "the earlier field is recursive" is a computation and not a claim. -/
theorem nlPre_recArg : ∃ F ∈ nlPre, F.recArg.isSome := by
  refine ⟨nlistCons.fields[0], ?_, ?_⟩ <;> simp [nlPre, nlistCons]

/-- …and in particular `bindersIndep_of_pre_norec`'s hypothesis fails here. -/
theorem nlPre_not_norec : ¬ ∀ F' ∈ nlPre, F'.recArg = none := by
  intro h
  obtain ⟨F, hF, hs⟩ := nlPre_recArg
  rw [h F hF] at hs; simp at hs

/-- The field context of field 1, exactly as `VIndCtor.WF.fields` builds it. -/
def nlΓ : List VExpr := (nlPre.map (·.type)).reverse ++ ntreeAux.params.reverse

/-- The recursive-field data of field 1: it recurses into `_nested.List_1`, which is
`ntreeAux.types[1]`. -/
def nlRec1 : VIndRecArg := ⟨[], 1, []⟩

theorem nlF1_recArg : ∃ F, nlistCons.fields[1]? = some F ∧ F.recArg = some nlRec1 :=
  ⟨_, rfl, rfl⟩

/-- `ξ = []` here, which is the limit this witness has and `rai_hyps_all` also has. -/
theorem nl_binders_nil : nlRec1.binders = [] := rfl

/-- **All ten hypotheses of `VIndRecArg.exists_indep`, at `ntreeAux` / `_nested.List_1.cons`,
field 1 — with `pre` containing a recursive field.** -/
theorem ntree_hyps_all :
    ∃ (env₂ : VEnv) (F : VIndField),
      nlistCons.fields[1]? = some F ∧ F.recArg = some nlRec1 ∧
      VEnv.Ordered VEnv.empty ∧
      VEnv.Ordered env₂ ∧
      VEnv.empty.addIndTypes ntreeAux = some env₂ ∧
      nlPre.length = 1 ∧
      nlΓ = (nlPre.map (·.type)).reverse ++ ntreeAux.params.reverse ∧
      (∀ (i' : Nat) (F' : VIndField), nlPre[i']? = some F' →
        F'.WF env₂ ntreeAux (nlPre.take i')
          (((nlPre.take i').map (·.type)).reverse ++ ntreeAux.params.reverse) i') ∧
      env₂.HasType ntreeAux.uvars nlΓ F.type (.sort F.lvl) ∧
      (∀ B ∈ nlRec1.binders, ntreeAux.NoBlock B) ∧
      OnCtx (nlRec1.binders.reverse ++ nlΓ) (env₂.IsType ntreeAux.uvars) ∧
      env₂.IsDefEqType ntreeAux.uvars nlΓ F.type (nlRec1.canonType ntreeAux 1) := by
  obtain ⟨env₂, hstage⟩ : ∃ env₂, VEnv.empty.addIndTypes ntreeAux = some env₂ :=
    VEnv.exists_addConstList (by simp [VEnv.empty]) (by decide)
  have hord : VEnv.Ordered env₂ :=
    VInductDecl'.addIndTypes_ordered .empty ntreeAux_WF' hstage
  have hC : VIndCtor.WF env₂ ntreeAux 1 _ nlistCons :=
    ntreeAux_WF'.ctors env₂ hstage 1 _ rfl nlistCons (.tail _ (.head _))
  have hF1 := hC.fields 1 _ rfl
  have hpos : VIndField.PosSome env₂ ntreeAux nlΓ 1 _ nlRec1 :=
    VIndField.posSome_of_wf hF1 rfl
  obtain ⟨-, -, hbind, -, hOn, -, -, hdefeq, -⟩ := hpos
  refine ⟨env₂, _, rfl, rfl, .empty, hord, hstage, rfl, rfl, ?_, hF1.hasType, hbind, hOn,
    hdefeq⟩
  intro i' F' hF'
  match i', hF' with
  | 0, hF' => cases hF'; exact hC.fields 0 _ rfl
  | (_ + 1), hF' => simp [nlPre, nlistCons] at hF'

/-- **…and the obligation is met at that instance**, by
`VIndRecArg.exists_indep_of_binders_nil` — the `ξ = []` drop-in, not by anything that moves a
binder.  This is the sentence §3's header insists on: non-vacuity of the premise, degeneracy of
the conclusion, stated apart. -/
theorem ntree_indepGoal :
    ∃ (env₂ : VEnv) (F : VIndField),
      nlistCons.fields[1]? = some F ∧
      VIndRecArg.IndepGoal env₂ ntreeAux nlΓ nlPre 1 F nlRec1 := by
  obtain ⟨env₂, F, hF, -, -, -, -, -, -, -, -, hbind, -, hdefeq⟩ := ntree_hyps_all
  exact ⟨env₂, F, hF,
    VIndRecArg.indepGoal_of_bindersIndep hbind hdefeq
      (VIndRecArg.bindersIndep_of_binders_nil nl_binders_nil)⟩

end NTreeHyps

/-! ## §4 Axiom audit -/

section Audit
#print axioms Lean4Lean.RecArgIndepClose.indepUpgrade_of_indepGoal
#print axioms Lean4Lean.RecArgIndepClose.indepGoal_iff_indepUpgrade
#print axioms Lean4Lean.RecArgIndepClose.typeConsts_map_fst
#print axioms Lean4Lean.RecArgIndepClose.blockConst_ruleFreeHead_of_staged
#print axioms Lean4Lean.RecArgIndepClose.blockSpine_not_defeq_forallE
#print axioms Lean4Lean.RecArgIndepClose.blockSpine_not_defeq_sort
#print axioms Lean4Lean.RecArgIndepClose.noConsts_of_constsIn
#print axioms Lean4Lean.RecArgIndepClose.env₀_const_noBlock_of_staged
#print axioms Lean4Lean.RecArgIndepClose.defeq_noBlock_of_staged
#print axioms Lean4Lean.RecArgIndepClose.NTreeHyps.nlPre_recArg
#print axioms Lean4Lean.RecArgIndepClose.NTreeHyps.nlPre_not_norec
#print axioms Lean4Lean.RecArgIndepClose.NTreeHyps.ntree_hyps_all
#print axioms Lean4Lean.RecArgIndepClose.NTreeHyps.ntree_indepGoal
end Audit

end RecArgIndepClose

end Lean4Lean
