import Lean4Lean.Verify.Inductive.ValAtParam
import Lean4Lean.Theory.Inductive.TeleMove2

/-!
# `hargs`, attacked once: the scope half is necessary, and it is free

This file is about the single remaining leaf of the nested flip — `hargs`, the constructor-head
datum `Theory/Inductive/HargsShared.lean` §6 isolates and `Verify/Inductive/SpineClause.lean`
restates over checker-side data as `VIndRestore.SpineHargsC`.

## What this file establishes

* §1 states `hargs` per companion member (`VIndRestore.HargsAt`), and proves it is *literally*
  what §8.7 consumes (`tyVal_hasType_of_spineHargsC`).
* §2 **the scope invariant, general and hole-free**: `hargs` implies that every presented spine
  argument is `ClosedN D.np`.  So the corner's *other* spine hypothesis — `hcl`, carried
  separately at eight sites — is a consequence of the datum, not a second residual.  Its payoff
  is `csubstTy_WF_of_hargs`: `SpineClause.lean` §4's transport with `(R.csubstTy D K).Closed`
  **discharged**.
* §3 **the negative, general and hole-free**: `hargs` is FALSE of any spine with an argument
  loose in the parameter telescope, and `VNestedOcc.Occurs`, `OccursN` and `VInductDecl'.KFresh`
  all transport to such a spine.  So no consequence of the occurrence record can produce
  `hargs`, at any block — the `Occurs`/`OccursN` route is closed the way
  `VIndRestore.instAt_indep_of_tyArgs` closed the `Faithful` route.  §3c measures `Faithful`
  itself: two of its three clauses transport, and the third sees the spine only as a syntactic
  equation.
* §4 the clause, and both traps (statable where it must live; not vacuous).
* §5 the arity-0 witness at `ntreeAux`, running §2 and §3 through general theorems.

## What this file does NOT establish

`hargs` in general.  It is *produced* at two blocks already — `NestedWit.nfnAux_spineHargsN` and
`InductiveDeclExamples.ntreeAux_spineHargsC`, both arity 0 and hole-free — and
`Verify/Inductive/RestrictStep.lean`'s `restrictStep_entry` shows the general case is an `↔` with
one constant-strengthening step.  Nothing here closes that; §3 says what *cannot* close it.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars splitPis)

/-! ## §1 `hargs`, per companion member

`SpineHargsC` (`Verify/Inductive/SpineClause.lean` §2) is the datum bundled over the companion
tail.  `HargsAt` is its body at one member, which is the form every consumer's `hargs` hypothesis
actually has, and `spineHargsC_iff_hargsAt` is `Iff.rfl`, so nothing is smuggled between the two. -/

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {env e : VEnv}
  {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}

/-- **THE DATUM, AT ONE MEMBER.**  The presented spine instantiates the presented head's declared
parameter telescope, over the new block's parameters, at the target environment. -/
def HargsAt (R : VIndRestore) (D : VInductDecl') (e : VEnv) (np j : Nat) (ci : VConstant) : Prop :=
  e.HasArgs D.uvars D.params.reverse (R.declTele ci np j) (R.tyArgs j)

/-- `SpineHargsC` is `HargsAt` over the companion tail, and nothing else. -/
theorem spineHargsC_iff_hargsAt :
    R.SpineHargsC D K env e ↔ ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
        R.HargsAt D e (R.tyArgs j).length j ci := Iff.rfl

/-- **§8.7's `val` CLAUSE FROM THE CLAUSE**, with `hsplit` already discharged by
`HargsShared.lean` §2.  This is the theorem that identifies `SpineHargsC` as §8.7's residual
rather than as a neighbouring statement: the proof is `tyVal_hasType_of_hargs` applied to it.

`npJ` is pinned to `fun j => (R.tyArgs j).length` — under `Built` that is `(occ j).decl.np`
(`built_tyArgs_length`), so this is no restriction; it is what makes the clause `npJ`-free. -/
theorem tyVal_hasType_of_spineHargsC {e₂ : VEnv}
    (hfa : R.Faithful D env K (fun j => (R.tyArgs j).length)) (hle : env ≤ e₂)
    (hparams : OnCtx D.params.reverse (e₂.IsType D.uvars))
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars) (hS : R.SpineHargsC D K env e₂) :
    e₂.HasType D.uvars [] (R.tyVal D j) T.type :=
  tyVal_hasType_of_hargs hfa hle hparams hT hK hlvl (fun ci hci => hS j T hT hK ci hci)

end VIndRestore

/-! ## §2 The scope invariant: `hargs` implies the closedness family

`∀ a ∈ R.tyArgs j, a.ClosedN D.np` is carried as a *separate* hypothesis at eight sites in this
corner (`Theory/Typing/ConstSubstNested.lean`'s `csubst_closed`/`csubstTy_closed`,
`Theory/Inductive/RestoreBridge.lean` ×3, `Theory/Inductive/HTeleGen.lean`,
`Verify/Inductive/FldDischarge.lean` ×3, `Verify/Inductive/ValRestGeneral.lean`), and its only
producers in the tree are witness-specific (`Theory/Inductive/ParamRedex.lean` §7).  It is a
consequence of the datum: a typed spine is a scoped spine.

The engine is `VEnv.IsDefEq.closedN` — the scope invariant of typing — plus
`VEnv.HasArgs.mem_wf`.  No inversion, no `VEnv.HasArgs.of_mkApp`, no `PiInv`. -/

namespace VEnv

/-- **A well-typed spine is a scoped spine.**  Each argument of a `HasArgs` is closed in the
context it is typed in. -/
theorem HasArgs.closedN {env : VEnv} (henv : env.Ordered) {U : Nat} {Γ As as : List VExpr}
    (hΓ : CtxClosed Γ) (h : env.HasArgs U Γ As as) : ∀ a ∈ as, a.ClosedN Γ.length := by
  intro a ha
  obtain ⟨A, hA⟩ := h.mem_wf a ha
  exact hA.closedN henv hΓ

/-- …so a spine with an argument loose in the context is not a well-typed spine, against **any**
telescope.  This is the negative form §3 runs on. -/
theorem not_hasArgs_of_not_closedN {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ As as : List VExpr} (hΓ : CtxClosed Γ) {a : VExpr} (ha : a ∈ as)
    (hcl : ¬ a.ClosedN Γ.length) : ¬ env.HasArgs U Γ As as :=
  fun h => hcl (h.closedN henv hΓ a ha)

end VEnv

/-! ### §2b The payoff: `hcl` from the datum, and the transport with `hcl` gone

`SpineClause.lean` §4's `csubstTy_WF_of_spineHargsC` — the whole nested transport's hypothesis
`(R.csubstTy D K).WF e₂ e D.uvars` from the clause — takes `(R.csubstTy D K).Closed` as a separate
hypothesis.  It never had to: the clause implies it.  Two steps, and the first is a correction to
`Theory/Typing/ConstSubstNested.lean`'s statement rather than to its proof. -/

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {env e e₂ : VEnv}
  {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}

/-- **`csubstTy_closed` with its spine hypothesis GUARDED.**
`Theory/Typing/ConstSubstNested.lean`'s `csubstTy_closed` asks for
`∀ j, ∀ a ∈ R.tyArgs j, a.ClosedN D.np` at **every** `j` — including `j ≥ D.types.length`, where
`Built`, `OwnId` and `Faithful` are all silent (each of their clauses is guarded by
`D.types[j]? = some T`), so the unguarded form is not derivable from any bundle in the tree.  It is
also unnecessary: `csubstTyList` filters on `D.types.zipIdx`, and `csubstTy_dom` hands the index
facts back.  Guarding it is what makes §2's route reach the consumer at all.

(Recorded at the statement, per the standing rule: this weakens a *hypothesis* and proves nothing
new — the proof is `csubstTy_closed`'s, with `csubstTy_dom` in place of a discarded membership.) -/
theorem csubstTy_closed_guarded (R : VIndRestore) (D : VInductDecl') (K : List Name)
    (hp : VExpr.ClosedTele D.params 0)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ a ∈ R.tyArgs j, a.ClosedN D.np) : (R.csubstTy D K).Closed := by
  intro c t hc
  obtain ⟨j, T, hT, -, hK, rfl⟩ := csubstTy_dom hc
  show (mkLams D.params _).ClosedN 0
  rw [VExpr.closedN_mkLams]
  refine ⟨hp, ?_⟩
  rw [Nat.zero_add, VExpr.closedN_mkApp]
  exact ⟨trivial, ha j T hT hK⟩

/-- **THE SCOPE INVARIANT AT THE CLAUSE.**  `hcl`, guarded, from `hargs` — general, hole-free, and
with no hypothesis the consumers do not already carry (`Built` for the lookup, `e.Ordered` and the
parameter context for the invariant). -/
theorem spineHargsC_closedN (henv : e.Ordered)
    (hparams : OnCtx D.params.reverse (e.IsType D.uvars))
    (hB : D.Built R K env occ) (hS : R.SpineHargsC D K env e) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ a ∈ R.tyArgs j, a.ClosedN D.np := by
  intro j T hT hK a ha
  have h := hS j T hT hK _ (built_ty_const hB hT hK)
  simpa using h.closedN henv (hparams.ctxClosed henv) a ha

/-- …hence `(R.csubstTy D K).Closed` is free at the clause. -/
theorem csubstTy_closed_of_spineHargsC (henv : e.Ordered) (hOrd : env.Ordered) (hD : D.WF env)
    (hparams : OnCtx D.params.reverse (e.IsType D.uvars))
    (hB : D.Built R K env occ) (hS : R.SpineHargsC D K env e) : (R.csubstTy D K).Closed :=
  csubstTy_closed_guarded R D K
    (VExpr.ClosedTele.of_onCtx (Γ := []) hOrd (by simpa using hD.params))
    (spineHargsC_closedN henv hparams hB hS)

/-- **THE TRANSPORT, WITH `hcl` DISCHARGED.**  `SpineClause.lean` §4's
`csubstTy_WF_of_spineHargsC` minus its `(R.csubstTy D K).Closed` hypothesis: the substitution's
whole well-formedness from the clause, `D.WF`, the two `Ordered`s, freshness and the staging.

The `e.Ordered` and `OnCtx` inputs are the ones that theorem already takes (`he`, and `hparams`
via `D.WF.params` + `OnCtx.mono`), so this is strictly fewer hypotheses, not a trade. -/
theorem csubstTy_WF_of_hargs (hB : D.Built R K env occ) (hS : R.SpineHargsC D K env e)
    (hle : env ≤ e) (henv : env.Ordered) (he : e.Ordered) (hD : D.WF env)
    (hf : (R.csubstTy D K).FreshIn env)
    (h₂ : env.addIndTypes D = some e₂) (h₁ : env.addIndTypesC D K = some e)
    (hlvl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ l ∈ R.tyLvls j, l.WF D.uvars) :
    (R.csubstTy D K).WF e₂ e D.uvars :=
  csubstTy_WF_of_spineHargsC hB hS hle henv he hD hf
    (csubstTy_closed_of_spineHargsC he henv hD
      (OnCtx.mono (fun h => h.mono hle) hD.params) hB hS) h₂ h₁ hlvl

end VIndRestore

/-! ## §3 The negative: the occurrence record cannot produce `hargs`, at any block

`VIndRestore.instAt_indep_of_tyArgs` (`Theory/Inductive/NestedRules.lean` §8.7) closed the
`Faithful` route by showing `instAt` does not always read the spine.  This section closes the
`Occurs`/`OccursN` route, and it closes it *unconditionally* — no side condition of the
`instAt_indep` kind:

* every clause of `VNestedOcc.Occurs` and of `OccursN` transports to an arbitrary spine of the
  right length that mentions no reserved name (`§3a`), and the same for
  `VInductDecl'.KFresh` — so those three bundles are **blind to the spine's scope**;
* and §2 says `hargs` is FALSE of a spine that is not scoped.

So there is a spine at which the whole environment-free bundle holds and the datum fails, at
**every** occurrence record with a non-degenerate foreign parameter telescope (§3b).  The
`args_noNested` clause does not help: a de Bruijn variable mentions no constant at all.

**Where the missing condition actually lives**: the implementation *rejects* exactly this family.
`ElimNestedInductive.isNestedInductiveApp?` (`Lean4Lean/Inductive/Add.lean`) sets `looseBVars` if
any of the occurrence's first `numParams` arguments `hasLooseBVars`, and then

    throw <| .other s!"invalid nested inductive datatype '{fn}', \
      nested inductive datatypes parameters cannot contain local variables."

So the family below is not a soundness bug: it is a spec clause the abstract theory has not
recorded.  §4 states it. -/

namespace VNestedOcc

/-- **`Occurs` is blind to the spine beyond its length.**  `Theory/Inductive/NestedFresh.lean`'s
`occurs_args_congr` is the congruence form; this is the constructive form, which is what §3b
needs (it produces a record rather than transporting a hypothesis about one). -/
theorem Occurs.setArgs {N : VNestedOcc} {env : VEnv} (h : N.Occurs env) {as : List VExpr}
    (hlen : as.length = N.decl.np) : ({N with args := as} : VNestedOcc).Occurs env :=
  { h with args_len := hlen }

/-- **…and so is `OccursN`**, because its one extra clause is a condition on *constants*: a de
Bruijn variable satisfies `NoConstIn` for free. -/
theorem OccursN.setArgs {N : VNestedOcc} {env : VEnv} (h : N.OccursN env) {as : List VExpr}
    (hlen : as.length = N.decl.np) (hn : ∀ a ∈ as, a.NoConstIn IsNestedName) :
    ({N with args := as} : VNestedOcc).OccursN env :=
  { h.toOccurs.setArgs hlen with args_noNested := hn }

/-- **The datum is false at an unscoped spine**, against every telescope, at every `Ordered`
environment whose parameter context is well formed.  `ArgsTypedH.ty` is the conjunct that dies;
`.ctor` dies with it whenever the source block has a constructor.

**Stated at `ArgsTypedH` — the `HasArgs` form — and deliberately not at `ArgsTyped`, the applied
form.**  The applied form would be the more striking statement, but refuting it means getting from
`HasType ((const n ls).mkApp args) B` back to a `HasArgs` over the spine, which is
`VEnv.HasArgs.of_mkApp`, i.e. `IsDefEqU.forallE_inv` — the Π-inversion hole the nested corner is
keeping out (`HargsShared.lean` §8b, `NestedTele.lean` §T12).  So the weaker form is the one that is
hole-free, and it is the form every consumer of the datum takes anyway
(`tyVal_hasType_of_hargs`). -/
theorem not_argsTypedH_of_not_closedN {N : VNestedOcc} {D : VInductDecl'} {e : VEnv}
    (henv : e.Ordered) (hparams : OnCtx D.params.reverse (e.IsType D.uvars))
    {a : VExpr} (ha : a ∈ N.args) (hcl : ¬ a.ClosedN D.np) : ¬ N.ArgsTypedH D e := by
  refine fun h => VEnv.not_hasArgs_of_not_closedN henv (hparams.ctxClosed henv) ha ?_ h.ty
  simpa using hcl

end VNestedOcc

/-! ### §3b The separating family, in general

One theorem, no witness block: at **any** occurrence record whose foreign block has at least one
parameter, the spine can be replaced by `.bvar D.np`s — `OccursN` survives, and the datum fails
at every environment of the step. -/

namespace VNestedOcc

/-- **THE FAMILY.**  `looseSpine N D` is `N` with its spine replaced by `N.decl.np` copies of the
first variable *past* the new block's parameter telescope. -/
def looseSpine (N : VNestedOcc) (D : VInductDecl') : VNestedOcc :=
  { N with args := List.replicate N.decl.np (.bvar D.np) }

/-- The replacement is `_nested`-free and of the right length, so `OccursN` transports. -/
theorem looseSpine_occursN {N : VNestedOcc} {env : VEnv} (h : N.OccursN env)
    (D : VInductDecl') : (N.looseSpine D).OccursN env :=
  h.setArgs (by simp) (by
    intro a ha; rw [List.eq_of_mem_replicate ha]; trivial)

/-- **…and the datum fails there.**  `hnp` is the only non-degeneracy needed: the foreign block
must have a parameter, or the spine is empty and there is nothing to be unscoped. -/
theorem looseSpine_not_argsTypedH {N : VNestedOcc} {D : VInductDecl'} {e : VEnv}
    (hnp : 0 < N.decl.np) (henv : e.Ordered)
    (hparams : OnCtx D.params.reverse (e.IsType D.uvars)) :
    ¬ (N.looseSpine D).ArgsTypedH D e := by
  refine not_argsTypedH_of_not_closedN henv hparams
    (a := .bvar D.np) ?_ (by simp [VExpr.ClosedN])
  exact List.mem_replicate.2 ⟨by omega, rfl⟩

end VNestedOcc

/-! ### §3c What each candidate actually constrains — measured

The brief's candidate list was `VNestedOcc`, the `Occurs`/`OccursN` family, `Faithful`'s clauses
and the `TrIndDeclN` data.  Measured against the *scope* of the presented spine:

| datum | sees the spine? | measured by |
| --- | --- | --- |
| `VNestedOcc` itself | its length only | `Occurs.setArgs` (§3a) |
| `Occurs` | length only | `Occurs.setArgs` |
| `OccursN` | length + `NoConstIn IsNestedName` — **no scope** | `OccursN.setArgs` |
| `KFresh` | + `NoConsts K` — **no scope** | `KFresh.setArgs` below |
| `Faithful.ty_agree` | **no** (when the split body is closed) | `faithful_ty_agree_setArgs` below |
| `Faithful.ctors_complete` | **no** — names and levels only | `faithful_ctors_complete_setArgs` |
| `Faithful.ctor_agree` | **yes**, syntactically | not transported; see below |
| `Built.member` | **yes**, syntactically | not transported; see below |
| `TrIndDeclN.trCtors` | **yes**, syntactically (`TrExprS` of `C.typeR D R j`) | read off, §3d |

The three "yes" rows are all *syntactic*: they pin the spine by an equation between expressions,
never by a judgement.  §2 is what makes that decisive — a bundle that holds of an unscoped spine
cannot yield `hargs`, and a bundle that pins the spine into a *stored type* still holds of an
unscoped spine, because a stored type has no scope obligation of its own (the companion member's
type is `instAt`, and `instAt_indep_of_tyArgs` is exactly the observation that it may not read the
spine at all).  Reaching the "yes" rows' own separating witness needs a whole re-spined block, and
that is **not** done here: those three rows are read off their definitions and labelled as such. -/

namespace VInductDecl'

/-- **`KFresh` is blind to the spine's scope**: its spine clause is `VExpr.NoConsts K`, and a de
Bruijn variable mentions no constant. -/
theorem KFresh.setArgs {D : VInductDecl'} {K : List Name} {env : VEnv}
    {occ : Nat → VNestedOcc} (h : D.KFresh K env occ) {as : Nat → List VExpr}
    (hn : ∀ (j : Nat), ∀ a ∈ as j, VExpr.NoConsts K a) :
    D.KFresh K env (fun j => { occ j with args := as j }) :=
  { h with argsNoK := fun j _ _ _ a ha => hn j a ha }

end VInductDecl'

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {env : VEnv} {npJ : Nat → Nat}

/-- **`Faithful.ty_agree` transports to an arbitrary spine** whenever the presented head's split
body is closed — `instAt_indep_of_tyArgs` lifted from `instAt` to the clause that quantifies over
it.  This is the general form of the brief's lower bound: it is not merely that `instAt` can ignore
the spine, it is that `ty_agree` then holds of **every** spine, unscoped ones included. -/
theorem faithful_ty_agree_setArgs (hfa : R.Faithful D env K npJ) {as : Nat → List VExpr}
    (hcl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
        (splitPis (npJ j) (ci.type.instL (R.tyLvls j))).2.ClosedN 0) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∃ ci : VConstant,
        env.constants (({R with tyArgs := as} : VIndRestore).tyName j) = some ci ∧
        ci.uvars = (({R with tyArgs := as} : VIndRestore).tyLvls j).length ∧
        ({R with tyArgs := as} : VIndRestore).instAt D (npJ j) j ci.type = T.type := by
  intro j T hT hK
  obtain ⟨ci, hci, huv, heq⟩ := hfa.ty_agree j T hT hK
  refine ⟨ci, hci, huv, ?_⟩
  rw [instAt_indep_of_tyArgs (hcl j T hT hK ci hci) ({R with tyArgs := as} : VIndRestore) rfl,
    ← heq, instAt_indep_of_tyArgs (hcl j T hT hK ci hci) R rfl]

/-- **…and `ctors_complete` transports unconditionally**: it mentions only `R.tyName`,
`R.ctorName` and `npJ`. -/
theorem faithful_ctors_complete_setArgs (hfa : R.Faithful D env K npJ) (as : Nat → List VExpr) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∃ (D₀ : VInductDecl') (j₀ : Nat) (T₀ : VIndType),
        D₀.Declared env ∧ D₀.types[j₀]? = some T₀ ∧
        T₀.name = ({R with tyArgs := as} : VIndRestore).tyName j ∧ npJ j = D₀.np ∧
        T.ctors.map (fun C => ({R with tyArgs := as} : VIndRestore).ctorName C.name)
          = T₀.ctors.map (·.name) :=
  hfa.ctors_complete

end VIndRestore

/-! ## §4 The clause the abstract theory is missing, and both traps

`hargs` needs a *scope* condition on the spine, §3 says no existing bundle supplies it, and the
implementation enforces it by an explicit `throw`.  The clause is below.

**Trap 1 — statability.**  It is stated over `R`, `D` and `K` and **nothing else**: no `occ`, no
`npJ`, no environment, and — unlike `SpineClause.lean` §5's `SpineHargsN` — **no staging premise**,
because closedness is not a judgement.  Its vocabulary is `VExpr.ClosedN`, `VIndRestore.tyArgs`,
`VInductDecl'.types`/`np` and `VIndType.name`, all of which `Verify/Environment/InductR.lean` has in
scope where `TrIndDeclN` is declared (it already writes `VExpr.splitPis` and
`D.types[j]? = some T` in that file's own probe field, and `ClosedN` is `Theory/VExpr.lean`).  So it
is statable both as a `TrIndDeclN` field and as a `Built`/`KFresh` field.

**Trap 2 — vacuity.**  Existentially closing it over the restoration is vacuous
(`exists_spineClosedC`), exactly as `∃ occ, SpineHargsK` is (`SpineClause.lean` §2a).  So it has to
be a field on the restoration the step already carries, not an existential.

**And it is free.**  §2 proves `SpineHargsC → SpineClosedC`.  So if the flip takes
`SpineClause.lean` §4's measured `trSpine` field, the scope clause is *not* a second clause: the
flip's price stays **one**. -/

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {env e : VEnv}
  {occ : Nat → VNestedOcc}

/-- **THE SCOPE CLAUSE.**  Each companion member's presented spine mentions no variable beyond the
new block's parameter telescope.  This is `Add.lean`'s
"nested inductive datatypes parameters cannot contain local variables", stated abstractly. -/
def SpineClosedC (R : VIndRestore) (D : VInductDecl') (K : List Name) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ a ∈ R.tyArgs j, a.ClosedN D.np

/-- **The clause is FREE at the datum** — so the flip needs one clause, not two. -/
theorem spineClosedC_of_spineHargsC (henv : e.Ordered)
    (hparams : OnCtx D.params.reverse (e.IsType D.uvars))
    (hB : D.Built R K env occ) (hS : R.SpineHargsC D K env e) : R.SpineClosedC D K :=
  spineHargsC_closedN henv hparams hB hS

/-- **…and it is NECESSARY**: fail it and the datum is false, at every `Ordered` environment. -/
theorem not_spineHargsC_of_not_spineClosedC (henv : e.Ordered)
    (hparams : OnCtx D.params.reverse (e.IsType D.uvars))
    (hB : D.Built R K env occ) (hn : ¬ R.SpineClosedC D K) : ¬ R.SpineHargsC D K env e :=
  fun hS => hn (spineClosedC_of_spineHargsC henv hparams hB hS)

/-- **THE EXISTENTIAL FORM IS VACUOUS**, for every block and every companion list: the empty
presentation satisfies it.  So `SpineClosedC` is a field on the step's own restoration or it is
nothing — the same trap `VInductDecl'.exists_spineHargsK` records for the `occ` form of the
datum. -/
theorem exists_spineClosedC (D : VInductDecl') (K : List Name) :
    ∃ R : VIndRestore, R.SpineClosedC D K :=
  ⟨⟨fun _ => .anonymous, fun _ => [], fun _ => [], id, id⟩, by
    intro _ _ _ _ a ha; simp at ha⟩

end VIndRestore

/-! ## §5 The witness: both halves at `ntreeAux`, arity 0, through the general theorems

`ntreeAux` — `NTree α` with a `List (NTree α)` field, `uvars = 1`, `params = [Type u]`,
`np = 1`, the block Lean's own kernel runs the nested elimination on.

The value of this theorem is the **route**: every conjunct is a general theorem of §2/§3 applied to
the block, never a block-specific computation.  In particular the two `ClosedN` conjuncts are *not*
`decide`d — they come from the datum by `spineHargsC_closedN`, which is the point of §2.

`ntreeAux_spineHargsC` (`SpineClause.lean` §6b) supplies the datum; everything after it is mine. -/

namespace InductiveDeclExamples

/-- **THE WITNESS.**  At `ntreeAux`, existentially closed:

1. the staging, and §1's datum at `AddInductStagesR`'s first stage (`SpineClause.lean` §6b);
2. §4's scope clause — **by §2's general route**, not by computation;
3. `(R.csubstTy D K).Closed` — by §2b's general route, so the hypothesis
   `SpineClause.lean` §4's transport carries separately is *discharged* here;
4. the whole substitution well-formedness from the datum with that hypothesis gone
   (`csubstTy_WF_of_hargs`);
5. §3's separating family at the **real** occurrence `List (NTree α)`: the re-spined record still
   satisfies `OccursN` at the same environment, and the datum is false of it at the same
   environment. So `hargs` at this block is not a consequence of its occurrence record. -/
theorem ntreeAux_hargs_scope_witness :
    ∃ env₁ env₂ env₃ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some env₂ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some env₃ ∧
      ntreeRestore.SpineHargsC ntreeAux ntreeK env₁ env₃ ∧
      ntreeRestore.SpineClosedC ntreeAux ntreeK ∧
      (ntreeRestore.csubstTy ntreeAux ntreeK).Closed ∧
      (ntreeRestore.csubstTy ntreeAux ntreeK).WF env₂ env₃ ntreeAux.uvars ∧
      (listOcc.looseSpine ntreeAux).OccursN env₁ ∧
      ¬ (listOcc.looseSpine ntreeAux).ArgsTypedH ntreeAux env₃ := by
  obtain ⟨env₁, env₂, env₃, h, h₂, h₃, hS⟩ := ntreeAux_spineHargsC
  have henv₁ : env₁.Ordered := listEnv_ordered h
  have h₃' : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some env₃ := by
    rw [VEnv.addIndTypesC] at h₃; exact h₃
  have henv₃ : env₃.Ordered :=
    VEnv.addConstList_ordered henv₁ (VEnv.addInductR_typeConstsC_wf ntreeAux_WF') h₃'
  have hB := ntreeAux_built h
  refine ⟨env₁, env₂, env₃, h, h₂, h₃, hS,
    VIndRestore.spineClosedC_of_spineHargsC henv₃ ntreeAux_params_WF hB hS,
    VIndRestore.csubstTy_closed_of_spineHargsC henv₃ henv₁ ntreeAux_WF'
      ntreeAux_params_WF hB hS,
    VIndRestore.csubstTy_WF_of_hargs hB hS (VEnv.addConstList_le h₃') henv₁ henv₃ ntreeAux_WF'
      (VIndRestore.csubstTy_freshIn h₂) h₂ h₃ ntreeAux_tyLvls_wf,
    VNestedOcc.looseSpine_occursN (listOcc_occurs h) ntreeAux,
    VNestedOcc.looseSpine_not_argsTypedH (by decide) henv₃ ntreeAux_params_WF⟩

/-! ### §5a Non-degeneracy of the witness, `decide`-checked

Three ways §5 could be uninteresting, all excluded. -/

/-- The **foreign** block's parameter count is positive — the one non-degeneracy
`looseSpine_not_argsTypedH` needs, and the reason §5's separating spine is not `[]`.
(`InductiveDeclExamples.ntree_np_pos`, `HargsShared.lean` §9b, is the *new* block's `np`; this is
`List`'s.) -/
theorem listOcc_decl_np_pos : 0 < listOcc.decl.np := by decide

/-- The spine genuinely mentions a parameter: the **strengthening** of §4's clause to `ClosedN 0`
is FALSE at this block, **at the companion member**.  So the clause is not the trivial
"closed spine" condition.

Not a duplicate of `ntree_not_tyArgs_closed0` (`Theory/Inductive/NestedRules.lean`), which refutes
the *unguarded* `hcl0` at `j = 0` — the block's **own** member, where `VIndRestore.OwnId` forces
`R.tyArgs 0 = bvars 0 D.np` and the refutation is about the identity presentation.  This one is at
`j = 1`, the member in `K`, so it is about the *presented* spine. -/
theorem ntree_not_spineClosed_zero :
    ¬ ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK →
      ∀ a ∈ ntreeRestore.tyArgs j, a.ClosedN 0 := by
  intro h
  have h1 := h 1 _
    (show ntreeAux.types[1]? = some (listOcc.member ntreeAux.header ntreeRestore) from rfl)
    (by decide) (.app (.const ``NTree [.param 0]) (.bvar 0))
    (by rw [show ntreeRestore.tyArgs 1
        = [VExpr.app (.const ``NTree [.param 0]) (.bvar 0)] from rfl]; exact List.Mem.head _)
  exact absurd (show (0 : Nat) < 0 from h1.2) (Nat.lt_irrefl 0)

/-- …and the separating spine really is different from the real one, so §5's last two conjuncts
are not about the same record. -/
theorem listOcc_looseSpine_ne : (listOcc.looseSpine ntreeAux).args ≠ listOcc.args := by decide

end InductiveDeclExamples

end Lean4Lean

/-! ## §6 Grading: hole-freeness, per declaration

Every line below is hole-freeness and nothing else (`docs/vacuity-ledger.md` §0); inhabitation is
§5, and non-degeneracy §5a.  Names read off this file's own `namespace` lines. -/

#print axioms Lean4Lean.VIndRestore.spineHargsC_iff_hargsAt
#print axioms Lean4Lean.VIndRestore.tyVal_hasType_of_spineHargsC
#print axioms Lean4Lean.VEnv.HasArgs.closedN
#print axioms Lean4Lean.VEnv.not_hasArgs_of_not_closedN
#print axioms Lean4Lean.VIndRestore.csubstTy_closed_guarded
#print axioms Lean4Lean.VIndRestore.spineHargsC_closedN
#print axioms Lean4Lean.VIndRestore.csubstTy_closed_of_spineHargsC
#print axioms Lean4Lean.VIndRestore.csubstTy_WF_of_hargs
#print axioms Lean4Lean.VNestedOcc.Occurs.setArgs
#print axioms Lean4Lean.VNestedOcc.OccursN.setArgs
#print axioms Lean4Lean.VNestedOcc.not_argsTypedH_of_not_closedN
#print axioms Lean4Lean.VNestedOcc.looseSpine_occursN
#print axioms Lean4Lean.VNestedOcc.looseSpine_not_argsTypedH
#print axioms Lean4Lean.VInductDecl'.KFresh.setArgs
#print axioms Lean4Lean.VIndRestore.faithful_ty_agree_setArgs
#print axioms Lean4Lean.VIndRestore.faithful_ctors_complete_setArgs
#print axioms Lean4Lean.VIndRestore.spineClosedC_of_spineHargsC
#print axioms Lean4Lean.VIndRestore.not_spineHargsC_of_not_spineClosedC
#print axioms Lean4Lean.VIndRestore.exists_spineClosedC
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_hargs_scope_witness
#print axioms Lean4Lean.InductiveDeclExamples.listOcc_decl_np_pos
#print axioms Lean4Lean.InductiveDeclExamples.ntree_not_spineClosed_zero
#print axioms Lean4Lean.InductiveDeclExamples.listOcc_looseSpine_ne
