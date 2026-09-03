import Lean4Lean.Theory.Inductive.HargsShared
import Lean4Lean.Verify.Inductive.SpineTransfer
import Lean4Lean.Verify.Inductive.NestedOccData
import Lean4Lean.Verify.Inductive.OccArgsTyping

/-!
# Supplying `VNestedOcc.ArgsTypedH` on the `Verify/` side

`Theory/Inductive/HargsShared.lean` reduced the four remaining `hargs`/`hbody` sites of the
nested `AddInduct` flip to **one shared datum**, and located its home: a clause on the
occurrence record, `VNestedOcc.ArgsTypedH`, produced at every presented head by
`VInductDecl'.Built.spineTyped_ty` / `_ctor`.  Its handoff (`docs/handoff-hargsshared.md` §4b)
named the discharge site — `ElimNestedInductive.Result.RestoreData` / `TrIndDeclN`, on this side
of the layering boundary — and could not reach it, `HargsShared.lean` being under `Theory/`.

This file reaches it.  The headline is **not** the measurement I expected to report: the clause is
independent of every *name*-discipline bundle on this side (§3), but it is **derivable from
`D.WF`** — the third source `docs/handoff-hargsshared.md` §4a ruled out — at **both** nested blocks
in the tree, with every hypothesis discharged (§10).

What is established, in descending order of value:

* **§10** two closed theorems, no free variables and nothing hypothesised: at `nfnAux` (`NFn`
  nesting `PFn`) and at `ntreeAux` (`NTree α` with a `List (NTree α)` field, `np = 1`, the block
  Lean's own kernel runs the nested elimination on), the clause holds, the **shared datum** holds
  at the presented type head, and at `nfnAux` **§8.7's `val` clause** holds with it.
* **§5/§7** why: `docs/handoff-hargsshared.md` §4a's "`D.WF venv` **cannot** supply the datum
  either" is **wrong**, and its cited authority (`instAt_indep_of_tyArgs`) is about a different
  clause — the companion member's stored *type*.  The companion member's **constructors** are in
  `D.types`, so `VInductDecl'.WF.ctors` sees the substituted field types, and the recursive field
  that nesting manufactures carries the datum in `VIndField.WF.pos`.  §4a's elimination argument
  ("by elimination the source is `TrIndDeclN`") does not go through.
* **§2** the clause in `Verify/`-side form (`VInductDecl'.ArgsTypedK`) with the consumers wired to
  it — including **§8.7's `val` clause discharged in general, hole-free and with no
  `HasArgs.of_mkApp`**: `ArgsTypedH.ty` *is* `tyVal_hasType_of_hargs`' `hargs`, once `Built`'s
  three name/level/spine equations and `Occurs.ty_const` are applied.
* **§3** the clause is **not derivable** from `RestoreData` + `OccData`, and the two invariance
  theorems that show why are general: `OccData` does not mention the spine at all, `RestoreData`
  sees it through one environment-free name condition.  A junk-spine perturbation of the tree's own
  nested witness satisfies all twenty of their fields and refutes the clause at every environment
  of the step.
* **§4** joint inhabitation of the clause with `OccData`, `RestoreData`, `Built` and `Occurs` at one
  block, one `D`, one `R`, one `occ`, one environment — at `AddInductStagesR`'s **first stage**,
  which is the environment §8.7 wants.
* **§6** the boundary in general: **no** pre-block environment can carry the clause
  (`docs/handoff-hargsshared.md` §7 item 2's requested generalisation), plus the instance at the
  second witness.
* **§8** the clause is **one** datum, not two: §4b's "honest count" collapses under a *syntactic*
  telescope agreement that both witnesses satisfy, with no `HasArgs.congr_tele` (which a concurrent
  stream owns).
* **§9** the four coincidences §5/§7's route rests on, the environment mismatch that stops it
  composing in general, and the exact `TrIndDeclN` edit if the general route is wanted instead.

## What is NOT claimed

* **The flip is not made**, and the general discharge is not achieved: §9 says exactly what is
  missing.  The two `§10` theorems are inhabitation at two blocks, not a theorem about all blocks.
* `docs/handoff-hargsshared.md` §4a's own one-line theorem (`addInductStagesR_no_spineTyped`) is
  **not** landed.  §9 records the two things it costs — `Ordered` at the post-stage environment and
  a junk-spine `Expr`-side `TrConstant` witness — and note that §5 removes the *use* §4a made of
  it: its verdict on `AddInductStagesR` may well be right, but the elimination argument it fed is
  refuted independently.
* No field is added to `TrIndDeclN`, `RestoreData` or `OccData` — those live in files this stream
  does not own.
* Hole-freeness and inhabitation are graded separately throughout (`docs/vacuity-ledger.md` §0).
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkApp bvars instAll splitPis)

/-! ## §2 The clause, in `Verify/`-side form, and the four consumers

`VNestedOcc.ArgsTypedH` (`Theory/Inductive/HargsShared.lean` §8b) is a statement about **one**
occurrence.  What a `Verify/`-side bundle has to supply is the family, indexed the way
`RestoreData`/`OccData`/`Built` index theirs: over the companion members of `D`.  That is the
only content of the definition below; it exists so that "the obligation" has a name to be
refuted (§3), inhabited (§4) and produced from (§5). -/

/-- **THE `Verify/`-SIDE OBLIGATION.**  Every companion member's occurrence carries the spine
typing, in `HasArgs` form, at the environment `e`.

`HasArgs` form and not applied form, deliberately: `docs/handoff-hargsshared.md` §3c(ii)
measured that the applied form's route back (`VEnv.HasArgs.of_mkApp`) carries `sorryAx`, and that
using it here would be the **first** consumer of `PiInv` in the nested corner, which
`Theory/Inductive/NestedTele.lean` §T12/§T15/§T16 keep deliberately `PiInv`-free.  Every producer
and consumer in this file is on the `HasArgs` side of that line. -/
def VInductDecl'.ArgsTypedK (D : VInductDecl') (K : List Name) (e : VEnv)
    (occ : Nat → VNestedOcc) : Prop :=
  ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).ArgsTypedH D e

namespace VInductDecl'

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e : VEnv}
  {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}

/-- The applied form of the family, hole-free, from `Built.occurs`. -/
theorem ArgsTypedK.toArgsTyped (hS : D.ArgsTypedK K e occ) (hB : D.Built R K env occ)
    (hle : env ≤ e) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).ArgsTyped D e :=
  fun j T hT hK => (hS j T hT hK).toArgsTyped (hB.occurs j T hT hK).toOccurs hle

/-- **THE SHARED DATUM AT THE TYPE HEAD**, from the `Verify/`-side obligation. -/
theorem Built.spineTyped_ty_of_argsTypedK (hB : D.Built R K env occ)
    (hS : D.ArgsTypedK K e occ) (hle : env ≤ e)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    R.SpineTyped D e (R.tyName j) j :=
  hB.spineTyped_ty (hS.toArgsTyped hB hle) hT hK

/-- **…AND AT EVERY CONSTRUCTOR HEAD.** -/
theorem Built.spineTyped_ctor_of_argsTypedK (hB : D.Built R K env occ)
    (hS : D.ArgsTypedK K e occ) (hle : env ≤ e)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) {C : VIndCtor} (hC : C ∈ T.ctors) :
    R.SpineTyped D e (R.ctorName C.name) j :=
  hB.spineTyped_ctor (hS.toArgsTyped hB hle) hT hK hC

end VInductDecl'

/-! ### §2.1 §8.7's `val` clause, discharged directly and hole-free

The other three sites go through the *applied* form (`SpineTypedAt`), which `§2` above delivers.
§8.7 does not have to: `VIndRestore.tyVal_hasType_of_hargs`
(`Theory/Inductive/HargsShared.lean` §6) takes `hargs` in **`HasArgs` form**, and that is
`ArgsTypedH.ty` on the nose once three of `Built`'s equations and `Occurs.ty_const` are used to
identify the telescope:

* `Built.tyName`  : `R.tyName j = (occ j).tyName`,
* `Built.tyLvls`  : `R.tyLvls j = (occ j).lvls`,
* `Built.tyArgs`  : `R.tyArgs j = (occ j).args`,
* `Occurs.ty_const` : the looked-up `ci` **is** `⟨(occ j).decl.uvars, (occ j).src.type⟩`.

So `R.declTele ci ((occ j).decl.np) j = (splitPis (occ j).decl.np ((occ j).src.type.instL (occ j).lvls)).1`,
which is exactly the telescope `ArgsTypedH.ty` is stated against.  No `of_mkApp`, no `e.WF`, no
length side condition. -/

namespace VIndRestore

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e₂ : VEnv}
  {occ : Nat → VNestedOcc} {j : Nat} {T : VIndType}

/-- **`hargs` in the exact shape `tyVal_hasType_of_hargs` consumes it**, from the clause. -/
theorem hargs_of_argsTypedK (hB : D.Built R K env occ) (hS : D.ArgsTypedK K env₂ occ)
    (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
      env₂.HasArgs D.uvars D.params.reverse
        (R.declTele ci ((occ j).decl.np) j) (R.tyArgs j) := by
  intro ci hci
  have ho := (hB.occurs j T hT hK).toOccurs
  rw [hB.tyName j T hT hK] at hci
  cases Option.some.inj (ho.ty_const.symm.trans hci)
  show env₂.HasArgs D.uvars D.params.reverse
    (splitPis ((occ j).decl.np) ((occ j).src.type.instL (R.tyLvls j))).1 (R.tyArgs j)
  rw [hB.tyLvls j T hT hK, hB.tyArgs j T hT hK]
  exact (hS j T hT hK).ty

/-- **§8.7's `val` CLAUSE, FROM THE `Verify/`-SIDE OBLIGATION — HOLE-FREE.**  One of the four
sites of the flip, closed outright modulo the clause. -/
theorem tyVal_hasType_of_argsTypedK (hB : D.Built R K env occ) (hS : D.ArgsTypedK K env₂ occ)
    (hfa : R.Faithful D env K (fun j => (occ j).decl.np)) (hle : env ≤ env₂)
    (hparams : OnCtx D.params.reverse (env₂.IsType D.uvars))
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars) :
    env₂.HasType D.uvars [] (R.tyVal D j) T.type :=
  tyVal_hasType_of_hargs hfa hle hparams hT hK hlvl (hargs_of_argsTypedK hB hS hT hK)

/-- …and with `Faithful` read off `Built` rather than assumed separately. -/
theorem tyVal_hasType_of_argsTypedK' (hB : D.Built R K env occ) (hS : D.ArgsTypedK K env₂ occ)
    (hle : env ≤ env₂) (hparams : OnCtx D.params.reverse (env₂.IsType D.uvars))
    (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars) :
    env₂.HasType D.uvars [] (R.tyVal D j) T.type :=
  tyVal_hasType_of_argsTypedK hB hS hB.toFaithful hle hparams hT hK hlvl

end VIndRestore

#print axioms Lean4Lean.VInductDecl'.ArgsTypedK.toArgsTyped
#print axioms Lean4Lean.VInductDecl'.Built.spineTyped_ty_of_argsTypedK
#print axioms Lean4Lean.VInductDecl'.Built.spineTyped_ctor_of_argsTypedK
#print axioms Lean4Lean.VIndRestore.hargs_of_argsTypedK
#print axioms Lean4Lean.VIndRestore.tyVal_hasType_of_argsTypedK
#print axioms Lean4Lean.VIndRestore.tyVal_hasType_of_argsTypedK'

/-! ## §3 The clause is not derivable from `RestoreData` + `OccData`

Two invariance theorems, both general and both one line, say exactly how much of the spine those
two bundles can see:

* `OccData` sees **nothing**: none of its six fields mentions `VNestedOcc.args`, so it survives
  an arbitrary replacement of every occurrence's spine.
* `RestoreData` sees the spine through **one** field, `args`, and that field is the
  environment-free name condition `VExpr.NoConstIn IsNestedName`
  (`Verify/Inductive/OccArgsTyping.lean` is the round that put it there, and §4 of that file is
  the proof that no *environment*-indexed spelling could have gone there).

So a spine of undeclared junk that happens not to be `_nested`-prefixed passes both bundles, and
§3.2 refutes the clause at it — at **every** environment that does not declare the junk name,
which is every environment of the step. -/

namespace ElimNestedInductive.Result

variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Name}
  {occ : Nat → VNestedOcc}

/-- **`OccData` does not see the nested spine at all.**  Measured, not read off: the statement
below is accepted with the six fields transported verbatim, which is only possible because none
of them mentions `args`. -/
theorem OccData.setArgs (h : r.OccData types occ) (as : Nat → List VExpr) :
    r.OccData types (fun j => { occ j with args := as j }) where
  auxName := h.auxName
  auxHead := h.auxHead
  ctorName := h.ctorName
  srcCtorPrefix := h.srcCtorPrefix
  auxCtors := h.auxCtors
  ctorNodup := h.ctorNodup

/-- **`RestoreData` sees the spine through exactly one field**, and that field is a name
condition with no environment in it. -/
theorem RestoreData.setArgs {as as' : Nat → List VExpr} (h : r.RestoreData types D K as)
    (hj : ∀ j, ∀ a ∈ as' j, a.NoConstIn IsNestedName) : r.RestoreData types D K as' :=
  { h with args := hj }

end ElimNestedInductive.Result

/-! ### §3.1 The junk spine, at the tree's own nested witness

`NFn` nesting `PFn`, the block `NestedRestoreWit.lean` builds the checker's `Result` for.  The
perturbation replaces the occurrence's spine `[NFn]` by `[Junk]`, `Junk` being a name no
environment of the step declares. -/

namespace NestedWit

open InductiveDeclExamples ElimNestedInductive

/-- The occurrence with an undeclared, non-reserved spine. -/
def pfnOccJunkArgs : VNestedOcc := { pfnOcc with args := [.const `Junk []] }

/-- …and the abstract spine that matches it. -/
def nfnAsJunkArgs : Nat → List VExpr := fun _ => [.const `Junk []]

/-- The spine is not `_nested`-prefixed, so it passes the one field `RestoreData` checks. -/
theorem nfnAsJunkArgs_noNested : ∀ j, ∀ a ∈ nfnAsJunkArgs j, a.NoConstIn IsNestedName := by
  intro j a ha
  simp only [nfnAsJunkArgs, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha; decide

/-- **All fourteen `RestoreData` fields hold of the junk spine.** -/
theorem nfnResult_restoreData_junkArgs :
    nfnResult.RestoreData [nfnIndType] nfnAux nfnK nfnAsJunkArgs :=
  nfnResult_restoreData.setArgs nfnAsJunkArgs_noNested

/-- **…and all six `OccData` fields.** -/
theorem nfnResult_occData_junkArgs :
    nfnResult.OccData [nfnIndType] (fun _ => pfnOccJunkArgs) :=
  nfnResult_occData.setArgs (fun _ => [.const `Junk []])

/-- The two agree, as `Built.tyArgs` requires. -/
theorem nfnAsJunkArgs_eq : ∀ j, nfnAsJunkArgs j = (pfnOccJunkArgs).args := fun _ => rfl

end NestedWit

/-! ### §3.2 …and the clause is false at it, at every environment of the step -/

namespace NestedWit

open InductiveDeclExamples ElimNestedInductive

/-- The junk spine's single argument is a constant, so `VExpr.ConstsIn` reduces to a lookup. -/
theorem pfnOccJunkArgs_not_constsIn {e : VEnv} (he : ¬ e.contains `Junk) :
    ¬ ∀ a ∈ pfnOccJunkArgs.args, VExpr.ConstsIn a e.contains := by
  intro h
  exact he (h (.const `Junk []) (by decide))

/-- **THE CLAUSE IS REFUTED AT THE JUNK SPINE**, at every environment that does not declare
`Junk` — which is every environment of the `NFn` step, since only `NFn`, `NFn.node`, `NFn.rec`,
`NFn.rec_1` and (below) `_nested.PFn_1` are added to it.

The only environment hypotheses are the ones `VEnv.IsDefEq.constsIn` needs, and `nfnAux.params`
is empty so the context side condition is `trivial`. -/
theorem pfnOccJunkArgs_not_argsTypedH {e : VEnv} (henv : e.Ordered) (he : ¬ e.contains `Junk) :
    ¬ pfnOccJunkArgs.ArgsTypedH nfnAux e := by
  intro h
  refine pfnOccJunkArgs_not_constsIn he fun a ha => ?_
  have hty : (splitPis pfnOccJunkArgs.decl.np
      (pfnOccJunkArgs.src.type.instL pfnOccJunkArgs.lvls)).1
      = [VExpr.sort (.succ .zero)] := by decide
  have h1 := h.ty
  rw [hty, show nfnAux.uvars = 0 from rfl,
    show nfnAux.params.reverse = ([] : List VExpr) from rfl,
    show pfnOccJunkArgs.args = [VExpr.const `Junk []] from rfl] at h1
  cases h1 with
  | cons hA _ =>
    simp only [show pfnOccJunkArgs.args = [VExpr.const `Junk []] from rfl,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact (hA.constsIn henv.constsIn trivial).1

/-- **THE MEASUREMENT.**  `RestoreData` and `OccData` hold, the spine agreement `Built.tyArgs`
needs holds, and the clause fails — so no derivation of `VInductDecl'.ArgsTypedK` from those two
bundles exists, and adding it to either as a *derived* field is impossible. -/
theorem argsTypedK_independent_of_restoreData_occData {e : VEnv}
    (henv : e.Ordered) (he : ¬ e.contains `Junk) :
    nfnResult.RestoreData [nfnIndType] nfnAux nfnK nfnAsJunkArgs ∧
      nfnResult.OccData [nfnIndType] (fun _ => pfnOccJunkArgs) ∧
      (∀ j, nfnAsJunkArgs j = (pfnOccJunkArgs).args) ∧
      ¬ nfnAux.ArgsTypedK nfnK e (fun _ => pfnOccJunkArgs) :=
  ⟨nfnResult_restoreData_junkArgs, nfnResult_occData_junkArgs, nfnAsJunkArgs_eq,
    fun hS => pfnOccJunkArgs_not_argsTypedH henv he
      (hS 1 _ rfl (by decide))⟩

end NestedWit

#print axioms Lean4Lean.ElimNestedInductive.Result.OccData.setArgs
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.setArgs
#print axioms Lean4Lean.NestedWit.nfnResult_restoreData_junkArgs
#print axioms Lean4Lean.NestedWit.nfnResult_occData_junkArgs
#print axioms Lean4Lean.NestedWit.pfnOccJunkArgs_not_argsTypedH
#print axioms Lean4Lean.NestedWit.argsTypedK_independent_of_restoreData_occData

/-! ## §4 Joint inhabitation, and the producers firing end to end

`docs/vacuity-ledger.md` row 205: check the hypothesis set is **jointly** inhabited, not each
hypothesis alone.  Everything below is at one block (`nfnAux`, `NFn` nesting `PFn`), one `D`, one
`K`, one `R` (`nfnRestore' = mkRestore …`, the restoration the *checker's* `Result` computes),
one `occ`, and one environment `F₁`.

The environment is the first stage of `AddInductStagesR`: `env₂` — where `PFn` is declared and
`NFn` is not — extended by `nfnAux.typeConstsC nfnK`, i.e. by the block's **non-companion** type
constants.  That is the earliest environment at which the clause can hold at all: §3.2's argument
applies verbatim to `env₂` itself with `NFn` in place of `Junk`
(`Verify/Inductive/OccArgsTyping.lean` §4.1 is that refutation, already in the tree), so the
clause is **false** one stage earlier.  This is `docs/handoff-hargsshared.md` §3c(i) at the second
witness. -/

namespace NestedWit

open InductiveDeclExamples ElimNestedInductive

/-- **The clause at this witness needs exactly one lookup.**  Both of `pfnOcc`'s telescopes —
`PFn`'s stored type's and `PFn.mk`'s — are `PFn`'s single parameter binder `Type`, and the spine
is `[NFn]`, so all three components of `ArgsTypedH` are the one judgement `NFn : Type`. -/
theorem pfnOcc_argsTypedH_of_hasType {e : VEnv}
    (hN : e.HasType 0 [] (.const ``NFn []) (.sort (.succ .zero))) :
    pfnOcc.ArgsTypedH nfnAux e := by
  have harg : e.HasArgs nfnAux.uvars nfnAux.params.reverse
      [VExpr.sort (.succ .zero)] pfnOcc.args := .cons hN .nil
  refine ⟨by decide, ?_, fun C hC => ?_⟩
  · rw [show (splitPis pfnOcc.decl.np (pfnOcc.src.type.instL pfnOcc.lvls)).1
      = [VExpr.sort (.succ .zero)] from by decide]
    exact harg
  · simp only [show pfnOcc.src.ctors = [pfnMk] from rfl, List.mem_cons, List.not_mem_nil,
      or_false] at hC
    subst hC
    rw [show (splitPis pfnOcc.decl.np ((pfnMk.type pfnOcc.decl pfnOcc.idx).instL
      pfnOcc.lvls)).1 = [VExpr.sort (.succ .zero)] from by decide]
    exact harg

/-- …and the lookup form, which is what a staged environment hands over. -/
theorem pfnOcc_argsTypedH_of_nfn {e : VEnv}
    (hNFn : e.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩) :
    pfnOcc.ArgsTypedH nfnAux e :=
  pfnOcc_argsTypedH_of_hasType (.const hNFn (by decide) rfl)

section
variable {env₂ F₁ : VEnv}
variable (h : VEnv.empty.addInduct' pfnDecl = some env₂)
variable (hF₁ : env₂.addConstList (nfnAux.typeConstsC nfnK) = some F₁)

include hF₁ in
theorem nfnF₁_nfn : F₁.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConstList_constants hF₁ (``NFn, ⟨0, .sort (.succ .zero)⟩) <| by
    rw [show nfnAux.typeConstsC nfnK
      = [(``NFn, (⟨0, .sort (.succ .zero)⟩ : VConstant))] from rfl]
    exact List.mem_cons_self

include hF₁ in
/-- **THE `Verify/`-SIDE OBLIGATION, INHABITED**, at the first stage of the step. -/
theorem nfnAux_argsTypedK : nfnAux.ArgsTypedK nfnK F₁ (fun _ => pfnOcc) :=
  fun _ _ _ _ => pfnOcc_argsTypedH_of_nfn (nfnF₁_nfn hF₁)

include h hF₁ in
/-- **END TO END AT THE TYPE HEAD**: `Built` (from the checker's `Result` via
`nfnAux_built'_of_blockK`) and the clause, at one block and one environment, run through §2's
producer.  This is the joint check. -/
theorem nfnAux_datum_ty :
    nfnRestore'.SpineTyped nfnAux F₁ (nfnRestore'.tyName 1) 1 :=
  (nfnAux_built'_of_blockK h).spineTyped_ty_of_argsTypedK (nfnAux_argsTypedK hF₁)
    (VEnv.addConstList_le hF₁)
    (show nfnAux.types[1]? = some (pfnOcc.member nfnAux.header nfnRestore') from rfl)
    (by decide)

include h hF₁ in
/-- **…AND AT THE CONSTRUCTOR HEAD**, through `Built.member` + `Built.ctorName_inv`. -/
theorem nfnAux_datum_ctor (C : VIndCtor)
    (hC : C ∈ (pfnOcc.member nfnAux.header nfnRestore').ctors) :
    nfnRestore'.SpineTyped nfnAux F₁ (nfnRestore'.ctorName C.name) 1 :=
  (nfnAux_built'_of_blockK h).spineTyped_ctor_of_argsTypedK (nfnAux_argsTypedK hF₁)
    (VEnv.addConstList_le hF₁)
    (show nfnAux.types[1]? = some (pfnOcc.member nfnAux.header nfnRestore') from rfl)
    (by decide) hC

include h hF₁ in
/-- **§8.7's `val` CLAUSE, FIRING AT THE WITNESS.**  Not merely stated: `tyVal_hasType_of_hargs`
consumed, the clause supplying its `hargs`, `Built` supplying its `Faithful`, at the block the
kernel really runs the nested elimination on.  One of the flip's four sites, closed at a real
witness. -/
theorem nfnAux_tyVal_hasType :
    F₁.HasType nfnAux.uvars [] (nfnRestore'.tyVal nfnAux 1)
      (pfnOcc.member nfnAux.header nfnRestore').type :=
  VIndRestore.tyVal_hasType_of_argsTypedK' (nfnAux_built'_of_blockK h) (nfnAux_argsTypedK hF₁)
    (VEnv.addConstList_le hF₁) (by exact trivial)
    (show nfnAux.types[1]? = some (pfnOcc.member nfnAux.header nfnRestore') from rfl)
    (by decide) (by decide)

end

/-- The two staging equations, satisfied. -/
theorem nfnAux_stage₁_exists :
    ∃ env₂ F₁ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addConstList (nfnAux.typeConstsC nfnK) = some F₁ := by
  obtain ⟨env₂, h⟩ : ∃ e, VEnv.empty.addInduct' pfnDecl = some e := ⟨_, rfl⟩
  have hfresh : ∀ n ∈ [``NFn], env₂.constants n = none := by
    intro n hn
    rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
    rfl
  obtain ⟨F₁, hF₁⟩ : ∃ e, env₂.addConstList (nfnAux.typeConstsC nfnK) = some e :=
    VEnv.addConstList_eq_some_iff.2
      ⟨fun n hn => hfresh n (by revert hn; revert n; decide), by decide⟩
  exact ⟨env₂, F₁, h, hF₁⟩

/-- …and with the staging supplied rather than assumed, so the hypothesis set is inhabited with
no equations left open: **one** block, **one** `D`, **one** `K`, **one** `R`, **one** `occ`,
**one** environment, and all six statements at once. -/
theorem nfnAux_argsTypedK_inhabited :
    ∃ env₂ F₁ : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addConstList (nfnAux.typeConstsC nfnK) = some F₁ ∧
      nfnAux.ArgsTypedK nfnK F₁ (fun _ => pfnOcc) ∧
      nfnAux.Built nfnRestore' nfnK env₂ (fun _ => pfnOcc) ∧
      nfnResult.RestoreData [nfnIndType] nfnAux nfnK nfnAs ∧
      nfnResult.OccData [nfnIndType] (fun _ => pfnOcc) ∧
      nfnRestore'.SpineTyped nfnAux F₁ (nfnRestore'.tyName 1) 1 := by
  obtain ⟨env₂, F₁, h, hF₁⟩ := nfnAux_stage₁_exists
  exact ⟨env₂, F₁, h, hF₁, nfnAux_argsTypedK hF₁, nfnAux_built'_of_blockK h,
    nfnResult_restoreData, nfnResult_occData, nfnAux_datum_ty h hF₁⟩

/-! ### §4.1 Non-degeneracy of the witness -/

/-- The nested spine is not empty, so the `HasArgs` is not `.nil`. -/
theorem pfnOcc_args_ne_nil : pfnOcc.args ≠ [] := by decide

/-- The presented head is a **foreign** constant, not the block's own member. -/
theorem pfnOcc_tyName_ne_own :
    pfnOcc.tyName ≠ (nfnAux.types.getD 1 default).name := by decide

/-- The presentation is not the identity one: the spine is not the parameter run. -/
theorem pfnOcc_args_ne_bvars : pfnOcc.args ≠ VExpr.bvars 0 nfnAux.np := by decide

/-- …and the companion index really is in `K`, so §4's producers are not fired vacuously. -/
theorem nfnK_companion : (nfnAux.types.getD 1 default).name ∈ nfnK := by decide

/-- **The datum really is at the foreign head.**  `nfnRestore'` is `mkRestore`, so its presented
head at the companion index is whatever `Result.presentedHead` computes; it computes `PFn`, the
constant the *history* declared — not junk and not the block's own member. -/
theorem nfnRestore'_tyName_one : nfnRestore'.tyName 1 = ``PFn := by decide

/-- …applied to the block's own member, which is why the datum cannot live at the pre-block
environment. -/
theorem nfnRestore'_tyArgs_one : nfnRestore'.tyArgs 1 = [.const ``NFn []] := by decide

end NestedWit

#print axioms Lean4Lean.NestedWit.pfnOcc_argsTypedH_of_hasType
#print axioms Lean4Lean.NestedWit.pfnOcc_argsTypedH_of_nfn
#print axioms Lean4Lean.NestedWit.nfnAux_argsTypedK
#print axioms Lean4Lean.NestedWit.nfnAux_datum_ty
#print axioms Lean4Lean.NestedWit.nfnAux_datum_ctor
#print axioms Lean4Lean.NestedWit.nfnAux_tyVal_hasType
#print axioms Lean4Lean.NestedWit.nfnAux_stage₁_exists
#print axioms Lean4Lean.NestedWit.nfnAux_argsTypedK_inhabited
#print axioms Lean4Lean.NestedWit.pfnOcc_args_ne_nil
#print axioms Lean4Lean.NestedWit.pfnOcc_tyName_ne_own
#print axioms Lean4Lean.NestedWit.pfnOcc_args_ne_bvars
#print axioms Lean4Lean.NestedWit.nfnK_companion
#print axioms Lean4Lean.NestedWit.nfnRestore'_tyName_one
#print axioms Lean4Lean.NestedWit.nfnRestore'_tyArgs_one

/-! ## §5 A correction: `D.WF` **does** see the spine, through the companion's constructors

`docs/handoff-hargsshared.md` §4a says, of the three things `InductStepNested` carries besides
`AddInductStagesR`:

> `D.WF venv` **cannot** supply the datum either, and that is already a theorem:
> `VIndRestore.instAt_indep_of_tyArgs` … shows the companion member's stored type is blind to
> the presented spine when the split body is closed.

The cited theorem is right and the conclusion drawn from it is too strong.  `instAt_indep_of_tyArgs`
is about `VNestedOcc.instAt`, i.e. about the companion member's **stored type** — and that really
is blind: `List`'s type is `Type u → Type u`, so `(splitPis 1 …).2` is the closed term `Type u`
and `instAll` throws the spine away.  But the companion member is a member of `D.types`, so
`VInductDecl'.WF.ctors` also runs on **its constructors**, and their field types are
`VExpr.instAll (F₀.type.instL N.lvls) N.args k` — the spine substituted into the *foreign* block's
field types.  Those are not blind to it at all.

§5.1 is the general extraction, §5.2 is the datum coming out of `D.WF` at the tree's nested
witness, and §5.3 says exactly what stops this from being the general discharge. -/

namespace VInductDecl'

/-- **The recursive-field clause of `D.WF`, extracted.**  `VIndField.WF.pos`'s `some` branch,
sixth conjunct, with the `match` discharged.  General: any member, any constructor, any field. -/
theorem WF.recField_canonResult {D : VInductDecl'} {env env₁ : VEnv}
    (hwf : D.WF env) (het : env.addIndTypes D = some env₁)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) {C : VIndCtor} (hC : C ∈ T.ctors)
    {i : Nat} {F : VIndField} (hF : C.fields[i]? = some F) {r : VIndRecArg}
    (hr : F.recArg = some r) :
    env₁.HasType D.uvars
      (r.binders.reverse ++ (((C.fields.take i).map (·.type)).reverse ++ D.params.reverse))
      (r.canonResult D i) (.sort D.lvl) := by
  have hp := ((hwf.ctors env₁ het j T hT C hC).fields i F hF).pos
  rw [hr] at hp
  exact hp.2.2.2.2.2.1

end VInductDecl'

/-! ### §5.2 …and the datum, from `D.WF`, at the nested witness

At `nfnAux` the companion member is `_nested.PFn_1`, its one constructor is `pfnAuxMk`, and
`pfnAuxMk`'s **first** field is `PFn.mk`'s first field `.bvar 0` — `PFn`'s parameter — with the
spine substituted for it.  The spine is `[NFn]`, so that field's type *is* the spine's only
argument, the recogniser fires on it (this is the field nesting creates), and `pos`'s sixth
conjunct is `NFn : Type` in the empty context: exactly `pfnOcc_argsTypedH_of_hasType`'s
hypothesis.

The environment is `env.addIndTypes nfnAux`, which is where `WF.ctors` is staged. -/

namespace NestedWit

open InductiveDeclExamples ElimNestedInductive

/-- `pfnAuxMk`'s first field is recursive into member 0 with no binders — the field the nesting
manufactures.  Read off the construction: `decide`. -/
theorem pfnAuxMk_field0 :
    pfnAuxMk.fields[0]? =
      some (⟨.const ``NFn [], .succ .zero, some ⟨[], 0, []⟩⟩ : VIndField) := rfl

/-- …and its `canonResult` is the spine's only argument. -/
theorem pfnAuxMk_field0_canonResult :
    (⟨[], 0, []⟩ : VIndRecArg).canonResult nfnAux 0
      = pfnOcc.args.getD 0 default := rfl

/-- **THE DATUM FROM `D.WF`.**  `docs/handoff-hargsshared.md` §4a's third source, which it ruled
out, supplying the clause at the nested witness.  Nothing about `R`, nothing about
`AddInductStagesR`, nothing about the checker's `Result` enters. -/
theorem pfnOcc_argsTypedH_of_wf {env et : VEnv} (hwf : nfnAux.WF env)
    (het : env.addIndTypes nfnAux = some et) : pfnOcc.ArgsTypedH nfnAux et :=
  pfnOcc_argsTypedH_of_hasType <|
    hwf.recField_canonResult het
      (show nfnAux.types[1]? = some (pfnOcc.member nfnAux.header nfnRestore') from rfl)
      (show pfnAuxMk ∈ (pfnOcc.member nfnAux.header nfnRestore').ctors from
        List.mem_cons_self)
      pfnAuxMk_field0 rfl

/-- …hence the family, hence the datum, from `D.WF` alone plus `Built`. -/
theorem nfnAux_argsTypedK_of_wf {env et : VEnv} (hwf : nfnAux.WF env)
    (het : env.addIndTypes nfnAux = some et) :
    nfnAux.ArgsTypedK nfnK et (fun _ => pfnOcc) :=
  fun _ _ _ _ => pfnOcc_argsTypedH_of_wf hwf het

/-- **END TO END FROM `D.WF`.**  The datum at the type head, with `D.WF` as the only source of
the spine typing.  `env₂ ≤ et` is `addConstList_le` on `addIndTypes`. -/
theorem nfnAux_datum_ty_of_wf {env₂ et : VEnv}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂) (hwf : nfnAux.WF env₂)
    (het : env₂.addIndTypes nfnAux = some et) :
    nfnRestore'.SpineTyped nfnAux et (nfnRestore'.tyName 1) 1 :=
  (nfnAux_built'_of_blockK h).spineTyped_ty_of_argsTypedK (nfnAux_argsTypedK_of_wf hwf het)
    (VEnv.addConstList_le het)
    (show nfnAux.types[1]? = some (pfnOcc.member nfnAux.header nfnRestore') from rfl)
    (by decide)

end NestedWit

#print axioms Lean4Lean.VInductDecl'.WF.recField_canonResult
#print axioms Lean4Lean.NestedWit.pfnAuxMk_field0
#print axioms Lean4Lean.NestedWit.pfnAuxMk_field0_canonResult
#print axioms Lean4Lean.NestedWit.pfnOcc_argsTypedH_of_wf
#print axioms Lean4Lean.NestedWit.nfnAux_argsTypedK_of_wf
#print axioms Lean4Lean.NestedWit.nfnAux_datum_ty_of_wf

/-! ### §5.3 …and `nfnAux.WF` is **unconditional**, so at this witness the clause is a theorem

`nfnAux_WF : ∀ {env}, nfnAux.WF env` (`Theory/Inductive/NestedBuild.lean`) holds in *every*
environment — `nfnAux` has no parameters and its members' types are `Type`.  So at this witness
the `D.WF` route leaves **no** hypothesis but the staging, and §8.7's `val` clause comes out of it
with nothing assumed about the spine at all. -/

namespace NestedWit

open InductiveDeclExamples ElimNestedInductive

/-- **THE CLAUSE, WITH NO HYPOTHESIS BUT THE STAGING.** -/
theorem pfnOcc_argsTypedH_of_staging {env et : VEnv}
    (het : env.addIndTypes nfnAux = some et) : pfnOcc.ArgsTypedH nfnAux et :=
  pfnOcc_argsTypedH_of_wf nfnAux_WF het

/-- **§8.7's `val` CLAUSE FROM `D.WF` ALONE**, at the environment `WF.ctors` is staged at.  This
composes §5's producer with §2.1's consumer at one environment — the composition §9 says is not
available in general. -/
theorem nfnAux_tyVal_hasType_of_wf {env₂ et : VEnv}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂)
    (het : env₂.addIndTypes nfnAux = some et) :
    et.HasType nfnAux.uvars [] (nfnRestore'.tyVal nfnAux 1)
      (pfnOcc.member nfnAux.header nfnRestore').type :=
  VIndRestore.tyVal_hasType_of_argsTypedK' (nfnAux_built'_of_blockK h)
    (nfnAux_argsTypedK_of_wf nfnAux_WF het) (VEnv.addConstList_le het) (by exact trivial)
    (show nfnAux.types[1]? = some (pfnOcc.member nfnAux.header nfnRestore') from rfl)
    (by decide) (by decide)

/-- …and the staging equation for it is satisfied, so §5.3 is not conditional on an empty
premise. -/
theorem nfnAux_addIndTypes_exists {env₂ : VEnv}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂) :
    ∃ et, env₂.addIndTypes nfnAux = some et := by
  have hfresh : ∀ n ∈ [``NFn, `_nested.PFn_1], env₂.constants n = none := by
    intro n hn
    rw [VEnv.addInduct'_constants_of_not_mem h (by revert hn; revert n; decide)]
    rfl
  exact VEnv.addConstList_eq_some_iff.2
    ⟨fun n hn => hfresh n (by revert hn; revert n; decide), by decide⟩

end NestedWit

#print axioms Lean4Lean.NestedWit.pfnOcc_argsTypedH_of_staging
#print axioms Lean4Lean.NestedWit.nfnAux_tyVal_hasType_of_wf
#print axioms Lean4Lean.NestedWit.nfnAux_addIndTypes_exists

/-! ## §6 The boundary, in general: no pre-block environment can carry the clause

`docs/handoff-hargsshared.md` §7 item 2 asks for this: `ntree_not_spineTyped_pre` refutes the
datum at the pre-block environment *at one witness*, and the argument ("the presented spine
mentions a name the step declares") is general.  Here it is, stated about the clause itself rather
than about the datum, so it bounds where the clause can be *supplied* rather than where the datum
can be *used*.

The inductive step is `HasArgs.mem_wf`: a spine that instantiates a telescope has every argument
well typed.  That is the whole content — no `WF`, no `PiInv`, no inversion. -/

namespace VEnv

/-- Each argument of a well-typed spine is well typed.  (`HasArgs` bundles the arguments with
*substituted* domains; this forgets the domains.) -/
theorem HasArgs.mem_wf {env : VEnv} {U : Nat} {Γ As as : List VExpr}
    (h : env.HasArgs U Γ As as) : ∀ a ∈ as, ∃ A, env.HasType U Γ a A := by
  induction h with
  | nil => simp
  | cons hA _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, hA⟩
    · exact ih a ha

end VEnv

/-- **THE CLAUSE IS FALSE AT ANY ENVIRONMENT THAT DOES NOT DECLARE WHAT THE SPINE MENTIONS.**
General: no block, no restoration, no `Built`.  The two side conditions are exactly the ones
`VEnv.IsDefEq.constsIn` needs. -/
theorem VNestedOcc.not_argsTypedH_of_not_constsIn {N : VNestedOcc} {D : VInductDecl'} {e : VEnv}
    (henv : e.Ordered) (hΓ : CtxConstsIn e.contains D.params.reverse)
    {a : VExpr} (ha : a ∈ N.args) (hcl : ¬ VExpr.ConstsIn a e.contains) :
    ¬ N.ArgsTypedH D e := by
  intro h
  obtain ⟨A, hA⟩ := h.ty.mem_wf a ha
  exact hcl (hA.constsIn henv.constsIn hΓ).1

/-! ### §6.1 …and it bites at the pre-block environment, at the second witness

`docs/handoff-hargsshared.md` §3c(i) proves this at `ntreeAux`/`listOcc`, where the spine is the
*applied* head `NTree α`.  Here it is at `nfnAux`/`pfnOcc`, where the spine is the bare constant
`NFn` and the block has **no** parameters — so the refutation is not an artefact of either
shape. -/

namespace NestedWit

open InductiveDeclExamples ElimNestedInductive

/-- **The clause is refuted at the pre-block environment.**  `env₂` is where `PFn` is declared and
`NFn` — which the spine *is* — is not.  So the clause cannot be a fact about the environment the
step runs at, at either witness, and any producer for it must be staged after the block's own type
constants land. -/
theorem pfnOcc_not_argsTypedH_pre {env₂ : VEnv}
    (h : VEnv.empty.addInduct' pfnDecl = some env₂) (henv : env₂.Ordered) :
    ¬ pfnOcc.ArgsTypedH nfnAux env₂ :=
  VNestedOcc.not_argsTypedH_of_not_constsIn henv trivial
    (show VExpr.const ``NFn [] ∈ pfnOcc.args from by decide)
    (fun hcl => nfn_not_contains_env₂ h hcl)

end NestedWit

#print axioms Lean4Lean.VEnv.HasArgs.mem_wf
#print axioms Lean4Lean.VNestedOcc.not_argsTypedH_of_not_constsIn
#print axioms Lean4Lean.NestedWit.pfnOcc_not_argsTypedH_pre

/-! ## §7 The `D.WF` route at the **parameterised** witness, and its limits

§5 could be an artefact of `nfnAux`: `np = 0`, no parameters, a spine that is a bare constant.
`ntreeAux` — `NTree α` with a `List (NTree α)` field, `np = 1`, spine `[NTree #0]` — is the block
Lean's own kernel runs the nested elimination on, and the route works there too, at the same field
position and by the same clause.  So it is a route, not a coincidence. -/

namespace InductiveDeclExamples

open VNestedOcc

/-- The clause at the parameterised witness, from one typing judgement.  All three of `listOcc`'s
telescopes — `List`'s stored type's, `List.nil`'s and `List.cons`'s — are `List`'s single parameter
binder. -/
theorem listOcc_argsTypedH_of_hasType {e : VEnv}
    (hN : e.HasType 1 [VExpr.sort (.succ (.param 0))]
      (.app (.const ``NTree [.param 0]) (.bvar 0)) (.sort (.succ (.param 0)))) :
    listOcc.ArgsTypedH ntreeAux e := by
  have harg : e.HasArgs ntreeAux.uvars ntreeAux.params.reverse
      [VExpr.sort (.succ (.param 0))] listOcc.args := .cons hN .nil
  refine ⟨by decide, ?_, fun C hC => ?_⟩
  · rw [show (splitPis listOcc.decl.np (listOcc.src.type.instL listOcc.lvls)).1
      = [VExpr.sort (.succ (.param 0))] from by decide]
    exact harg
  · rw [show (splitPis listOcc.decl.np
      ((C.type listOcc.decl listOcc.idx).instL listOcc.lvls)).1
      = [VExpr.sort (.succ (.param 0))] from by
        revert hC; revert C; decide]
    exact harg

/-- **THE DATUM FROM `D.WF` AT THE PARAMETERISED WITNESS.**  `List.cons`'s first field is `List`'s
parameter; nesting substitutes the spine for it, the recogniser fires, and `pos`'s sixth conjunct
is `NTree #0 : Type u` over `ntreeAux`'s parameter telescope — the clause's only content here. -/
theorem listOcc_argsTypedH_of_wf {env₁ et : VEnv} (hwf : ntreeAux.WF env₁)
    (het : env₁.addIndTypes ntreeAux = some et) : listOcc.ArgsTypedH ntreeAux et :=
  listOcc_argsTypedH_of_hasType <|
    hwf.recField_canonResult het
      (show ntreeAux.types[1]? = some (listOcc.member ntreeAux.header ntreeRestore) from rfl)
      (show listOcc.ctor ntreeAux.header ntreeRestore listCons
        ∈ (listOcc.member ntreeAux.header ntreeRestore).ctors from
        List.mem_cons_of_mem _ List.mem_cons_self)
      (show (listOcc.ctor ntreeAux.header ntreeRestore listCons).fields[0]?
        = some (⟨(VIndRecArg.mk [] 0 []).canonTypeH ntreeAux.header 0, VLevel.succ (.param 0),
            some ⟨[], 0, []⟩⟩ : VIndField) from rfl)
      rfl

/-- …hence the family at the parameterised witness.

The `h : VEnv.empty.addInduct' listDecl = some env₁` this used to take became unused when
`ntreeAux_WF h` was re-pointed to the hypothesis-free `ntreeAux_WF'`, so it is gone: the family
holds at **every** `env₁` that stages `ntreeAux`, not only the one holding `listDecl`. -/
theorem ntreeAux_argsTypedK_of_wf {env₁ et : VEnv}
    (het : env₁.addIndTypes ntreeAux = some et) :
    ntreeAux.ArgsTypedK ntreeK et (fun _ => listOcc) :=
  fun _ _ _ _ => listOcc_argsTypedH_of_wf ntreeAux_WF' het

/-- **END TO END AT THE PARAMETERISED WITNESS**: the shared datum at the presented type head
`List.{u} (NTree.{u} #0)`, with `D.WF` the only source of the spine typing. -/
theorem ntreeAux_datum_ty_of_wf {env₁ et : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (het : env₁.addIndTypes ntreeAux = some et) :
    ntreeRestore.SpineTyped ntreeAux et (ntreeRestore.tyName 1) 1 :=
  (ntreeAux_built h).spineTyped_ty_of_argsTypedK (ntreeAux_argsTypedK_of_wf het)
    (VEnv.addConstList_le het)
    (show ntreeAux.types[1]? = some (listOcc.member ntreeAux.header ntreeRestore) from rfl)
    (by decide)

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.listOcc_argsTypedH_of_hasType
#print axioms Lean4Lean.InductiveDeclExamples.listOcc_argsTypedH_of_wf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_argsTypedK_of_wf
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_datum_ty_of_wf

/-! ## §8 The clause is **one** datum, not two, under a syntactic side condition

`docs/handoff-hargsshared.md` §4b's "honest count: the datum is two, not one" is right as stated —
`ArgsTypedH.ty` is against the member's parameter telescope, `ArgsTypedH.ctor` against each
constructor's own — and it records that collapsing them "would go through
`VEnv.HasArgs.congr_tele`", which a concurrent stream owns.

It does not have to.  Whenever the two telescopes are **syntactically** equal, the collapse is a
rewrite, and both of the tree's nested witnesses satisfy that: `PFn`/`PFn.mk` and
`List`/`List.nil`/`List.cons` all present the same parameter binder.  F3 (`VIndCtor.WF.params_eq`)
only gives *definitional* equality in general, which is where `congr_tele` would be needed — but
that is a statement about the general case, not about the clause's two components at any block the
elimination actually runs on. -/

/-- **THE CLAUSE FROM ONE `HasArgs`**, given syntactic agreement of the foreign block's
constructor parameter telescopes with its member's.  No `congr_tele`, no defeq, no environment
condition. -/
theorem VNestedOcc.argsTypedH_of_ty {N : VNestedOcc} {D : VInductDecl'} {e : VEnv}
    (hlvls : ∀ l ∈ N.lvls, l.WF D.uvars)
    (hctor : ∀ C ∈ N.src.ctors,
      (VExpr.splitPis N.decl.np ((C.type N.decl N.idx).instL N.lvls)).1
        = (VExpr.splitPis N.decl.np (N.src.type.instL N.lvls)).1)
    (hty : e.HasArgs D.uvars D.params.reverse
      (VExpr.splitPis N.decl.np (N.src.type.instL N.lvls)).1 N.args) :
    N.ArgsTypedH D e where
  lvls := hlvls
  ty := hty
  ctor := fun C hC => by rw [hctor C hC]; exact hty

namespace InductiveDeclExamples

/-- The side condition holds at the `PFn` witness. -/
theorem pfnOcc_ctorTele_agree : ∀ C ∈ pfnOcc.src.ctors,
    (VExpr.splitPis pfnOcc.decl.np ((C.type pfnOcc.decl pfnOcc.idx).instL pfnOcc.lvls)).1
      = (VExpr.splitPis pfnOcc.decl.np (pfnOcc.src.type.instL pfnOcc.lvls)).1 := by decide

/-- …and at the parameterised `List` witness, for **both** of `List`'s constructors. -/
theorem listOcc_ctorTele_agree : ∀ C ∈ listOcc.src.ctors,
    (VExpr.splitPis listOcc.decl.np ((C.type listOcc.decl listOcc.idx).instL listOcc.lvls)).1
      = (VExpr.splitPis listOcc.decl.np (listOcc.src.type.instL listOcc.lvls)).1 := by decide

end InductiveDeclExamples

#print axioms Lean4Lean.VNestedOcc.argsTypedH_of_ty
#print axioms Lean4Lean.InductiveDeclExamples.pfnOcc_ctorTele_agree
#print axioms Lean4Lean.InductiveDeclExamples.listOcc_ctorTele_agree

/-! ## §9 What is left, and the exact `TrIndDeclN` edit if the general route is wanted

**What §5/§7 do and do not give.**  The route out of `D.WF` is: the companion member's
constructor has a field whose *source* type is one of the foreign block's parameters; nesting
substitutes the spine argument for it; the recogniser fires; and `VIndField.WF.pos`'s sixth
conjunct types `r.canonResult` — which at that field *is* the spine argument — at `.sort D.lvl`,
which at that field *is* the parameter's own sort.  Four coincidences, all four of them holding at
both of the tree's witnesses, none of them general:

1. the field must sit at declaration position `0`, or the prefix context is not `D.params.reverse`
   (a weakening would be needed, and the earlier field types are in the way);
2. the foreign block must *have* a constructor field that is a bare parameter — a phantom
   parameter (`Sigma`'s second component under a `Prop`-valued family, say) has none;
3. the recogniser must fire, i.e. the substituted argument must be a recursive occurrence of the
   *new* block.  A spine argument that is block-free — `List (Nat × NTree α)`'s `Nat` position —
   lands in `pos`'s `none` branch, which gives only `IsDefEqType F.type A` for some block-free `A`,
   not a typing at the parameter's sort;
4. `D.lvl` must be the parameter's sort level.  `D.lvl` is the block's *common* level, and
   `VIndType.WF.canon` only makes it `isEquiv` to each member's result level.

**And the environment.**  `WF.ctors` is staged at `env.addIndTypes D`, which declares the
companions; §8.7 consumes `hargs` at `AddInductStagesR`'s second stage, which does **not**.  The
two are incomparable, so §5's supply and §2.1's consumer do not compose at the same environment in
general — at the witness they do, because `nfnAux`'s datum needs only `NFn`, which both declare.
`RestoreData.args`/`OccursN.args_noNested` say the spine is free of `_nested` names, so nothing in
the *statement* obstructs a transport; what is missing is a restriction lemma saying a derivation
whose subject avoids the companion names can be replayed without them.  That is the one general
lemma this file's route needs and does not have.

**The edit, if the general route is wanted instead.**  One clause on `TrIndDeclN`
(`Verify/Environment/InductR.lean`), stated for the companion tail only, exactly as `trCtors` is
staged:

    trSpine : ∀ env₁, env.addIndTypesC D K = some env₁ →
      ∀ (j : Nat) T, D.types[j]? = some T → types.length ≤ j →
        env₁.HasArgs D.uvars D.params.reverse
          (VExpr.splitPis (npJ j) (T.typeAt …)) (R.tyArgs j)

i.e. `VInductDecl'.ArgsTypedK` restated over `R` rather than over `occ` (the two are
interchangeable by `Built.tyLvls`/`tyArgs` and `Occurs.ty_const`, which is `hargs_of_argsTypedK`
above).  It is a *hypothesis* relation, so adding a conjunct requires the consumer audit
`Verify/Inductive/TrIndDeclNCtorOwn.lean` established the pattern for; §3 is the proof that the
conjunct is not derivable from what is there.  **This file does not make that edit** —
`InductR.lean` is another stream's file, and the flip is the orchestrator's to sequence.

**Not touched, deliberately**: `tryEtaStructCore.WF` and `isDefEqUnitLike.WF`
(`docs/vacuity-ledger.md` row 197), and the flip itself. -/

/-! ## §10 The headline, with nothing hypothesised

Both statements below are closed — no free variables, no staging assumed, no `D.WF`, no
`AddInductStagesR`.  They say: **at both nested blocks in this tree, the shared datum of the flip's
four sites holds, and at the `NFn` block §8.7's `val` clause holds with it.**

That is not the general discharge (§3 is the proof that the general clause is new content, and §9
lists the four coincidences the route rests on).  It is the strongest form of "instantiate, don't
admire" available for this datum: two blocks, one of them parameterised and the one Lean's own
kernel runs the nested elimination on, with every hypothesis discharged. -/

namespace NestedWit

open InductiveDeclExamples ElimNestedInductive

/-- **HYPOTHESIS-FREE, AT THE `NFn` BLOCK**: the clause, the datum at the presented type head, and
§8.7's `val` clause, all at one environment. -/
theorem nfnAux_datum_of_wf_inhabited :
    ∃ env₂ et : VEnv, VEnv.empty.addInduct' pfnDecl = some env₂ ∧
      env₂.addIndTypes nfnAux = some et ∧
      nfnAux.ArgsTypedK nfnK et (fun _ => pfnOcc) ∧
      nfnRestore'.SpineTyped nfnAux et (nfnRestore'.tyName 1) 1 ∧
      et.HasType nfnAux.uvars [] (nfnRestore'.tyVal nfnAux 1)
        (pfnOcc.member nfnAux.header nfnRestore').type := by
  obtain ⟨env₂, h⟩ : ∃ e, VEnv.empty.addInduct' pfnDecl = some e := ⟨_, rfl⟩
  obtain ⟨et, het⟩ := nfnAux_addIndTypes_exists h
  exact ⟨env₂, et, h, het, nfnAux_argsTypedK_of_wf nfnAux_WF het,
    nfnAux_datum_ty_of_wf h nfnAux_WF het, nfnAux_tyVal_hasType_of_wf h het⟩

end NestedWit

namespace InductiveDeclExamples

/-- **HYPOTHESIS-FREE, AT THE PARAMETERISED `NTree`/`List` BLOCK**: the clause and the datum at the
presented head `List.{u} (NTree.{u} #0)`. -/
theorem ntreeAux_datum_of_wf_inhabited :
    ∃ env₁ et : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypes ntreeAux = some et ∧
      ntreeAux.ArgsTypedK ntreeK et (fun _ => listOcc) ∧
      ntreeRestore.SpineTyped ntreeAux et (ntreeRestore.tyName 1) 1 := by
  obtain ⟨env₁, E₁, -, -, -, h, hE₁, -⟩ := ntree_stage₂_exists
  exact ⟨env₁, E₁, h, hE₁, ntreeAux_argsTypedK_of_wf hE₁, ntreeAux_datum_ty_of_wf h hE₁⟩

/-- **THE TRIM ABOVE, INSTANTIATED WHERE THE REMOVED HYPOTHESIS IS FALSE.**

`ntreeAux_argsTypedK_of_wf` used to take `h : VEnv.empty.addInduct' listDecl = some env₁`.  It
became unused when `ntreeAux_WF h` was re-pointed to the hypothesis-free `ntreeAux_WF'`, and was
deleted (`docs/handoff-wfripple.md` §3.1).  Dropping a hypothesis changes what a statement says,
so here is the difference: at `env₁ := VEnv.empty` the removed equation is **refuted** —
`addInduct'` declares `List`, and `VEnv.empty` holds nothing — while the surviving staging
hypothesis is inhabited.  So the untrimmed statement had no instance at all at this `env₁`, and
the trimmed one delivers the argument family. -/
theorem ntreeAux_argsTypedK_over_empty :
    ¬ (VEnv.empty.addInduct' listDecl = some VEnv.empty) ∧
      ∃ et : VEnv, VEnv.empty.addIndTypes ntreeAux = some et ∧
        ntreeAux.ArgsTypedK ntreeK et (fun _ => listOcc) := by
  refine ⟨fun h => absurd (list_const h) nofun, ?_⟩
  obtain ⟨et, het⟩ : ∃ e : VEnv, VEnv.empty.addIndTypes ntreeAux = some e :=
    VEnv.addConstList_eq_some_iff.2 ⟨fun _ _ => rfl, by decide⟩
  exact ⟨et, het, ntreeAux_argsTypedK_of_wf het⟩

end InductiveDeclExamples

#print axioms Lean4Lean.NestedWit.nfnAux_datum_of_wf_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_datum_of_wf_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_argsTypedK_over_empty
