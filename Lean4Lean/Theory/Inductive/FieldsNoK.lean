import Lean4Lean.Theory.Inductive.NestedFresh
import Lean4Lean.Theory.Inductive.MemberRedex
import Lean4Lean.Theory.Inductive.RestoreBridge

/-!
# `Built.fields_noK` is redundant — the derivation, and the price at every site

`VInductDecl'.Built.fields_noK` (`Theory/Inductive/NestedBuild.lean`) is ruling 116d's residual
clause.  Since `Built.occurs` was retyped to `VNestedOcc.OccursN`
(`docs/handoff-nestednames.md`, Part 2) the clause has been *derivable* — that was the payoff
`OccursN` was built for.  This file discharges the derivation and measures its cost, **without
editing `Built`**: see §6 for why the removal itself cannot land inside one stream's file grant,
and `docs/handoff-fieldsnok.md` for the exact diff.

* `§1` the `NoConstIn`/`NoConsts` bridge, **relocated into `Theory/`** — a prerequisite §6.3 of
  `Verify/Inductive/OccArgsTyping.lean` did not name.
* `§2` `VEnv.KHyg`: the three environment facts `OccursN` cannot supply, bundled.
* `§3` the derivation: `fields_noK`'s body, from `Built.occurs` and `KHyg`, at the *exact*
  signature of the field it would replace.
* `§4` the six `Built`-building sites, measured one at a time.  The four that live under
  `Theory/` are proved here; the two general bridges live under `Verify/` and are measured in
  `docs/handoff-fieldsnok.md` §4 instead (this file may not import `Verify/`).
* `§5` anti-vacuity: `KHyg` is inhabited, each of its three clauses is a real restriction, and
  `OccursN` is still a proper strengthening of `Occurs`.
* `§6` what the removal costs, as a statement about the tree rather than a plan.
* `§7` the edit itself, **modelled and machine-checked**: `Built'` is post-edit `Built`, and
  `fields_noK`, `toFresh`, `toFaithful` and `fields_noK_needs_spine` are re-proved against it with
  their original proof terms and the same axiom sets.

Nothing here changes any existing declaration, so `Theory/Inductive/NestedFresh.lean`'s
`occurs_args_congr`, `listOccBadSpine_occurs` and `fields_noK_needs_spine` and
`Verify/Inductive/OccArgsTyping.lean`'s `occursN_args_congr_false` are untouched **by
construction**.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §1 The `NoConstIn`/`NoConsts` bridge, on the `Theory/` side of the layering

`VExpr.noConsts_of_noConstIn` exists — at `Verify/Inductive/SpineTransfer.lean:61`.  It is a
statement about `VExpr.NoConstIn` (`Theory/Inductive/NestedNames.lean`) and `VExpr.NoConsts`
(`Theory/Inductive/Decl.lean`) with no `Verify/` vocabulary in it at all, and the derivation in
§3 — which, after the edit, has to live *in `NestedBuild.lean`* next to `Built` — needs it.  So
the edit has a Part-1-style relocation as a prerequisite, exactly like `NoConstIn` itself last
round.

The proof below is the `Verify/`-side one verbatim, under a primed name so that the two can
coexist until the relocation happens.  `docs/handoff-fieldsnok.md` §2 states the move. -/

namespace VExpr

/-- `NoConstIn` at a predicate that covers `K` gives `NoConsts K`.  Verbatim
`Verify/Inductive/SpineTransfer.lean`'s `noConsts_of_noConstIn`, in `Theory/`. -/
theorem noConsts_of_noConstIn' {P : Name → Prop} {K : List Name} (hK : ∀ n ∈ K, P n) :
    ∀ {e : VExpr}, e.NoConstIn P → e.NoConsts K
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => fun hc => h (hK c hc)
  | .app .., h | .lam .., h | .forallE .., h =>
    ⟨noConsts_of_noConstIn' hK h.1, noConsts_of_noConstIn' hK h.2⟩

end VExpr

/-! ## §2 `VEnv.KHyg`: what `OccursN` cannot supply

`VNestedOcc.OccursN.args_noNested` says the nested spine mentions no `_nested`-prefixed
constant.  To turn that into `fields_noK` three facts about `env` and `K` are needed, and
**none of the three is a consequence of `Built`** — measured in §6.2 below.  Bundling them is
what makes the replacement clause a single field, hence what keeps every *consumer* of
`Built.fields_noK` working with its existing proof term (§3.4). -/

/-- **Companion-name hygiene at an environment.**  The three environment-side premises of
`VNestedOcc.fields_noK_of_occurs`, minus the spine premise `OccursN` now carries.

`constsClosedC` is `VEnv.ConstsClosed`'s constants half (`NestedBuild.lean` §F2.1); `notContains`
is the step's own staging freshness (`VInductDecl'.fresh_of_addIndTypes`); `isNested` is the
reserved-prefix fact (`ElimNestedInductive.Result.RestoreData.isNestedName_of_mem` at the general
construction, `by decide` at a concrete block). -/
structure VEnv.KHyg (env : VEnv) (K : List Name) : Prop where
  /-- Declared constants have types mentioning only declared constants. -/
  constsClosedC : env.ConstsClosedC
  /-- No companion name is declared yet. -/
  notContains : ∀ n ∈ K, ¬ env.contains n
  /-- Every companion name carries the reserved `_nested` prefix. -/
  isNested : ∀ n ∈ K, IsNestedName n

/-! ## §3 The derivation

Read this section as the body of the edit: after `fields_noK` comes off `Built` and a
`hyg : VEnv.KHyg env K` field replaces it, `§3.4` **is** the replacement projection, and it
type-checks at the field's old signature. -/

namespace VNestedOcc
variable {N : VNestedOcc} {env : VEnv} {K : List Name}

/-- **§3.1 The spine premise, from `OccursN`.**  `fields_noK_of_occurs`'s `hargs`, which
`Theory/Inductive/NestedFresh.lean`'s `fields_noK_needs_spine` proves is not a consequence of
`Occurs`. -/
theorem OccursN.args_noConsts_of_hyg (h : N.OccursN env) (hK : ∀ n ∈ K, IsNestedName n) :
    ∀ a ∈ N.args, VExpr.NoConsts K a :=
  fun a ha => VExpr.noConsts_of_noConstIn' hK (h.args_noNested a ha)

/-- **§3.2 `fields_noK`'s body at one occurrence, with no spine hypothesis left.** -/
theorem OccursN.fields_noK_of_hyg (hyg : env.KHyg K) (h : N.OccursN env)
    {C₀ : VIndCtor} (hC₀ : C₀ ∈ N.src.ctors) {k : Nat} {F₀ : VIndField}
    (hF₀ : C₀.fields[k]? = some F₀) :
    VExpr.NoConsts K (VExpr.instAll (F₀.type.instL N.lvls) N.args k) :=
  fields_noK_of_occurs hyg.constsClosedC h.toOccurs hyg.notContains
    (h.args_noConsts_of_hyg hyg.isNested) hC₀ hF₀

end VNestedOcc

/-- **§3.3 `Built.fields_noK`'s whole body, from `occurs` and `KHyg`.**  Everything the field
asserts, with the field not in sight. -/
theorem VInductDecl'.fields_noK_of_occursN {D : VInductDecl'} {K : List Name} {env : VEnv}
    {occ : Nat → VNestedOcc} (hyg : env.KHyg K)
    (hocc : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      (occ j).OccursN env) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ C₀ ∈ (occ j).src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
        VExpr.NoConsts K (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args k) :=
  fun j T hT hKT _C₀ hC₀ _k _F₀ hF₀ =>
    VNestedOcc.OccursN.fields_noK_of_hyg hyg (hocc j T hT hKT) hC₀ hF₀

/-- **§3.4 The replacement projection.**  After the edit this is `Built.fields_noK` — same
statement, one extra argument, and *that argument is the field that replaces it*, so at the real
edit `hyg` reads `h.hyg` and the extra argument disappears again.  The four call sites of the old
field (`NestedBuild.lean`:787, :1071, `NestedFresh.lean`:146, plus `BuiltFresh`'s twin) accept
this proof term with `h.hyg` spliced in and nothing else changed. -/
theorem VInductDecl'.Built.fields_noK_derived {D : VInductDecl'} {R : VIndRestore}
    {K : List Name} {env : VEnv} {occ : Nat → VNestedOcc}
    (h : D.Built R K env occ) (hyg : env.KHyg K) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ C₀ ∈ (occ j).src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
        VExpr.NoConsts K (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args k) :=
  VInductDecl'.fields_noK_of_occursN hyg h.occurs

/-- **§3.5 `BuiltFresh` from `KHyg`.**  Compare `VInductDecl'.builtFresh_of_occurs`
(`NestedBuild.lean` §F4): the `hargs` hypothesis is gone, replaced by `KHyg.isNested`.  This is
the *strictly weaker-hypothesis* version — `hargs` was a statement about `D.np` expressions per
member, `isNested` is a statement about `K`'s names. -/
theorem VInductDecl'.builtFresh_of_hyg {D : VInductDecl'} {K : List Name} {env : VEnv}
    {occ : Nat → VNestedOcc} (hyg : env.KHyg K) (hnd : D.blockNames.Nodup)
    (hocc : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      (occ j).OccursN env) :
    D.BuiltFresh K occ where
  nodup := hnd
  fields_noK := VInductDecl'.fields_noK_of_occursN hyg hocc

/-- …and `Built.toFresh`'s replacement, for completeness.  (`Built.toFresh` itself is **dead**:
measured against the project's reference index, its only reference is its own declaration —
`Theory/Inductive/NestedBuild.lean`:785.  The edit may delete it rather than port it.) -/
theorem VInductDecl'.Built.toFresh_of_hyg {D : VInductDecl'} {R : VIndRestore} {K : List Name}
    {env : VEnv} {occ : Nat → VNestedOcc} (h : D.Built R K env occ) (hyg : env.KHyg K) :
    D.BuiltFresh K occ :=
  VInductDecl'.builtFresh_of_hyg hyg h.nodup h.occurs

#print axioms Lean4Lean.VExpr.noConsts_of_noConstIn'
#print axioms Lean4Lean.VNestedOcc.OccursN.args_noConsts_of_hyg
#print axioms Lean4Lean.VNestedOcc.OccursN.fields_noK_of_hyg
#print axioms Lean4Lean.VInductDecl'.fields_noK_of_occursN
#print axioms Lean4Lean.VInductDecl'.Built.fields_noK_derived
#print axioms Lean4Lean.VInductDecl'.builtFresh_of_hyg
#print axioms Lean4Lean.VInductDecl'.Built.toFresh_of_hyg

/-! ## §4 The six `Built`-building sites, measured

`Verify/Inductive/OccArgsTyping.lean` §6.3 Step 2 asserted that "the six `Built`-building sites
all already have the `addInduct'` hypothesis the first two come from, and the third is
`RestoreData.isNestedName_of_mem`".  **Re-measured here, and it holds at the four sites this
module can reach** — for each, `KHyg` is proved from facts that were already in the tree, and
then the site's `fields_noK` is re-derived *without* reading the site's own field.

The two sites this module cannot reach are under `Verify/`
(`NestedRestoreWit.lean`:570 `mkRestore_built`, and `NestedOccData.lean`:473, which routes
through it).  Nothing under `Theory/` may import `Verify/`, so they are measured in
`docs/handoff-fieldsnok.md` §4 instead — where the answer is *yes with one caveat*:
`mkRestore_built` itself carries none of the three, its two reduced forms
(`NestedFreshBridge.lean`'s `mkRestore_built_of_spine`, `SpineTransfer.lean`'s
`mkRestore_built_of_blockK`) carry `constsClosedC` and `notContains` already, and only
`mkRestore_built_of_blockK` can produce `isNested` (from `hKB : ∀ n ∈ K, n ∈ D.blockNames`, via
`RestoreData.isNestedName_of_mem`).  `mkRestore_built_of_spine` **cannot**: it has no `hKB` and no
`RestoreData.auxName` route to one, so it needs a genuinely new hypothesis. -/

namespace InductiveDeclExamples

/-! ### §4.1 `ntreeAux_built` (`NestedBuild.lean`:1403), `K = ntreeK`, `env = env₁` -/

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- All three clauses, from facts already at the site: `listEnv_constsClosedC`,
`ntreeK_not_contains`, and one `decide`. -/
theorem ntreeK_hyg : env₁.KHyg ntreeK where
  constsClosedC := listEnv_constsClosedC h
  notContains := ntreeK_not_contains h
  isNested := by decide

/-- **The site's `fields_noK`, re-derived.**  `ntreeAux_built`'s own `fields_noK` field is not
read: the input is `occurs` (which is `OccursN`) plus `KHyg`. -/
theorem ntreeAux_fields_noK_derived :
    ∀ (j : Nat) (T : VIndType), ntreeAux.types[j]? = some T → T.name ∈ ntreeK →
      ∀ C₀ ∈ (listOcc : VNestedOcc).src.ctors, ∀ (k : Nat) (F₀ : VIndField),
        C₀.fields[k]? = some F₀ →
        VExpr.NoConsts ntreeK (VExpr.instAll (F₀.type.instL listOcc.lvls) listOcc.args k) :=
  VInductDecl'.fields_noK_of_occursN (occ := fun _ => listOcc) (ntreeK_hyg h)
    (fun _ _ _ _ => listOcc_occurs h)

end

/-! ### §4.2 `nfnAux_built` (`NestedBuild.lean`:1912), `K = nfnK`, `env = env₂` -/

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)
include h

theorem nfnK_hyg : env₂.KHyg nfnK where
  constsClosedC := pfnEnv_constsClosedC h
  notContains := nfnK_not_contains h
  isNested := by decide

theorem nfnAux_fields_noK_derived :
    ∀ (j : Nat) (T : VIndType), nfnAux.types[j]? = some T → T.name ∈ nfnK →
      ∀ C₀ ∈ (pfnOcc : VNestedOcc).src.ctors, ∀ (k : Nat) (F₀ : VIndField),
        C₀.fields[k]? = some F₀ →
        VExpr.NoConsts nfnK (VExpr.instAll (F₀.type.instL pfnOcc.lvls) pfnOcc.args k) :=
  VInductDecl'.fields_noK_of_occursN (occ := fun _ => pfnOcc) (nfnK_hyg h)
    (fun _ _ _ _ => pfnOcc_occurs h)

/-! ### §4.3 `nfnAuxDirty_built` (`RestoreBridge.lean`:941)

Same `K` and same `env` as §4.2 — the *dirty* block differs from `nfnAux` in its `types`, not in
its companion names — so `nfnK_hyg` covers it with no new fact at all.  The derivation is stated
against `nfnAuxDirty`'s own `types` to make that concrete. -/

theorem nfnAuxDirty_fields_noK_derived :
    ∀ (j : Nat) (T : VIndType), nfnAuxDirty.types[j]? = some T → T.name ∈ nfnK →
      ∀ C₀ ∈ (pfnOcc : VNestedOcc).src.ctors, ∀ (k : Nat) (F₀ : VIndField),
        C₀.fields[k]? = some F₀ →
        VExpr.NoConsts nfnK (VExpr.instAll (F₀.type.instL pfnOcc.lvls) pfnOcc.args k) :=
  VInductDecl'.fields_noK_of_occursN (occ := fun _ => pfnOcc) (nfnK_hyg h)
    (fun j T hT hK => (nfnAuxDirty_built h).occurs j T hT hK)

end

end InductiveDeclExamples

namespace MRedex.QNWit
open InductiveDeclExamples

/-! ### §4.4 `qnAux_built` (`MemberRedex.lean`:1083), `K = qnK`, `env = env₂` of `qjDecl`

Note this `env₂` is a *different* environment from §4.2's: it is fixed by
`VEnv.empty.addInduct' qjDecl = some env₂`.  The site has `qjEnv_constsClosedC` and
`qnK_not_contains`, and `qnK = [`_nested.QJ_1]` is `IsNestedName` by `decide`. -/

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' qjDecl = some env₂)
include h

theorem qnK_hyg : env₂.KHyg qnK where
  constsClosedC := qjEnv_constsClosedC h
  notContains := qnK_not_contains h
  isNested := by decide

theorem qnAux_fields_noK_derived :
    ∀ (j : Nat) (T : VIndType), qnAux.types[j]? = some T → T.name ∈ qnK →
      ∀ C₀ ∈ (qnOcc : VNestedOcc).src.ctors, ∀ (k : Nat) (F₀ : VIndField),
        C₀.fields[k]? = some F₀ →
        VExpr.NoConsts qnK (VExpr.instAll (F₀.type.instL qnOcc.lvls) qnOcc.args k) :=
  VInductDecl'.fields_noK_of_occursN (occ := fun _ => qnOcc) (qnK_hyg h)
    (fun _ _ _ _ => qnOcc_occurs h)

end

end MRedex.QNWit

#print axioms Lean4Lean.InductiveDeclExamples.ntreeK_hyg
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_fields_noK_derived
#print axioms Lean4Lean.InductiveDeclExamples.nfnK_hyg
#print axioms Lean4Lean.InductiveDeclExamples.nfnAux_fields_noK_derived
#print axioms Lean4Lean.InductiveDeclExamples.nfnAuxDirty_fields_noK_derived
#print axioms Lean4Lean.MRedex.QNWit.qnK_hyg
#print axioms Lean4Lean.MRedex.QNWit.qnAux_fields_noK_derived

/-! ## §5 Anti-vacuity

`docs/vacuity-ledger.md` §0: a hypothesis carried must be discharged or proved inhabited, and a
strengthening satisfied by everything discharges nothing.  `KHyg` is the hypothesis this file
proposes to carry, so all four checks are here. -/

namespace InductiveDeclExamples

/-! ### §5.1 Inhabited, at a named environment

Not `∃ env K, env.KHyg K` with `K = []` — that is satisfied by `VEnv.empty` and says nothing.
The witness below has a **non-empty** `K` and an environment fixed by a `decide`-able equation,
and it is the environment of a real nested step. -/

theorem listDecl_env_exists' : ∃ e, VEnv.empty.addInduct' listDecl = some e := ⟨_, rfl⟩

/-- `KHyg` is inhabited at a non-empty `K`, at the `NTree` step's own history environment.  The
environment is the one `VEnv.empty.addInduct' listDecl` computes, supplied by `rfl`, so no choice
principle enters. -/
theorem khyg_inhabited : ∃ (env : VEnv) (K : List Name), env.KHyg K ∧ K ≠ [] :=
  ⟨_, ntreeK, ntreeK_hyg rfl, by decide⟩

/-! ### §5.2 `isNested` is a real restriction, and it is the load-bearing clause

`ntreeK ++ [`Junk]` is `notContains` at `env₁` just as `ntreeK` is (`Junk` is not a `listDecl`
name), but it is not `KHyg`: `Junk` carries no reserved prefix.  So the third clause is not
implied by the other two. -/

theorem junkK_not_isNested : ¬ ∀ n ∈ (`_nested.List_1 :: [`Junk] : List Name), IsNestedName n :=
  fun h => absurd (h `Junk (by decide)) (by decide)

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

omit h in
theorem junkK_not_khyg : ¬ env₁.KHyg (`_nested.List_1 :: [`Junk]) :=
  fun hy => junkK_not_isNested hy.isNested

end

/-- **…and dropping `isNested` breaks the derivation, not merely the proof.**  `pfnOcc` is an
`OccursN` occurrence whose spine is `[NFn]`; at `K = [``NFn]` the spine premise
`∀ a ∈ N.args, NoConsts K a` is **false**.  So `OccursN.args_noConsts_of_hyg` cannot drop `hK`,
and `fields_noK` cannot be derived from `OccursN` plus environment closure alone. -/
theorem pfnOcc_args_not_noConsts_at_NFn :
    ¬ ∀ a ∈ pfnOcc.args, VExpr.NoConsts [``NFn] a := by decide

/-- The `K` that refutes it is exactly one that fails `isNested`. -/
theorem nfnK'_not_isNested : ¬ ∀ n ∈ ([``NFn] : List Name), IsNestedName n :=
  fun h => absurd (h ``NFn (by decide)) (by decide)

/-! ### §5.3 `notContains` is a real restriction

At `env₁` the name `List` *is* declared, so `K = [``List]` fails `notContains` — while
`constsClosedC` is a fact about `env₁` alone and cannot notice.  (`isNested` fails here too;
`§5.2` already separated that clause, and this one separates `notContains` from
`constsClosedC`.) -/

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

theorem listK_not_notContains : ¬ ∀ n ∈ ([``List] : List Name), ¬ env₁.contains n := fun hn =>
  hn ``List (by decide) (listDecl.addInduct'_contains h (by decide))

theorem listK_not_khyg : ¬ env₁.KHyg [``List] := fun hy => listK_not_notContains h hy.notContains

end

/-! ### §5.4 `OccursN` is still a proper strengthening of `Occurs`

The `Theory/`-side restatement of `Verify/Inductive/OccArgsTyping.lean`'s
`listOccBadSpine_not_occursN`, so that this file's own controls do not depend on a `Verify/`
module.  `listOccBadSpine` **is** an `Occurs env₁` occurrence
(`NestedFresh.lean`'s `listOccBadSpine_occurs`) and is **not** an `OccursN` one — which is why
the clause could not go into `Occurs` and had to go on an extension. -/

theorem listOccBadSpine_args_not_noNested :
    ¬ ∀ a ∈ listOccBadSpine.args, a.NoConstIn IsNestedName := by decide

section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

omit h in
theorem listOccBadSpine_not_occursN' : ¬ listOccBadSpine.OccursN env₁ :=
  fun ho => listOccBadSpine_args_not_noNested ho.args_noNested

/-- **The separating pair, at `OccursN`.**  Same `decl`/`idx`/`lvls`/spine length, both `Occurs`,
only one `OccursN` — and `fields_noK` holds of exactly the `OccursN` one.  This is
`fields_noK_needs_spine` re-read as "the spine premise is exactly `args_noNested`". -/
theorem occursN_separates :
    listOcc.Occurs env₁ ∧ listOccBadSpine.Occurs env₁ ∧
    listOcc.OccursN env₁ ∧ ¬ listOccBadSpine.OccursN env₁ :=
  ⟨(listOcc_occurs h).toOccurs, listOccBadSpine_occurs h, listOcc_occurs h,
    listOccBadSpine_not_occursN'⟩

end

end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.khyg_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.junkK_not_isNested
#print axioms Lean4Lean.InductiveDeclExamples.junkK_not_khyg
#print axioms Lean4Lean.InductiveDeclExamples.pfnOcc_args_not_noConsts_at_NFn
#print axioms Lean4Lean.InductiveDeclExamples.nfnK'_not_isNested
#print axioms Lean4Lean.InductiveDeclExamples.listK_not_notContains
#print axioms Lean4Lean.InductiveDeclExamples.listK_not_khyg
#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_args_not_noNested
#print axioms Lean4Lean.InductiveDeclExamples.listOccBadSpine_not_occursN'
#print axioms Lean4Lean.InductiveDeclExamples.occursN_separates

/-! ## §6 What the removal costs

### §6.1 The consumer side is free; the producer side is not

`Built.fields_noK` has exactly **nine** references in the project (measured against the LSP
reference index, not the source text): its declaration, three consumers and five producers.

| reference | role |
| --- | --- |
| `NestedBuild.lean`:766 | the field itself |
| `NestedBuild.lean`:787 (`Built.toFresh`) | consumer — and `toFresh` is dead (one reference, its own declaration) |
| `NestedBuild.lean`:1071 (`Built.toFaithful`) | consumer — the real one |
| `NestedFresh.lean`:146 (`fields_noK_needs_spine`) | consumer — an **anti-vacuity control** |
| `NestedBuild.lean`:1412, :1914 | producers (this stream's grant) |
| `RestoreBridge.lean`:974, `MemberRedex.lean`:1085 | producers (`Theory/`, not this stream's) |
| `NestedRestoreWit.lean`:576 | producer (`Verify/`, the general bridge) |

§3.4 is what makes the three consumers free: replace the field by `hyg : VEnv.KHyg env K` and
`Built.fields_noK` becomes a theorem at the *same* signature, so all three call sites keep their
existing proof terms verbatim — `NestedFresh.lean`:146's positional application
`… .fields_noK 1 _ rfl (by decide) C₀ hC₀ k F₀ hF₀` included.  That is the whole reason to
introduce a replacement field rather than push premises onto `toFaithful`: pushing them onto
`toFaithful` moves the ripple to `toFaithful`'s five call sites *and* breaks
`fields_noK_needs_spine`.

The five producers are not free: each must supply `hyg` where it supplied `fields_noK`.  §4
proves that all four `Theory/`-side producers can, from facts already in the tree.

### §6.2 The three premises are genuinely new to `Built`

`Built` carries `member`, `occurs`, `tyName`, `tyLvls`, `tyArgs`, `ctorName_inv`, `own`, `nodup`,
`fields_noK`.  None of the three `KHyg` clauses follows from them: `constsClosedC` and
`notContains` are facts about `env` that no clause constrains beyond "it declares `J`'s member and
constructors" (`Occurs.ty_const`, `Occurs.ctor_const`), and `isNested` is a fact about `K`'s
*names* — `VNestedOcc.auxName` is an unconstrained `Name` field, and `Built` never asserts that a
member name in `K` is an `auxName` of the shape `IsNestedName` accepts.  So `KHyg` is an addition,
not a repackaging, and the trade is: one clause quantified over the **foreign block's constructors
and fields** for three clauses quantified over `env` and `K`.

### §6.3 Why the edit is not in this file

The removal touches `Built`'s field list, so every producer changes.  Two producers are under
`Theory/` but outside this stream's grant (`RestoreBridge.lean`, `MemberRedex.lean`) and one is
under `Verify/` (`NestedRestoreWit.lean`, whose signature change then reaches
`NestedOccData.lean`, `NestedFreshBridge.lean` and `SpineTransfer.lean`).  A full `lake build`
cannot be green with only `NestedBuild.lean` edited, so the edit is stated in
`docs/handoff-fieldsnok.md` §5 with a per-file diff and left for the orchestrator, and everything
that can be proved without it is proved here — §7 included, which is the edit in every respect
except being applied. -/

/-! ## §7 The edit, as a machine-checked model

§6 says the removal cannot land inside one stream's grant.  What *can* land is the whole edit
**modelled**: `Built'` below is `Built` with `fields_noK` deleted and `hyg : VEnv.KHyg env K`
added, and everything the real edit has to preserve is re-proved against it, in each case with the
original's proof term and nothing else.

This is not a second `Built` for the tree to carry: it exists so the edit can be judged before it
is made, and `docs/handoff-fieldsnok.md` §5 says to delete this section when the edit lands. -/

/-- **`Built` after the edit.**  Nine clauses verbatim from `Theory/Inductive/NestedBuild.lean`'s
`VInductDecl'.Built`, with `fields_noK` replaced by `hyg`.  Docstrings dropped — read them at the
original. -/
structure VInductDecl'.Built' (D : VInductDecl') (R : VIndRestore) (K : List Name)
    (env : VEnv) (occ : Nat → VNestedOcc) : Prop where
  member : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    T = (occ j).member D.header R
  occurs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).OccursN env
  tyName : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    R.tyName j = (occ j).tyName
  tyLvls : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    R.tyLvls j = (occ j).lvls
  tyArgs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    R.tyArgs j = (occ j).args
  ctorName_inv : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ C ∈ (occ j).src.ctors, R.ctorName ((occ j).ctorName C.name) = C.name
  own : R.OwnId D K
  nodup : D.blockNames.Nodup
  /-- **The replacement clause.**  Three facts about `env` and `K`, in place of one about the
  foreign block's constructors and fields. -/
  hyg : env.KHyg K

section
variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env : VEnv}
  {occ : Nat → VNestedOcc}

/-- **§7.1 The replacement projection, at the old signature.**  No extra argument: `hyg` is read
off the structure.  So every one of the old field's three consumers keeps its call verbatim. -/
theorem VInductDecl'.Built'.fields_noK (h : D.Built' R K env occ) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ C₀ ∈ (occ j).src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
        VExpr.NoConsts K (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args k) :=
  VInductDecl'.fields_noK_of_occursN h.hyg h.occurs

/-- **§7.2 Consumer 1: `Built.toFresh`** (`NestedBuild.lean`:785), proof term unchanged. -/
theorem VInductDecl'.Built'.toFresh (h : D.Built' R K env occ) : D.BuiltFresh K occ :=
  ⟨h.nodup, h.fields_noK⟩

/-- **§7.3 Consumer 2: `Built.toFaithful`** (`NestedBuild.lean`:1046), proof term unchanged —
`h.fields_noK` now resolves to §7.1 rather than to a field, and nothing else moves. -/
theorem VInductDecl'.Built'.toFaithful (h : D.Built' R K env occ) :
    R.Faithful D env K (fun j => (occ j).decl.np) where
  ty_agree := by
    intro j T hT hK
    have ho := (h.occurs j T hT hK).toOccurs
    refine ⟨_, by rw [h.tyName j T hT hK]; exact ho.ty_const, ?_, ?_⟩
    · rw [h.tyLvls j T hT hK, ho.lvls_len]
    · rw [(occ j).instAt_eq D.header R D j _ _ rfl (h.tyLvls j T hT hK)
        (h.tyArgs j T hT hK) rfl, h.member j T hT hK]
      rfl
  ctor_agree := by
    intro j T hT hK C hC
    have ho := (h.occurs j T hT hK).toOccurs
    rw [h.member j T hT hK, VNestedOcc.member, List.mem_map] at hC
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    refine ⟨⟨(occ j).decl.uvars, C₀.type (occ j).decl (occ j).idx⟩, ?_, ?_, ?_⟩
    · rw [show ((occ j).ctor D.header R C₀).name = (occ j).ctorName C₀.name from rfl,
        h.ctorName_inv j T hT hK C₀ hC₀]
      exact ho.ctor_const C₀ hC₀
    · rw [h.tyLvls j T hT hK, ho.lvls_len]
    · rw [(occ j).instAt_eq D.header R D j _ _ rfl (h.tyLvls j T hT hK)
        (h.tyArgs j T hT hK) rfl]
      exact ((occ j).ctor_typeR D.header R D K rfl h.own h.nodup j C₀
        (h.fields_noK j T hT hK C₀ hC₀) (h.tyName j T hT hK)
        (h.tyLvls j T hT hK) (h.tyArgs j T hT hK) (ho.ctor_params C₀ hC₀) ho.args_len
        ho.lvls_len).symm
  ctors_complete := by
    intro j T hT hK
    have ho := (h.occurs j T hT hK).toOccurs
    refine ⟨(occ j).decl, (occ j).idx, (occ j).src, ho.hist, ho.src_mem, ?_, rfl, ?_⟩
    · rw [h.tyName j T hT hK]; rfl
    · rw [h.member j T hT hK]
      exact (occ j).member_ctors_complete D.header R (h.ctorName_inv j T hT hK)

end

namespace InductiveDeclExamples
section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- **§7.4 A producer site, after the edit.**  The nine surviving clauses are copied by name from
the existing `ntreeAux_built`; the whole of the site's diff is `hyg := ntreeK_hyg h` replacing
`fields_noK := …`.  (That the `with` notation transfers them is itself the measurement: the two
structures agree on every field but the last.) -/
theorem ntreeAux_built' : ntreeAux.Built' ntreeRestore ntreeK env₁ (fun _ => listOcc) :=
  { (ntreeAux_built h) with hyg := ntreeK_hyg h }

/-- **§7.5 Consumer 3: the anti-vacuity control.**  `Theory/Inductive/NestedFresh.lean`:133–148,
statement and proof term unchanged; the only substitution is `ntreeAux_built → ntreeAux_built'`.
The positional application `.fields_noK 1 _ rfl (by decide) C₀ hC₀ k F₀ hF₀` is byte-for-byte the
original's, which is what "the consumer accepts it unchanged" has to mean. -/
theorem fields_noK_needs_spine' :
    listOccBadSpine.decl = listOcc.decl ∧ listOccBadSpine.idx = listOcc.idx ∧
    listOccBadSpine.lvls = listOcc.lvls ∧ listOccBadSpine.auxName = listOcc.auxName ∧
    listOccBadSpine.args.length = listOcc.args.length ∧
    listOcc.Occurs env₁ ∧ listOccBadSpine.Occurs env₁ ∧
    (∀ C₀ ∈ listOcc.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK (VExpr.instAll (F₀.type.instL listOcc.lvls) listOcc.args k)) ∧
    ¬ (∀ C₀ ∈ listOccBadSpine.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK
        (VExpr.instAll (F₀.type.instL listOccBadSpine.lvls) listOccBadSpine.args k)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, (listOcc_occurs h).toOccurs, listOccBadSpine_occurs h, ?_, ?_⟩
  · exact fun C₀ hC₀ k F₀ hF₀ =>
      (ntreeAux_built' h).fields_noK 1 _ rfl (by decide) C₀ hC₀ k F₀ hF₀
  · intro hbad
    exact listOccBadSpine_not_fields_noK
      (hbad listCons (by rw [show listOccBadSpine.src.ctors = [listNil, listCons] from rfl]; simp)
        0 _ rfl)

end
end InductiveDeclExamples

/-! ### §7.6 Axiom audit of the model against the originals

`Built.toFaithful` has no `#print axioms` line at its own site, so the comparison is made here.
Both must read `[propext, Quot.sound]`; if the model's differs, the edit is not a refactor. -/

#print axioms Lean4Lean.VInductDecl'.Built.toFaithful
#print axioms Lean4Lean.VInductDecl'.Built'.fields_noK
#print axioms Lean4Lean.VInductDecl'.Built'.toFresh
#print axioms Lean4Lean.VInductDecl'.Built'.toFaithful
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_built
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_built'
#print axioms Lean4Lean.InductiveDeclExamples.fields_noK_needs_spine
#print axioms Lean4Lean.InductiveDeclExamples.fields_noK_needs_spine'

/-! ## §8 `KHyg` is not the weakest replacement — and the weakest one covers the site `KHyg` misses

Two corrections to §4 and §6 first, both **measured** against the compiled environment
(constants whose value or type applies `VInductDecl'.Built.mk`, minus the three auto-generated
recursors) rather than read off the source text.

**§8.0.1 There are five `Built.mk` sites, not six.**  `Theory/Inductive/NestedBuild.lean`
`ntreeAux_built` and `nfnAux_built`, `Theory/Inductive/RestoreBridge.lean` `nfnAuxDirty_built`,
`Theory/Inductive/MemberRedex.lean` `MRedex.QNWit.qnAux_built`, and — the only general one —
`Verify/Inductive/NestedRestoreWit.lean` `ElimNestedInductive.Result.RestoreData.mkRestore_built`.
§6.1's producer table is right at five; **§4's prose "six" is wrong**:
`Verify/Inductive/NestedOccData.lean`'s `OccData.mkRestore_built` does not apply `Built.mk`, it
delegates to `RestoreData.mkRestore_built`, so it is a *caller* of the site, not a site.  (The
same measurement confirms two of §6.1's claims: `Built.fields_noK` has exactly three users, all
consumers, and `Built.toFresh` has **zero**.)

**§8.0.2 `KHyg` narrows a proved bridge.**  Post-edit the general site takes `hyg` where it now
takes `BuiltFresh`, and its three reduced forms must supply it.  One cannot:
`Verify/Inductive/NestedFreshBridge.lean`'s `mkRestore_built_of_spine` carries
`hcc : env.ConstsClosedC`, `hK : ∀ n ∈ K, ¬ env.contains n` and `hspine` — the spine premise
*directly* — and has no route to `isNested`, because `RestoreData.isNestedName_of_mem`
(`Verify/Inductive/SpineTransfer.lean`) needs `hKB : ∀ n ∈ K, n ∈ D.blockNames`, which is exactly
the hypothesis `mkRestore_built_of_blockK` adds and `_of_spine` does without.  So §3's `KHyg`
replacement would cost `mkRestore_built_of_spine` a new hypothesis.

**§8.0.3 What all five sites actually supply is not `isNested`.**  Every one of the four
`Theory/`-side `fields_noK :=` bodies is literally
`VNestedOcc.fields_noK_of_occurs hcc occurs hK ⟨args_noK⟩ hC₀ hF₀` — `listOcc_args_noK`,
`pfnOcc_args_noK` (twice), `qnOcc_args_noK` — and the general site takes the same list through
`BuiltFresh`.  `VInductDecl'.KFresh` bundles exactly that premise list.

**It is defined in `Theory/Inductive/NestedBuild.lean` §F5, not here**, and that relocation is the
one part of this work that is not a model: a *field* of `Built` can only mention definitions
available in `Built`'s own module, so a bundle stated in this file could never become the
replacement clause.  `NestedBuild.lean` §F5 also carries `KFresh.fields_noK_of_occurs` (the
replacement projection, at the field's exact signature), `builtFresh_of_kfresh`, and
`KFresh.of_spine` — the last in the exact shape `mkRestore_built_of_spine`'s own hypotheses have,
so that after the removal that theorem's `BuiltFresh` argument becomes `KFresh.of_spine hcc hK
hspine ha` and nothing else there moves.

What is left here is the *comparison*: `KHyg` implies `KFresh` (§8.2), it is **not** implied by it
(§8.3), and the whole edit at `KFresh` is modelled (§8.4–§8.11).  Note also that
`KFresh.fields_noK_of_occurs` needs only `Occurs`, not `OccursN` — so unlike §3's route the
`KFresh` replacement does not depend on the `OccursN` retype at all.

(Numbering: what would have been §8.1 — the replacement projection — and §8.9 — `of_spine` — are
the two theorems that moved to `NestedBuild.lean` §F5, so those two labels are deliberately
absent here.  §8.12 says why the move was forced.) -/

namespace VInductDecl'
variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env : VEnv}
  {occ : Nat → VNestedOcc}

/-- **§8.2 `KHyg` implies `KFresh`**, at any `occ` whose members are `OccursN`.  So §3's
replacement is a *strengthening* of §8's, not an alternative to it. -/
theorem KFresh.of_khyg (hyg : env.KHyg K)
    (hocc : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).OccursN env) :
    D.KFresh K env occ where
  constsClosedC := hyg.constsClosedC
  notContains := hyg.notContains
  argsNoK := fun j T hT hK => (hocc j T hT hK).args_noConsts_of_hyg hyg.isNested

end VInductDecl'

#print axioms Lean4Lean.VInductDecl'.KFresh.of_khyg

/-! ### §8.3 …and `KFresh` does **not** imply `KHyg`

Widen `ntreeK` by one junk name.  `constsClosedC` is unchanged, `notContains` still holds (`Junk`
is no `listDecl` name), and `argsNoK` still holds (`listOcc.args` is `[NTree α]`, which mentions
neither companion name) — but `isNested` fails on `Junk`, by §5.2's `junkK_not_khyg`.  So the
inclusion of §8.2 is strict, and a site with the spine premise but no name discipline satisfies
`KFresh` and not `KHyg`.  That is `mkRestore_built_of_spine`'s exact position. -/

namespace InductiveDeclExamples
section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- `ntreeK ++ [`Junk]` is still undeclared at `env₁` — `ntreeK_not_contains`'s proof verbatim at
the wider list. -/
theorem junkK_not_contains :
    ∀ n ∈ (`_nested.List_1 :: [`Junk] : List Name), ¬ env₁.contains n := by
  intro n hn
  have hnm : n ∉ listDecl.allNames := by revert hn; revert n; decide
  rintro ⟨ci, hc⟩
  rw [VEnv.addInduct'_constants_of_not_mem h hnm] at hc
  exact absurd hc nofun

/-- **The separation.**  `KFresh` holds at the widened `K`; `KHyg` does not. -/
theorem kfresh_not_khyg :
    ntreeAux.KFresh (`_nested.List_1 :: [`Junk]) env₁ (fun _ => listOcc) ∧
    ¬ env₁.KHyg (`_nested.List_1 :: [`Junk]) :=
  ⟨{ constsClosedC := listEnv_constsClosedC h
     notContains := junkK_not_contains h
     argsNoK := fun _ _ _ _ => by decide },
   junkK_not_khyg⟩

end
end InductiveDeclExamples

#print axioms Lean4Lean.InductiveDeclExamples.junkK_not_contains
#print axioms Lean4Lean.InductiveDeclExamples.kfresh_not_khyg

/-! ### §8.4 The edit at `KFresh`, modelled

`Built''` is `Built` with `fields_noK` replaced by `kfresh`, exactly as §7's `Built'` replaced it
by `hyg`.  Everything §7 proved for `Built'` is re-proved here for `Built''`, with the same
proof terms — so the choice between the two replacement clauses costs the consumers nothing, and
§8.0.2 is the only thing that separates them. -/

structure VInductDecl'.Built'' (D : VInductDecl') (R : VIndRestore) (K : List Name)
    (env : VEnv) (occ : Nat → VNestedOcc) : Prop where
  member : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    T = (occ j).member D.header R
  occurs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → (occ j).OccursN env
  tyName : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    R.tyName j = (occ j).tyName
  tyLvls : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    R.tyLvls j = (occ j).lvls
  tyArgs : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    R.tyArgs j = (occ j).args
  ctorName_inv : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
    ∀ C ∈ (occ j).src.ctors, R.ctorName ((occ j).ctorName C.name) = C.name
  own : R.OwnId D K
  nodup : D.blockNames.Nodup
  /-- **The replacement clause**, at the premise list the sites already supply. -/
  kfresh : D.KFresh K env occ

section
variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env : VEnv}
  {occ : Nat → VNestedOcc}

/-- **§8.5 The replacement projection, at the old signature.** -/
theorem VInductDecl'.Built''.fields_noK (h : D.Built'' R K env occ) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ C₀ ∈ (occ j).src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
        VExpr.NoConsts K (VExpr.instAll (F₀.type.instL (occ j).lvls) (occ j).args k) :=
  h.kfresh.fields_noK_of_occurs fun j T hT hK => (h.occurs j T hT hK).toOccurs

/-- **§8.6 `Built'` gives `Built''`** — §8.2 lifted to the structures, so the two candidate edits
are ordered and not merely different. -/
theorem VInductDecl'.Built'.toBuilt'' (h : D.Built' R K env occ) : D.Built'' R K env occ :=
  { h with kfresh := VInductDecl'.KFresh.of_khyg h.hyg h.occurs }

/-- **§8.7 Consumer 1: `Built.toFresh`**, proof term unchanged. -/
theorem VInductDecl'.Built''.toFresh (h : D.Built'' R K env occ) : D.BuiltFresh K occ :=
  ⟨h.nodup, h.fields_noK⟩

/-- **§8.8 Consumer 2: `Built.toFaithful`**, proof term unchanged from
`Theory/Inductive/NestedBuild.lean`:1046 — `h.fields_noK` resolves to §8.5. -/
theorem VInductDecl'.Built''.toFaithful (h : D.Built'' R K env occ) :
    R.Faithful D env K (fun j => (occ j).decl.np) where
  ty_agree := by
    intro j T hT hK
    have ho := (h.occurs j T hT hK).toOccurs
    refine ⟨_, by rw [h.tyName j T hT hK]; exact ho.ty_const, ?_, ?_⟩
    · rw [h.tyLvls j T hT hK, ho.lvls_len]
    · rw [(occ j).instAt_eq D.header R D j _ _ rfl (h.tyLvls j T hT hK)
        (h.tyArgs j T hT hK) rfl, h.member j T hT hK]
      rfl
  ctor_agree := by
    intro j T hT hK C hC
    have ho := (h.occurs j T hT hK).toOccurs
    rw [h.member j T hT hK, VNestedOcc.member, List.mem_map] at hC
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    refine ⟨⟨(occ j).decl.uvars, C₀.type (occ j).decl (occ j).idx⟩, ?_, ?_, ?_⟩
    · rw [show ((occ j).ctor D.header R C₀).name = (occ j).ctorName C₀.name from rfl,
        h.ctorName_inv j T hT hK C₀ hC₀]
      exact ho.ctor_const C₀ hC₀
    · rw [h.tyLvls j T hT hK, ho.lvls_len]
    · rw [(occ j).instAt_eq D.header R D j _ _ rfl (h.tyLvls j T hT hK)
        (h.tyArgs j T hT hK) rfl]
      exact ((occ j).ctor_typeR D.header R D K rfl h.own h.nodup j C₀
        (h.fields_noK j T hT hK C₀ hC₀) (h.tyName j T hT hK)
        (h.tyLvls j T hT hK) (h.tyArgs j T hT hK) (ho.ctor_params C₀ hC₀) ho.args_len
        ho.lvls_len).symm
  ctors_complete := by
    intro j T hT hK
    have ho := (h.occurs j T hT hK).toOccurs
    refine ⟨(occ j).decl, (occ j).idx, (occ j).src, ho.hist, ho.src_mem, ?_, rfl, ?_⟩
    · rw [h.tyName j T hT hK]; rfl
    · rw [h.member j T hT hK]
      exact (occ j).member_ctors_complete D.header R (h.ctorName_inv j T hT hK)

end

namespace InductiveDeclExamples
section
variable {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
include h

/-- **§8.10 A producer site, after the `KFresh` edit.**  The whole diff is
`kfresh := ⟨listEnv_constsClosedC h, ntreeK_not_contains h, fun _ _ _ _ => listOcc_args_noK⟩`
replacing `fields_noK := …` — and those are the *same three arguments* the old
`fields_noK :=` body passed to `fields_noK_of_occurs`.  Nothing new is proved at the site. -/
theorem ntreeAux_built'' : ntreeAux.Built'' ntreeRestore ntreeK env₁ (fun _ => listOcc) :=
  { (ntreeAux_built h) with
    kfresh := ⟨listEnv_constsClosedC h, ntreeK_not_contains h,
      fun _ _ _ _ => listOcc_args_noK⟩ }

/-- **§8.11 Consumer 3: the anti-vacuity control**, statement and proof term unchanged from
`Theory/Inductive/NestedFresh.lean`:133–148; only `ntreeAux_built → ntreeAux_built''`. -/
theorem fields_noK_needs_spine'' :
    listOccBadSpine.decl = listOcc.decl ∧ listOccBadSpine.idx = listOcc.idx ∧
    listOccBadSpine.lvls = listOcc.lvls ∧ listOccBadSpine.auxName = listOcc.auxName ∧
    listOccBadSpine.args.length = listOcc.args.length ∧
    listOcc.Occurs env₁ ∧ listOccBadSpine.Occurs env₁ ∧
    (∀ C₀ ∈ listOcc.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK (VExpr.instAll (F₀.type.instL listOcc.lvls) listOcc.args k)) ∧
    ¬ (∀ C₀ ∈ listOccBadSpine.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK
        (VExpr.instAll (F₀.type.instL listOccBadSpine.lvls) listOccBadSpine.args k)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, (listOcc_occurs h).toOccurs, listOccBadSpine_occurs h, ?_, ?_⟩
  · exact fun C₀ hC₀ k F₀ hF₀ =>
      (ntreeAux_built'' h).fields_noK 1 _ rfl (by decide) C₀ hC₀ k F₀ hF₀
  · intro hbad
    exact listOccBadSpine_not_fields_noK
      (hbad listCons (by rw [show listOccBadSpine.src.ctors = [listNil, listCons] from rfl]; simp)
        0 _ rfl)

end
end InductiveDeclExamples

#print axioms Lean4Lean.VInductDecl'.Built''.fields_noK
#print axioms Lean4Lean.VInductDecl'.Built'.toBuilt''
#print axioms Lean4Lean.VInductDecl'.Built''.toFresh
#print axioms Lean4Lean.VInductDecl'.Built''.toFaithful
#print axioms Lean4Lean.InductiveDeclExamples.ntreeAux_built''
#print axioms Lean4Lean.InductiveDeclExamples.fields_noK_needs_spine''

/-! ### §8.12 The prerequisite no round named, and why the model could not see it

§7 modelled `Built'` and §8.4 modelled `Built''`, both in **this** file — and a model stated
downstream of `NestedBuild.lean` has every definition in scope, so neither model can detect a
module-order obstacle inside `NestedBuild.lean`.  There was one, and it applies to *both*
candidate clauses:

> `VEnv.KHyg` and `VInductDecl'.KFresh` each mention `VEnv.ConstsClosedC`, and
> `NestedBuild.lean` defined `VEnv.ConstsClosedC` at §F2.1 — **after** `VInductDecl'.Built`.  A
> field of `Built` can only mention what precedes `Built`, so until `ConstsClosedC` was lifted,
> neither clause could be a field of `Built` at all.

Measured, not reasoned: placing `KFresh` above `Built` with `ConstsClosedC` left at §F2.1 produced
four `invalidField` errors and turned two theorems `sorryAx`-tainted.  `NestedBuild.lean` now
declares `VEnv.ConstsClosedC` and `VInductDecl'.KFresh` in Part 6 immediately above `Built`, with
`KFresh`'s three theorems left at §F5 where `VNestedOcc.fields_noK_of_occurs` is in scope.  That is
a pure relocation: no statement changed, and the full build is green.

One consequence of the split is worth stating because it is part of the removal's diff:
`VInductDecl'.Built.toFresh` sits *between* `Built` and §F5, so it cannot read the replacement
projection and the removal must move it below §F5 or delete it.  **Delete it**: measured against
the compiled environment, `Built.toFresh` has zero users — its only occurrence is its own
declaration.  §7.2 and §8.7 port it only to show the port is free. -/

/-! ## §9 The removal landed (2026-09-03), and the model is provably the landed structure

§5–§8 assessed the removal; it is now **applied**.  `VInductDecl'.Built`'s last clause is
`kfresh : D.KFresh K env occ`, `Built.fields_noK` is the §F5 theorem in `NestedBuild.lean`,
`Built.toFresh` is deleted, and the five `Built.mk` sites and the two general-bridge families
carry the substitution.  Full `lake build` green, guards `24 / whitelist ✓ INCOMPLETE / 2-2`,
census 13 holes, and **no printed declaration in the repo changed or lost an axiom** (measured:
0 removed, 0 changed over 1496 → 1526 `#print axioms` lines).

### §9.1 `Built''` **is** `Built` — the model was faithful, not merely analogous

§8.4–§8.11 checked each consumer against `Built''` before the field moved.  Now that the field has
moved, the two structures can be compared directly, and the comparison is an *equivalence* rather
than a claim about proof terms: field-for-field, `{ h with }` in both directions.  This is the
strongest form the "the model matched the edit" claim can take, and it is only statable after the
edit lands — which is why it was not in §8. -/

section
variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env : VEnv}
  {occ : Nat → VNestedOcc}

/-- **The landed `Built` gives the model.** -/
theorem VInductDecl'.Built.toBuilt'' (h : D.Built R K env occ) : D.Built'' R K env occ :=
  { h with }

/-- **…and the model gives the landed `Built`.**  Together with `Built.toBuilt''` this says
`Built''` and `Built` have the same inhabitants, so every §8 consumer result transfers verbatim. -/
theorem VInductDecl'.Built''.toBuilt (h : D.Built'' R K env occ) : D.Built R K env occ :=
  { h with }

/-- **`Built'` (the rejected `KHyg` variant) still gives the landed `Built`** — via §8.6.  This is
the ordering §8.2/§8.3 established, now at the real structure: anything a site could prove with
`KHyg` in the field it can prove with `KFresh` there, and `kfresh_not_khyg` says the converse
fails. -/
theorem VInductDecl'.Built'.toBuilt (h : D.Built' R K env occ) : D.Built R K env occ :=
  h.toBuilt''.toBuilt

end

/-! ### §9.2 Anti-vacuity of the landed clause, stated in three separate parts

Per `docs/vacuity-ledger.md` §0 and row 193b these are three different claims and are stated
separately.  **(a) inhabitation**, **(b) hole-freeness**, **(c) consistency of the witness
environment**.

(a) is below and is unconditional — the `addInduct'` hypothesis every §4/§8 witness carries is
discharged by `listDecl_env_exists'`, so these are `∃`-statements with no hypotheses left.

(b) is separate and is read off `#print axioms`: every declaration in this file and in
`NestedBuild.lean` reports `[propext, Quot.sound]` or weaker, **no `sorryAx`**, so no witness
routes through a hole.  Hole-freeness is *not* implied by (a) and (a) is not implied by (b).

(c) is separate again: the witness environment is `VEnv.empty.addInduct' listDecl`, and
`listEnv_constsClosedC` / `listEnv_ordered` are proved of it, so it is not the degenerate
"declare everything" environment.  It declares no `univInhab`-style inhabitation axiom.  (A
neighbouring corner's witness environment *is* inconsistent; this one is not.) -/

namespace InductiveDeclExamples

/-- **(a) `VInductDecl'.KFresh` is inhabited at a non-empty `K`, unconditionally.** -/
theorem kfresh_inhabited :
    ∃ (D : VInductDecl') (K : List Name) (env : VEnv) (occ : Nat → VNestedOcc),
      D.KFresh K env occ ∧ K ≠ [] :=
  let ⟨_, he⟩ := listDecl_env_exists'
  ⟨ntreeAux, ntreeK, _, fun _ => listOcc,
    ⟨listEnv_constsClosedC he, ntreeK_not_contains he, fun _ _ _ _ => listOcc_args_noK⟩,
    by decide⟩

/-- **(a′) …and so is the post-removal `VInductDecl'.Built` itself**, at the same non-empty `K`.
This is the clause that matters: a field removal that left `Built` uninhabited would make every
consumer vacuously true, and `#print axioms` would not notice. -/
theorem built_inhabited :
    ∃ (D : VInductDecl') (R : VIndRestore) (K : List Name) (env : VEnv) (occ : Nat → VNestedOcc),
      D.Built R K env occ ∧ K ≠ [] :=
  let ⟨_, he⟩ := listDecl_env_exists'
  ⟨ntreeAux, ntreeRestore, ntreeK, _, fun _ => listOcc, ntreeAux_built he, by decide⟩

/-- **(a″) `Built.fields_noK` still *fires*** — the theorem that replaced the field is not merely
well-typed, it produces the clause at the witness, at the same instantiation
`fields_noK_needs_spine` uses.  Without this, §9.1's equivalence would be compatible with a
`Built` whose `fields_noK` projection is unusable. -/
theorem built_fields_noK_fires {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ∀ C₀ ∈ listOcc.src.ctors, ∀ (k : Nat) (F₀ : VIndField), C₀.fields[k]? = some F₀ →
      VExpr.NoConsts ntreeK (VExpr.instAll (F₀.type.instL listOcc.lvls) listOcc.args k) :=
  fun C₀ hC₀ k F₀ hF₀ => (ntreeAux_built h).fields_noK 1 _ rfl (by decide) C₀ hC₀ k F₀ hF₀

end InductiveDeclExamples

#print axioms Lean4Lean.VInductDecl'.Built.toBuilt''
#print axioms Lean4Lean.VInductDecl'.Built''.toBuilt
#print axioms Lean4Lean.VInductDecl'.Built'.toBuilt
#print axioms Lean4Lean.InductiveDeclExamples.kfresh_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.built_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.built_fields_noK_fires

end Lean4Lean
