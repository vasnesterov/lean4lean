/-
# `TeleCongr`: the (B)-side discharge, INSTANTIATED at a real block

The machinery this file used to hold has moved upstream, because it could not be consumed where it
sat: `TeleCongr.lean` imports `CtorBeta.lean` and `RecTyped.lean`, so everything proved here was
*downstream* of the two files that need to state the lighter obligations
(`docs/handoff-consumetele.md` §2).  What is left here is what genuinely belongs downstream —
the checks that the moved results are exercised at a witness rather than merely available.

* §1–§3 of the old file (`VEnv.TeleDefEq.of_isDefEqCtx` / `.substC` / `.weak0`,
  `VIndRestore.csubstTy_freshIn`, `VIndCtor.WF.hasArgs_params_bvars(_of_wf)`) →
  `Theory/Inductive/TeleMove2.lean`, which `CtorBeta.lean` imports.  `CtorBeta.lean`'s
  `VEnv.ctorConstsCR_wf_of_betaD` now asks for **four** data per companion-pointing recursive
  field, not five, and its own witness `ntreeAux_ctorConstsCR_wf_of_betaD` supplies four.
* §6/§6b of the old file (`VIndRestore.minorCtor_hAs`, `.minorCtorHargs_of_hargs`,
  `.minorCtorHargs_of_hargs'`) → `Theory/Inductive/RecTyped.lean` §4b/§4c, next to the
  `MinorCtorHargs` definition they lighten.  `minorCtorHargs_of_hargs'` has since been replaced by
  `minorCtor_sides_of_wf`, which is its body aimed at §5's two new side conditions instead of at
  the bundle.
* §4/§5 of the old file (`ctorConstsCR_wf_of_betaD₄` and its `ntreeAux` instance) are **deleted**:
  they were the four-component statement proved *alongside* the five-component one, and the
  four-component statement is now the only one there is.

`docs/handoff-telemove2.md` records the move and the axiom-identity measurements, and reports as
*not done* the one thing `docs/handoff-hasdrop.md` has since done: `MinorCtorHargs` no longer
carries `hAs`.  Its ripple estimate named `HTeleGen.lean`; by the time the drop was made that file
had stopped destructuring the bundle and `HTeleRecB.lean` had started, so the four error sites were
`HargsShared.lean` (3) and `HTeleRecB.lean` (1) — all inside one ownership.
-/
import Lean4Lean.Theory.Inductive.CtorBeta
import Lean4Lean.Theory.Inductive.RecTyped

namespace Lean4Lean

/-! ## §1 Anti-vacuity for (B): the side conditions hold where the telescope MOVES

`docs/vacuity-ledger.md` row 205's failure is the one to guard against here, and it is specific:
the (B) stream's first closure took a hypothesis that was **jointly unsatisfiable at every real
nested block**, and it compiled with a clean axiom line.  `RecTyped.lean` §4b's side conditions —
and, since the `hAs` drop, §5's `hσfD`/`hclFD` — are all *about* the entry `(q, t, C)`, so the
question is whether they hold together at an entry that actually carries content, not at the
degenerate one.

`ntreeAux.ctorsAll = [(0, ntreeNode), (1, nlistNil), (1, nlistCons)]`.  The entry at `q = 1` is
`nlistNil`, which has **no fields** — `RecTyped.lean`'s `ntree_minorFld_nil` supplies
`MinorFldDefEq` there for free and discloses it as degenerate, and at no fields `hAs` is `.nil`
and §4b says nothing.  So the check is run at **`q = 2`, `nlistCons`**, the companion-member
constructor with two recursive fields, where the restored telescope genuinely differs from the
source one (`ntree_nlistCons_fieldTypesR_ne`).

**What is established** (`ntree_minorCtorHargs_sides_at_cons`): all of §4b's and §5's non-data
side conditions hold *simultaneously* there, at `npJ = 1` from the block's own `Faithful` witness.
Conjuncts six and seven are exactly §5's `hσfD` and `hclFD` at this entry.
**What is not**: `hfld`, `hcbody` and `hfun`.  `hfld` is `MinorFldDefEq`, which §5 demands at every
entry and which is open at the moving entry; `hcbody`/`hfun` are `hargs`.  So §4c is a **reduction
of `MinorCtorHargs` to its two data components**, not a discharge of (B) — graded the way
`RecTyped.lean` §6c grades its own. -/

namespace InductiveDeclExamples

/-- **The entry the check is run at is not the degenerate one**: at `nlistCons` the restored field
telescope differs from the source one, so `MinorFldDefEq` there is not `TeleDefEq.refl` and
§4b's `congr_tele` step is doing real work. -/
theorem ntree_nlistCons_fieldTypesR_ne :
    nlistCons.fieldTypesR ntreeAux ntreeRestore ≠ nlistCons.fields.map (·.type) := by
  decide

/-- **`RecTyped.lean` §4c's five non-data hypotheses, jointly, at `q = 2` / `nlistCons`.**

`hfld`, `hcbody` and `hfun` are deliberately absent — they are the open data.  Everything §4c
needs *besides* them is exhibited at one block, one `R`, one `σ`, one entry. -/
theorem ntree_minorCtorHargs_sides_at_cons {env₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ntreeAux.ctorsAll[2]? = some (1, nlistCons) ∧
      (∃ T : VIndType, ntreeAux.types[1]? = some T ∧ T.name ∈ ntreeK) ∧
      ntreeAux.params.length = nlistCons.params.length ∧
      (∃ ci : VConstant, env₁.constants (ntreeRestore.ctorName nlistCons.name) = some ci ∧
        ntreeRestore.instAt ntreeAux 1 1 ci.type = nlistCons.typeR ntreeAux ntreeRestore 1) ∧
      (ntreeAux.atRecTele ntreeAux.params).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))
        = ntreeAux.atRecTele ntreeAux.params ∧
      (ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore)).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))
        = ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore) ∧
      VExpr.ClosedTele
        (ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore)) ntreeAux.np ∧
      (∀ a ∈ ntreeRestore.tyArgs 1,
        a.NoCSubst (ntreeRestore.csubst ntreeAux ntreeK)) ∧
      (∀ j, ∀ a ∈ ntreeRestore.tyArgs j, a.ClosedN ntreeAux.np) := by
  refine ⟨rfl, ⟨_, rfl, by decide⟩, rfl, ?_, rfl, rfl,
    ⟨⟨trivial, Nat.zero_lt_one⟩, ⟨trivial, trivial, Nat.one_lt_two⟩, trivial⟩, ?_,
    ntree_tyArgs_closedN_np⟩
  · obtain ⟨ci, hci, -, hagree⟩ :=
      (ntreeRestore_faithful h).ctor_agree 1 _ rfl (by decide) nlistCons
        (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨ci, hci, hagree⟩
  · intro a ha
    simp only [ntreeRestore] at ha
    simp only [List.mem_singleton, if_pos] at ha
    subst ha
    exact ⟨rfl, trivial⟩

/-- **The `NoCSubst` side condition at the companion index**, factored out of the conjunction
above so §2/§3 can call it. -/
theorem ntree_tyArgs_one_noCSubst :
    ∀ a ∈ ntreeRestore.tyArgs 1, a.NoCSubst (ntreeRestore.csubst ntreeAux ntreeK) := by
  intro a ha
  simp only [ntreeRestore] at ha
  simp only [List.mem_singleton, if_pos] at ha
  subst ha
  exact ⟨rfl, trivial⟩

/-! ## §2 …and the `hAs` conjunct itself, DERIVED at that entry

§1 exhibits the side conditions; this *uses* them.  `RecTyped.lean` §4b is applied at
`q = 2` / `nlistCons` with its three side conditions discharged (`rfl`, `rfl`, and an explicit
`ClosedTele` term), so the only remaining input is `hfld` — the `MinorFldDefEq` obligation (B)'s
closure demands at every entry anyway.

This is the difference between a discharge that is *available* and one that is *exercised*: the
`HasArgs` below **used to be** a component of `MinorCtorHargs`; since the drop it is what §5's own
proof builds, and no caller supplies it at all. -/

theorem ntree_minorCtor_hAs_at_cons {F : VEnv} {σ : CSubst} (hF : F.Ordered)
    (hσ : σ = ntreeRestore.csubst ntreeAux ntreeK)
    (hfld : ntreeRestore.MinorFldDefEq ntreeAux σ F 2 nlistCons) :
    F.HasArgs ntreeAux.recUvars
      ((VExpr.liftTele (ntreeAux.nm + 2)
          ((ntreeAux.atRecTele (nlistCons.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (ntreeAux.ihTypes 2 nlistCons).map (VExpr.substC · σ)).reverse
        ++ (((ntreeAux.minors.map (VExpr.substC · σ)).take 2).reverse
            ++ ((ntreeAux.motives.map (VExpr.substC · σ)).reverse
                ++ (ntreeAux.atRecTele ntreeAux.params).reverse)))
      (VExpr.instAllTele (ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore))
        (VExpr.bvars ((ntreeAux.ihTypes 2 nlistCons).length + nlistCons.fields.length
          + (ntreeAux.nm + 2)) ntreeAux.np) 0)
      (VExpr.bvars (ntreeAux.ihTypes 2 nlistCons).length nlistCons.fields.length) := by
  subst hσ
  exact VIndRestore.minorCtor_hAs hF hfld rfl rfl
    ⟨⟨trivial, Nat.zero_lt_one⟩, ⟨trivial, trivial, Nat.one_lt_two⟩, trivial⟩

/-! ## §3 …and the whole bundle from **two** components at that entry

`MinorCtorHargs` is now three components with `As`/`B'` pinned (`RecTyped.lean` §4,
`docs/handoff-hasdrop.md`), so §2's conjunct is no longer part of it and this section is
correspondingly *shorter than it was*: `minorCtorHargs_of_hargs` needs only `hlen` + `hagree`
(for `hpi`, through `instAt_ctor_hpi`) and the two data `hcbody`/`hfun`.  What has visibly gone
from the hypothesis list, compared with the four-component bundle, is `hF : F.Ordered`,
`hE₁o : E₁.Ordered` and `hfld : MinorFldDefEq` — `hAs`'s whole price.

`ci`/`hci`/`hagree` are the `Faithful.ctor_agree` datum, hypothesised here rather than obtained
inside because `hcbody`'s *statement* mentions `ci`.  §1 proves they are inhabited at this block, so
this is not an assumption doing hidden work: `ntree_minorCtorHargs_sides_at_cons`'s fourth conjunct
is exactly `∃ ci, hci ∧ hagree`, at `npJ = 1`. -/

theorem ntree_minorCtorHargs_of_two_at_cons {F : VEnv} {σ : CSubst} {ci : VConstant}
    (hσ : σ = ntreeRestore.csubst ntreeAux ntreeK)
    (hagree : ntreeRestore.instAt ntreeAux 1 1 ci.type = nlistCons.typeR ntreeAux ntreeRestore 1)
    (hcbody : F.HasType ntreeAux.recUvars ((ntreeAux.atRecTele ntreeAux.params).reverse)
      (ntreeAux.atRec (ntreeRestore.ctorBody ntreeAux 1 nlistCons))
      (ntreeAux.atRec (VExpr.instAll (VExpr.splitPis 1
        (ci.type.instL (ntreeRestore.tyLvls 1))).2 (ntreeRestore.tyArgs 1))))
    (hfun : F.HasType ntreeAux.recUvars
      ((VExpr.liftTele (ntreeAux.nm + 2)
          ((ntreeAux.atRecTele (nlistCons.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (ntreeAux.ihTypes 2 nlistCons).map (VExpr.substC · σ)).reverse
        ++ (((ntreeAux.minors.map (VExpr.substC · σ)).take 2).reverse
            ++ ((ntreeAux.motives.map (VExpr.substC · σ)).reverse
                ++ (ntreeAux.atRecTele ntreeAux.params).reverse)))
      ((VExpr.bvar ((ntreeAux.ihTypes 2 nlistCons).length + nlistCons.fields.length + 2
          + (ntreeAux.nm - 1 - 1))).mkApp
        ((nlistCons.args.map fun a => VExpr.shift (ntreeAux.nm + 2)
            (ntreeAux.ihTypes 2 nlistCons).length nlistCons.fields.length
            (ntreeAux.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll
          (VExpr.instAll (ntreeAux.tyAppR' ntreeRestore 1 nlistCons.fields.length
              (ntreeAux.atRecTele nlistCons.args))
            (VExpr.bvars ((ntreeAux.ihTypes 2 nlistCons).length + nlistCons.fields.length
              + (ntreeAux.nm + 2)) ntreeAux.np)
            (nlistCons.fieldTypesR ntreeAux ntreeRestore).length)
          (VExpr.bvars (ntreeAux.ihTypes 2 nlistCons).length nlistCons.fields.length))
        (.sort ntreeAux.elimLvl))) :
    ntreeRestore.MinorCtorHargs ntreeAux σ F 2 1 nlistCons := by
  subst hσ
  exact VIndRestore.minorCtorHargs_of_hargs rfl hagree hcbody hfun

/-! ## §4 …and §5's two new side conditions at that entry, through their general producer

Dropping `hAs` from the bundle moves it into `VEnv.recConstsR_wf_of_recHargsD`, which pays for it
with two **decidable** side conditions on the restoration data (`hσfD`/`hclFD`).  `RecTyped.lean`
§6 discharges them at `ntreeAux` for every entry by `rfl` and an explicit `ClosedTele` term; this
runs the *general* producer `minorCtor_sides_of_wf` at the non-degenerate entry instead, so the
`Faithful` → side-conditions chain is composed at a witness rather than merely available.

`ci` is **not** a parameter here: `Faithful.ctor_agree` supplies it, so this is arity 3 in the
staging equations and nothing else. -/

theorem ntree_minor_sides_at_cons {env₁ E₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (hE₁ : env₁.addIndTypes ntreeAux = some E₁) (hE₁o : E₁.Ordered) :
    ((ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore)).map
          (VExpr.substC · (ntreeRestore.csubst ntreeAux ntreeK))
        = ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore))
      ∧ VExpr.ClosedTele
          (ntreeAux.atRecTele (nlistCons.fieldTypesR ntreeAux ntreeRestore)) ntreeAux.np := by
  obtain ⟨ci, hci, -, hagree⟩ :=
    (ntreeRestore_faithful h).ctor_agree 1 _ rfl (by decide) nlistCons
      (List.mem_cons_of_mem _ List.mem_cons_self)
  exact VIndRestore.minorCtor_sides_of_wf (listEnv_ordered h) hE₁o (ntree_csubst_fresh h)
    ((ntreeAux_WF h).ctors E₁ hE₁ 1 _ rfl nlistCons
      (List.mem_cons_of_mem _ List.mem_cons_self))
    hci hagree ntree_tyArgs_closedN_np ntree_tyArgs_one_noCSubst

end InductiveDeclExamples

end Lean4Lean

/-! ## §5 Axiom lines

Read off the declarations' own namespaces, not composed from the path.  The moved declarations'
axiom lines are printed by their new homes (`TeleMove2.lean` §4, `RecTyped.lean` §7). -/
#print axioms Lean4Lean.InductiveDeclExamples.ntree_nlistCons_fieldTypesR_ne
#print axioms Lean4Lean.InductiveDeclExamples.ntree_minorCtorHargs_sides_at_cons
#print axioms Lean4Lean.InductiveDeclExamples.ntree_tyArgs_one_noCSubst
#print axioms Lean4Lean.InductiveDeclExamples.ntree_minorCtor_hAs_at_cons
#print axioms Lean4Lean.InductiveDeclExamples.ntree_minorCtorHargs_of_two_at_cons
#print axioms Lean4Lean.InductiveDeclExamples.ntree_minor_sides_at_cons
