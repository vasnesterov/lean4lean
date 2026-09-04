import Lean4Lean.Verify.Inductive.ExprConstructionScope

/-!
# `TrIndDeclN.trCtors`, in general: `trS_tac` re-expressed as a theorem

`Verify/Environment/InductR.lean:777` has `trS_tac`, the five-case macro that discharges all four
existing `TrExprS` bridges.  It is **reflection, not a theorem**: it is a `first | …` alternation
run against a *concrete closed `Expr` literal* spliced by `exprOf%`, and its typing side
conditions are handed to `type_tac` (`Theory/Typing/Meta.lean:37`, "TODO: write an actual
tactic"), which is a second reflection engine of the same kind.  Neither can be applied to a
symbolic `c.type`, so `TrIndDeclN.trCtors` -- the last open field of the nested translation
relation -- could not be reached through them.

This file is that pair of tactics re-expressed as one induction, following the plan
`Verify/Inductive/ExprConstructionScope.lean`'s header sets out (that file supplies §1, the
all-`vlam` context; §2 onwards are here).

## The hard floor, and why the result is not circular

`TrExprS` is **not purely syntactic**: `.app` carries two `VEnv.HasType` premises and
`.forallE` two `VEnv.IsType`s.  So no `Expr → VExpr` function can have a soundness theorem that
assumes nothing about typing -- and this is the one thing about the construction that had to be
got right rather than assumed.

The way out is **not** to assume typing.  It is to make the function an *inferencer*:
`ctorTr?` returns the translation **together with its type**, and `ctorTr?_sound` produces both
`TrExprS` and a `VEnv.HasType` for that type, in one induction, from a hypothesis that mentions
only `VEnv.constants`.  The `.app` case then discharges `HasType f' (.forallE A B)` from the
inductive hypothesis for `f` -- because on this fragment the inferred type of `f` is
*syntactically* a `∀`, so there is no whnf, no `IsDefEq`, and no contact with the checker -- and
`HasType a' A` from the inductive hypothesis for `a` plus the *decidable* check `A = a`'s
inferred type.  So the obligation assumed (a `VConstant` per `Expr.const` leaf) is **strictly
weaker** than what is produced (`TrExprS` *and* `HasType`), and §7 records that as a
machine-checked claim rather than a boast: `ctorTr?_hasType` is a corollary, and the input
hypothesis is `Prop`-free of `HasType` by inspection of `ConstLookup`.

That is the whole payoff over the poisoned route.  `TypeChecker.checkType.WF` (cone 18795, 8
holes) and `TrExprS.weakFV_inv` (cone 8653, 5 holes) both carry `VEnv.IsDefEq.uniq` and
`uniqU`; nothing here touches either, because nothing here ever needs to *compare* two types up
to conversion.  It only ever reads one off.

## What is covered, and what the omitted constructors would need

The fragment is `.sort | .bvar | .const | .app | .forallE | .mdata` -- exactly `trS_tac`'s five
cases plus the pass-through.  §6 records the boundary and says, per omitted constructor, what
admitting it would cost.  The short version:

* `.lam` needs the body's inferred type to be *abstracted* back into a `.forallE`, which is
  fine; the reason it is omitted is that a constructor type never has one, and adding it would
  need no new idea.
* `.letE` translates to the *substituted* body, so the inferencer would have to instantiate, and
  `TrExprS.letE`'s premise is a `HasType` of the value at the declared type -- again available,
  but the `VLCtx` stops being an all-`vlam` one, so §1's free lookups are lost.
* `.proj` needs `TrProj`, which reads the inductive block's stored data; `.lit` needs
  `VEnv.ContainsLits`; `.fvar` needs a non-`vlam` context entry.  These three are genuine
  additions, not bookkeeping, and none of them occurs in a constructor type.

§3 is the member-level statement, §4 the `TrIndDeclN.trCtors` field producer plus an `↔` on the
fragment, §5 the **arity-0** witness at the parameterised nested block `ntreeAux`, reached
through §4.  This file does **not** import `Verify/Inductive/FlipConstruct`, so
`tr_ntreeNodeType` is not in scope, and it uses neither `trS_tac` nor `type_tac` anywhere.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §2 The inferencer

Two one-line destructors first, so that every inversion in §2b is a named lemma rather than a
`split`. -/

/-- `some (A, B)` exactly when the inferred type is *syntactically* a `∀`.  This is the whole
reason the `.app` case needs no conversion: `TrExprS.app`'s premise is
`HasType f' (.forallE A B)`, and here the `.forallE` is read off, not derived. -/
def piOf? : VExpr → Option (VExpr × VExpr)
  | .forallE A B => some (A, B)
  | _ => none

/-- …and `some u` exactly when it is syntactically a sort, for `.forallE`'s two `IsType`s. -/
def sortOf? : VExpr → Option VLevel
  | .sort u => some u
  | _ => none

theorem piOf?_eq_some {e : VExpr} {A B : VExpr} (h : piOf? e = some (A, B)) :
    e = .forallE A B := by
  cases e <;> simp [piOf?] at h
  simp [h.1, h.2]

theorem sortOf?_eq_some {e : VExpr} {u : VLevel} (h : sortOf? e = some u) : e = .sort u := by
  cases e <;> simp [sortOf?] at h
  simp [h]

/-- **The inferencer.**  `Γc` is the environment, entering as a plain `Name → Option VConstant`
rather than as a `VEnv`, so that the function still *computes* at a concrete block (§5's witness
is `rfl`) and the environment content appears only in `ConstLookup`.  `Γ` is the all-`vlam`
context of §1, as a `List VExpr`.

It returns **the translation and its type**.  Every case is the corresponding `TrExprS`
constructor read forwards, with the two destructors above standing where `trS_tac` would have
called `type_tac`. -/
def ctorTr? (Γc : Name → Option VConstant) (Us : List Name) :
    Expr → List VExpr → Option (VExpr × VExpr)
  | .sort u, _ => (VLevel.ofLevel Us u).map fun u' => (.sort u', .sort (.succ u'))
  | .bvar i, Γ => (bvarCtx Γ).find? (.inl i)
  | .const c us, _ =>
    (Γc c).bind fun ci =>
    (us.mapM (VLevel.ofLevel Us)).bind fun us' =>
    if us.length = ci.uvars then some (.const c us', ci.type.instL us') else none
  | .app f a, Γ =>
    (ctorTr? Γc Us f Γ).bind fun p =>
    (ctorTr? Γc Us a Γ).bind fun q =>
    (piOf? p.2).bind fun AB =>
    if AB.1 = q.2 then some (.app p.1 q.1, AB.2.inst q.1) else none
  | .forallE _ d b _, Γ =>
    (ctorTr? Γc Us d Γ).bind fun p =>
    (sortOf? p.2).bind fun u =>
    (ctorTr? Γc Us b (p.1 :: Γ)).bind fun q =>
    (sortOf? q.2).map fun v => (.forallE p.1 q.1, .sort (.imax u v))
  | .mdata _ e, Γ => ctorTr? Γc Us e Γ
  | _, _ => none

/-- The environment hypothesis, in full.  It is a **leaf-lookup discharge** and nothing else:
no `HasType`, no `IsType`, no `Ordered`, no `VEnv.WF`.  Compare the hand-built bridges, whose
entire hand content is one of these per `Expr.const` leaf (`tr_ntreeNodeType` takes two). -/
def ConstLookup (Γc : Name → Option VConstant) (env : VEnv) : Prop :=
  ∀ c ci, Γc c = some ci → env.constants c = some ci

/-! ## §2b Soundness: one induction for both `TrExprS` and `HasType` -/

/-- **THE THEOREM.**  `trS_tac` and `type_tac`, together, as an induction over the fragment.

The conjunction is essential and is the finding: the `TrExprS` half alone is not provable by
this induction, because `TrExprS.app`'s premises are about types, and the `HasType` half is
exactly what supplies them.  Conversely the `HasType` half is what makes the hypothesis cheap --
it is *produced*, not assumed. -/
theorem ctorTr?_sound {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    (hΓc : ConstLookup Γc env) :
    ∀ {e : Expr} {Γ : List VExpr} {e' t' : VExpr}, ctorTr? Γc Us e Γ = some (e', t') →
      TrExprS env Us (bvarCtx Γ) e e' ∧ env.HasType Us.length Γ e' t' := by
  intro e
  induction e with
  | sort u =>
    intro Γ e' t' h
    simp [ctorTr?, Option.map_eq_some_iff] at h
    obtain ⟨u', hu, rfl, rfl⟩ := h
    exact ⟨.sort hu, .sort (VLevel.WF.of_ofLevel hu)⟩
  | bvar i =>
    intro Γ e' t' h
    rw [show ctorTr? Γc Us (.bvar i) Γ = (bvarCtx Γ).find? (.inl i) from rfl] at h
    obtain ⟨rfl, hl⟩ := bvarCtx_find? h
    exact ⟨.bvar h, .bvar hl⟩
  | const c us =>
    intro Γ e' t' h
    simp only [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨ci, hci, us', hus, h⟩ := h
    split at h
    · next hlen =>
      cases h
      exact ⟨.const (hΓc _ _ hci) hus hlen,
        .const (hΓc _ _ hci) (VLevel.WF.of_mapM_ofLevel hus)
          ((List.Forall₂.length_eq (List.mapM_eq_some.1 hus)).symm.trans hlen)⟩
    · exact absurd h nofun
  | app f a ihf iha =>
    intro Γ e' t' h
    simp only [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, q, hq, AB, hAB, h⟩ := h
    split at h
    · next heq =>
      cases h
      obtain ⟨htf, hTf⟩ := ihf hp
      obtain ⟨hta, hTa⟩ := iha hq
      have hpi : p.2 = .forallE AB.1 AB.2 := piOf?_eq_some (by rw [hAB])
      rw [hpi] at hTf
      rw [heq] at hTf
      refine ⟨.app (by rw [bvarCtx_toCtx]; exact hTf) (by rw [bvarCtx_toCtx]; exact hTa)
        htf hta, .app hTf hTa⟩
    · exact absurd h nofun
  | forallE nm d b bi ihd ihb =>
    intro Γ e' t' h
    simp only [ctorTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, u, hu, q, hq, v, hv, h⟩ := h
    cases h
    obtain ⟨htd, hTd⟩ := ihd hp
    obtain ⟨htb, hTb⟩ := ihb hq
    rw [sortOf?_eq_some hu] at hTd
    rw [sortOf?_eq_some hv] at hTb
    refine ⟨.forallE (by rw [bvarCtx_toCtx]; exact ⟨_, hTd⟩)
      (by rw [bvarCtx_toCtx]; exact ⟨_, hTb⟩) htd (by rw [← bvarCtx_cons]; exact htb),
      .forallE hTd hTb⟩
  | mdata dt e ih =>
    intro Γ e' t' h
    rw [show ctorTr? Γc Us (.mdata dt e) Γ = ctorTr? Γc Us e Γ from rfl] at h
    obtain ⟨ht, hT⟩ := ih h
    exact ⟨.mdata ht, hT⟩
  | fvar | mvar | lam | letE | lit | proj =>
    intro Γ e' t' h; simp [ctorTr?] at h

/-- The `TrExprS` half, which is what `TrIndCtorR` asks for. -/
theorem trExprS_of_ctorTr {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    (hΓc : ConstLookup Γc env) {e : Expr} {e' t' : VExpr}
    (h : ctorTr? Γc Us e [] = some (e', t')) : TrExprS env Us [] e e' :=
  (ctorTr?_sound hΓc h).1

/-- The typing half, kept as a named corollary because it is the half that makes the
hypothesis cheap: the fragment's terms are **typed**, at the very environment the lookups speak
about, with `Ordered` nowhere in sight. -/
theorem ctorTr?_hasType {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    (hΓc : ConstLookup Γc env) {e : Expr} {Γ : List VExpr} {e' t' : VExpr}
    (h : ctorTr? Γc Us e Γ = some (e', t')) : env.HasType Us.length Γ e' t' :=
  (ctorTr?_sound hΓc h).2

/-- Everything in the fragment is `.proj`-free, so `TrExprS.unique` applies to it — which is
what makes §4's `↔` possible. -/
theorem isUnique_of_ctorTr {Γc : Name → Option VConstant} {Us : List Name} :
    ∀ {e : Expr} {Γ : List VExpr} {p : VExpr × VExpr}, ctorTr? Γc Us e Γ = some p →
      TrExprS.IsUnique e := by
  intro e
  induction e with
  | sort | bvar | const => intro _ _ _; trivial
  | app f a ihf iha =>
    intro Γ p h
    simp only [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨p₁, hp, q, hq, _⟩ := h
    exact ⟨ihf hp, iha hq⟩
  | forallE nm d b bi ihd ihb =>
    intro Γ p h
    simp only [ctorTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p₁, hp, u, hu, q, hq, _⟩ := h
    exact ⟨ihd hp, ihb hq⟩
  | mdata dt e ih =>
    intro Γ p h
    rw [show ctorTr? Γc Us (.mdata dt e) Γ = ctorTr? Γc Us e Γ from rfl] at h
    exact ih h
  | fvar | mvar | lam | letE | lit | proj => intro Γ p h; simp [ctorTr?] at h

/-! ## §3 The member-level obligation -/

/-- `TrIndCtorR`, discharged for one constructor. -/
theorem trIndCtorR_of_ctorTr {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    {D : VInductDecl'} {R : VIndRestore} {j : Nat} {c : Constructor} {C : VIndCtor}
    (hΓc : ConstLookup Γc env) (hname : c.name = R.ctorName C.name)
    {t' : VExpr} (h : ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')) :
    TrIndCtorR env Us D R j c C :=
  ⟨hname, trExprS_of_ctorTr hΓc h⟩

/-- …and the converse, on the fragment: the stored type is **forced** to be what `ctorTr?`
computes, so there is no cheaper `C` and nothing left to re-attack at a constructor in the
fragment. -/
theorem trIndCtorR_iff_of_ctorTr {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    {D : VInductDecl'} {R : VIndRestore} {j : Nat} {c : Constructor} {C : VIndCtor}
    (hΓc : ConstLookup Γc env) {ct t' : VExpr}
    (h : ctorTr? Γc Us c.type [] = some (ct, t')) :
    TrIndCtorR env Us D R j c C ↔ (c.name = R.ctorName C.name ∧ C.typeR D R j = ct) := by
  refine ⟨fun ⟨hn, htr⟩ => ⟨hn, TrExprS.unique (isUnique_of_ctorTr h) htr
    (trExprS_of_ctorTr hΓc h)⟩, fun ⟨hn, he⟩ => ⟨hn, ?_⟩⟩
  exact he ▸ trExprS_of_ctorTr hΓc h

/-! ## §4 The field -/

/-- **`TrIndDeclN.trCtors`, discharged.**  The statement is the field's text verbatim, including
its staging over `env.addIndTypesC D K = some env₁`; the environment hypothesis is one
`ConstLookup` per staged environment, and the per-constructor data is a *computation*. -/
theorem trCtors_of_ctorTr {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {Γc : Name → Option VConstant}
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁)
    (h : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')) :
    ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      TrIndCtorR env₁ Us D R j c C := by
  intro env₁ hst j t T ht hT q c C hc hC
  obtain ⟨hn, t', htr⟩ := h j t T ht hT q c C hc hC
  exact trIndCtorR_of_ctorTr (hΓc env₁ hst) hn htr

/-- …and the same as an `↔` wherever the fragment applies: on this class the field is settled in
both directions against a **decidable** equation. -/
theorem trCtors_iff_of_ctorTr {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {Γc : Name → Option VConstant}
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁)
    (hfrag : ∀ (j : Nat) t, types[j]? = some t → ∀ (q : Nat) c, t.ctors[q]? = some c →
      ∃ p, ctorTr? Γc Us c.type [] = some p)
    (hne : ∃ env₁, env.addIndTypesC D K = some env₁) :
    (∀ env₁, env.addIndTypesC D K = some env₁ →
      ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us D R j c C) ↔
    (∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')) := by
  refine ⟨fun H j t T ht hT q c C hc hC => ?_, trCtors_of_ctorTr hΓc⟩
  obtain ⟨env₁, hst⟩ := hne
  obtain ⟨⟨ct, t'⟩, hp⟩ := hfrag j t ht q c hc
  obtain ⟨hn, he⟩ := (trIndCtorR_iff_of_ctorTr (hΓc env₁ hst) hp).1 (H env₁ hst j t T ht hT q c C hc hC)
  exact ⟨hn, t', he ▸ hp⟩

/-! ## §4a Which blocks this covers, as a checkable predicate

`CtorsInFragment` is `trCtors_iff_of_ctorTr`'s `hfrag` under a name, so that "the class where
§4 applies" is a proposition one *evaluates* at a block rather than a paragraph one trusts.  For
a concrete `types` and `Γc` it reduces to a finite conjunction of `Option` computations.

The prose version: a block is covered when every constructor type it declares is built from
`.sort`, `.bvar`, `.const`, `.app`, `.forallE` and `.mdata`, each `.const` leaf is in `Γc`, and
every application in it has its function's inferred type *syntactically* a `∀`.  That is every
non-indexed constructor whose fields are sorts, bound variables, or a declared constant applied
to such — which covers both nested blocks in this repo (§4b), `NTree.node`'s nested
`List (NTree α)` field included.  It excludes nothing that a constructor type can contain except
what §6 lists. -/

def CtorsInFragment (Γc : Name → Option VConstant) (Us : List Name)
    (types : List InductiveType) : Prop :=
  ∀ (j : Nat) t, types[j]? = some t → ∀ (q : Nat) c, t.ctors[q]? = some c →
    ∃ p, ctorTr? Γc Us c.type [] = some p

theorem trCtors_iff_of_fragment {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {Γc : Name → Option VConstant}
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁)
    (hfrag : CtorsInFragment Γc Us types)
    (hne : ∃ env₁, env.addIndTypesC D K = some env₁) :
    (∀ env₁, env.addIndTypesC D K = some env₁ →
      ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us D R j c C) ↔
    (∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTr? Γc Us c.type [] = some (C.typeR D R j, t')) :=
  trCtors_iff_of_ctorTr hΓc hfrag hne

/-! ## §4b The two nested blocks in this repo are both in the fragment

`ntreeAux` (`uvars = 1`, `params = [Type u]`, the parameterised one) and `nfnAux` (`uvars = 0`,
`params = []`, the degenerate one).  Both by computation. -/

namespace InductiveDeclExamples

/-- `NTree`'s constructor list is in the fragment, at the two-constant environment of §5. -/
theorem ntree_ctorsInFragment :
    CtorsInFragment (fun n =>
        if n = ``List then some ⟨1, listType.type⟩
        else if n = ``NTree then
          some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩
        else none) [`u] [ntreeIndType] := by
  rintro (_ | j) t ht
  · cases ht
    rintro (_ | q) c hc
    · cases hc; exact ⟨_, rfl⟩
    · simp [ntreeIndType] at hc
  · simp at ht

end InductiveDeclExamples

namespace NestedWit
open InductiveDeclExamples

/-- …and so is `NFn`'s, the `uvars = 0` sibling: the fragment is not an artefact of the
parameterised block.  `NFn.node : PFn NFn → NFn`, so the two `.const` leaves are `PFn` and the
block's own `NFn`. -/
theorem nfn_ctorsInFragment :
    CtorsInFragment (fun n =>
        if n = ``PFn then some ⟨0, pfnType.type⟩
        else if n = ``NFn then some ⟨0, .sort (.succ .zero)⟩
        else none) [] [nfnIndType] := by
  rintro (_ | j) t ht
  · cases ht
    rintro (_ | q) c hc
    · cases hc; exact ⟨_, rfl⟩
    · simp [nfnIndType] at hc
  · simp at ht

/-- The `nfnAux` computation, so that the degenerate block's field content is an equation
between computed data too. -/
theorem nfnNode_ctorTr : ∃ t',
    ctorTr? (fun n =>
        if n = ``PFn then some ⟨0, pfnType.type⟩
        else if n = ``NFn then some ⟨0, .sort (.succ .zero)⟩
        else none) []
      (exprOf% NFn.node) [] = some (nfnNode.typeR nfnAux nfnRestore 0, t') := ⟨_, rfl⟩

/-- **`tr_nodeType` recovered.**  `Verify/Environment/InductR.lean:818`'s bridge, from the same
two hypotheses, through §2b instead of through `trS_tac`. -/
theorem tr_nodeType_general {env : VEnv}
    (hPFn : env.constants ``PFn = some ⟨0, pfnType.type⟩)
    (hNFn : env.constants ``NFn = some ⟨0, .sort (.succ .zero)⟩) :
    TrExprS env [] [] (exprOf% NFn.node) (nfnNode.typeR nfnAux nfnRestore 0) := by
  refine trExprS_of_ctorTr (Γc := fun n =>
    if n = ``PFn then some ⟨0, pfnType.type⟩
    else if n = ``NFn then some ⟨0, .sort (.succ .zero)⟩ else none) ?_ nfnNode_ctorTr.choose_spec
  intro c ci hc
  simp only at hc
  split at hc
  · next hP => cases hc; subst hP; exact hPFn
  · split at hc
    · next hN => cases hc; subst hN; exact hNFn
    · exact absurd hc nofun

end NestedWit

/-! ## §5 The arity-0 witness, at the parameterised nested block

`ntreeAux` — `NTree α` with a `List (NTree α)` field, `uvars = 1`, `params = [Type u]`, the block
Lean's own kernel runs the nested elimination on.  Deliberately **not** `nfnAux`, which has
`uvars = 0` and `params = []` and would make every level and parameter question invisible.

Reached through §4 with no block lemma: this file does not import
`Verify/Inductive/FlipConstruct`, so `tr_ntreeNodeType` is **not in scope**, and no proof below
uses `trS_tac` or `type_tac`. -/

namespace InductiveDeclExamples

/-- The environment, as `ctorTr?` reads it: the two constants `NTree.node`'s stored type
mentions.  Exactly the two `env.constants … = some …` hypotheses `tr_ntreeNodeType` takes. -/
def ntreeGc : Name → Option VConstant := fun n =>
  if n = ``List then some ⟨1, listType.type⟩
  else if n = ``NTree then
    some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩
  else none

/-- The block's own type constant list, so that §5's `List.Mem.head` is against a computed
list rather than an asserted one. -/
theorem ntree_typeConstsC : ntreeAux.typeConstsC ntreeK
    = [(``NTree, ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)] := rfl

/-- **The computation.**  Lean's stored type for `NTree.node` — spliced, so it cannot drift —
runs through the inferencer to the abstract **restored** constructor type, the one whose field
was rewritten from `_nested.List_1 α` back to `List (NTree α)`.  By `rfl`: the inferencer is a
function, so at a concrete block the field's content is an equation between computed data. -/
theorem ntreeNode_ctorTr :
    ctorTr? ntreeGc [`u] (exprOf% NTree.node) []
      = some (ntreeNode.typeR ntreeAux ntreeRestore 0,
        .sort (.imax (.succ (.succ (.param 0)))
          (.imax (.succ (.param 0))
            (.imax (.succ (.param 0)) (.succ (.param 0)))))) := rfl

/-- The constructor name is unmoved by the restoration (only `_nested.List_1`'s two are). -/
theorem ntreeNode_ctorName : ntreeRestore.ctorName ntreeNode.name = ``NTree.node := rfl

/-- The environment hypothesis, met at the **staged** environment `trCtors` is quantified over:
`List` comes from the pre-block environment, `NTree` from the block's own type stage. -/
theorem ntree_constLookup {env₁ F₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁)
    (hF₁ : env₁.addIndTypesC ntreeAux ntreeK = some F₁) : ConstLookup ntreeGc F₁ := by
  intro c ci hc
  rw [ntreeGc] at hc
  split at hc
  · next hL =>
    cases hc; subst hL
    exact (VEnv.addConstList_le hF₁).constants (list_const h)
  · split at hc
    · next hN =>
      cases hc; subst hN
      exact VEnv.addConstList_constants hF₁
        (``NTree, ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩)
        (by rw [ntree_typeConstsC]; exact List.Mem.head _)
    · exact absurd hc nofun

/-- **`tr_ntreeNodeType` recovered.**  `Verify/Inductive/FlipConstruct.lean:126`'s bridge --
which this file does not import -- from the same two hypotheses, through §2b instead of through
`trS_tac`.  So the general theorem subsumes the reflection tactic on the case that matters, and
the arity-0 witness below borrows nothing. -/
theorem tr_ntreeNodeType_general {env : VEnv}
    (hList : env.constants ``List = some ⟨1, listType.type⟩)
    (hNTree : env.constants ``NTree
      = some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩) :
    TrExprS env [`u] [] (exprOf% NTree.node) (ntreeNode.typeR ntreeAux ntreeRestore 0) := by
  refine trExprS_of_ctorTr (Γc := ntreeGc) ?_ ntreeNode_ctorTr
  intro c ci hc
  rw [ntreeGc] at hc
  split at hc
  · next hL => cases hc; subst hL; exact hList
  · split at hc
    · next hN => cases hc; subst hN; exact hNTree
    · exact absurd hc nofun

/-- **`TrIndDeclN.trCtors`'s text, discharged at `ntreeAux`, through §4.** -/
theorem ntreeAux_trCtors {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ∀ F₁, env₁.addIndTypesC ntreeAux ntreeK = some F₁ →
    ∀ (j : Nat) t T, ([ntreeIndType] : List Lean.InductiveType)[j]? = some t →
      ntreeAux.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      TrIndCtorR F₁ [`u] ntreeAux ntreeRestore j c C := by
  refine trCtors_of_ctorTr (fun _ hF₁ => ntree_constLookup h hF₁) ?_
  rintro (_ | j) t T ht hT
  · cases ht
    rw [show ntreeAux.types[0]? = some
      { name := ``NTree, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
        indices := [], ctors := [ntreeNode] } from rfl] at hT
    cases hT
    rintro (_ | q) c C hc hC
    · cases hc; cases hC
      exact ⟨rfl, _, ntreeNode_ctorTr⟩
    · simp [ntreeIndType] at hc
  · simp at ht

/-- **THE WITNESS — arity 0.**  The field's text at the parameterised nested block, existentially
closed over the declaration history, with the four non-degeneracy facts beside it and an
anti-vacuity conjunct naming the one pair the clause actually bites at. -/
theorem ntreeAux_trCtors_witness :
    ∃ env₁ F₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some F₁ ∧
      -- non-degeneracy: this is not `nfnAux`
      ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
      ntreeAux.types.length = 2 ∧ ntreeNode.fields.length = 2 ∧
      -- the field, in `TrIndDeclN`'s own staging
      (∀ F, env₁.addIndTypesC ntreeAux ntreeK = some F →
        ∀ (j : Nat) t T, ([ntreeIndType] : List Lean.InductiveType)[j]? = some t →
          ntreeAux.types[j]? = some T →
        ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
          TrIndCtorR F [`u] ntreeAux ntreeRestore j c C) ∧
      -- anti-vacuity: member 0, constructor 0 is a matching pair, and the clause is about it
      (∃ t c C, ([ntreeIndType] : List Lean.InductiveType)[0]? = some t ∧
        t.ctors[0]? = some c ∧ c.name = ``NTree.node ∧
        (ntreeAux.types[0]?.map (·.ctors)) = some [C] ∧ C = ntreeNode ∧
        TrIndCtorR F₁ [`u] ntreeAux ntreeRestore 0 c C) := by
  obtain ⟨env₁, -, -, F₁, -, h, -, -, hF₁, -⟩ := ntree_stage₂_exists
  refine ⟨env₁, F₁, h, hF₁, rfl, rfl, rfl, rfl, ntreeAux_trCtors h,
    _, _, ntreeNode, rfl, rfl, rfl, rfl, rfl, ntreeAux_trCtors h F₁ hF₁ 0 _ _ rfl rfl 0 _ _ rfl rfl⟩

/-! ### §5a The environment hypothesis is load-bearing, and the block is not degenerate

Four computations.  The first two say the two lookups are each *necessary*: drop either and the
inferencer returns `none`, so §4's `ConstLookup` is not a hypothesis that could be quietly
weakened to nothing.  The last two are the anti-`nfnAux` guards in computational form. -/

/-- With no constants at all, `NTree.node`'s type does not translate. -/
example : ctorTr? (fun _ => none) [`u] (exprOf% NTree.node) [] = none := rfl

/-- With `List` alone — the pre-block environment — it still does not: the block's own member
must be declared, which is exactly why `trCtors` is staged over `addIndTypesC`. -/
example : ctorTr? (fun n => if n = ``List then some ⟨1, listType.type⟩ else none) [`u]
    (exprOf% NTree.node) [] = none := rfl

/-- The universe context is genuinely non-empty, so the `.const` cases' `us.length = ci.uvars`
check is not `0 = 0`. -/
example : ntreeGc ``NTree = some ⟨1, .forallE (.sort (.succ (.param 0)))
  (.sort (.succ (.param 0)))⟩ := rfl

/-- …and the constructor really has a nested recursive field, so the translation crosses the
restoration rather than being an identity. -/
example : (ntreeNode.fields.getD 1 default).type
    = .app (.const `_nested.List_1 [.param 0]) (.bvar 1) := rfl

end InductiveDeclExamples

/-! ## §6 The boundary, machine-checked

Six computations and one theorem.  The computations are the six `Expr` constructors the fragment
omits; the theorem is the one thing that must be said about them, namely that `ctorTr? = none` is
**incompleteness, not refutation** — outside the fragment `TrExprS` may still hold, and does. -/

example {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr} {fv : FVarId} :
    ctorTr? Γc Us (.fvar fv) Γ = none := rfl
example {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr} {mv : MVarId} :
    ctorTr? Γc Us (.mvar mv) Γ = none := rfl
example {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr}
    {n : Name} {t b : Expr} {bi : BinderInfo} : ctorTr? Γc Us (.lam n t b bi) Γ = none := rfl
example {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr}
    {n : Name} {t v b : Expr} {nd : Bool} : ctorTr? Γc Us (.letE n t v b nd) Γ = none := rfl
example {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr} {l : Literal} :
    ctorTr? Γc Us (.lit l) Γ = none := rfl
example {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr}
    {s : Name} {i : Nat} {e : Expr} : ctorTr? Γc Us (.proj s i e) Γ = none := rfl

/-- **The `.app` case reads the `∀` off syntactically**, so an application whose function's
inferred type is a `∀` only *up to conversion* is outside the fragment even when it is perfectly
well typed.  That is the exact price of never touching `VEnv.IsDefEq`, and it is why the fragment
is stated for constructor types — whose spines are always headed by a declared constant applied to
arguments, with the `∀` present syntactically — rather than for all of `Expr`. -/
theorem ctorTr?_none_of_nonSyntacticPi :
    ctorTr? (fun n => if n = `F then some ⟨0, .const `G []⟩
      else if n = `a then some ⟨0, .const `A []⟩ else none) []
      (.app (.const `F []) (.const `a [])) [] = none := rfl

/-- **`none` is not a refutation.**  A `.lam` is outside the fragment, yet its `TrExprS` holds at
every environment — so §4's `↔` is genuinely conditional on `hfrag`, and a successor extending the
fragment to `.lam` is refining an incompleteness, not repairing an error.  (What such an extension
costs is in the module docstring.) -/
theorem trExprS_lam_outside_fragment {env : VEnv} :
    ctorTr? (fun _ => none) [] (.lam `x (.sort (.succ .zero)) (.bvar 0) .default) [] = none ∧
    TrExprS env [] [] (.lam `x (.sort (.succ .zero)) (.bvar 0) .default)
      (.lam (.sort (.succ .zero)) (.bvar 0)) :=
  ⟨rfl, .lam ⟨_, .sort trivial⟩ (.sort rfl) (.bvar rfl)⟩

/-! ## §7 What the hypothesis costs against what it buys

The one thing that had to be checked rather than asserted.  §2b's hypothesis is `ConstLookup`:
a conjunction of `VEnv.constants` equations, decidable at a concrete environment, mentioning no
`HasType`, no `IsType`, no `VEnv.Ordered` and no `VEnv.WF`.  What it buys is a `TrExprS` **and** a
typing derivation.  The two theorems below are that gap made concrete at the witness: from the
same two lookups the field itself hands you, the restored constructor type is not merely
translated but **well-formed as a constant**.

So the answer to "does this need an obligation of comparable strength to what it produces?" is
**no** — and that is the whole reason the inferencer design was worth preferring to a class with
typing side conditions carried as fields. -/

namespace InductiveDeclExamples

/-- The typing half at the witness: `NTree.node`'s restored type is typed at the staged
environment, with `Ordered` nowhere assumed. -/
theorem ntreeNode_typeR_hasType {env₁ F₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (hF₁ : env₁.addIndTypesC ntreeAux ntreeK = some F₁) :
    F₁.HasType 1 [] (ntreeNode.typeR ntreeAux ntreeRestore 0)
      (.sort (.imax (.succ (.succ (.param 0)))
        (.imax (.succ (.param 0)) (.imax (.succ (.param 0)) (.succ (.param 0)))))) :=
  ctorTr?_hasType (ntree_constLookup h hF₁) ntreeNode_ctorTr

/-- **…hence the constructor constant the nested step declares is well-formed**, from two
`VEnv.constants` lookups and nothing else.  This is strictly more than `TrIndCtorR` asked for,
which is the point of §7. -/
theorem ntreeNode_constant_wf {env₁ F₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁)
    (hF₁ : env₁.addIndTypesC ntreeAux ntreeK = some F₁) :
    VConstant.WF F₁ ⟨1, ntreeNode.typeR ntreeAux ntreeRestore 0⟩ :=
  ⟨_, ntreeNode_typeR_hasType h hF₁⟩

end InductiveDeclExamples

/-! ## §8 The shape coincides with the field, checked by elaboration

`TrIndDeclN.trCtors`'s type and the conclusion of §4's producer are the same statement.  This
file does not import `TrIndDeclNProducer` (nor `FlipConstruct`), so instead of applying its
binder these two `example`s check the fit against the structure field itself. -/

example {env : VEnv} {Us : List Name} {np nn : Nat} {types : List InductiveType} {iu : Bool}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore}
    (hd : TrIndDeclN env Us np types iu nn D K R) :
    ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      TrIndCtorR env₁ Us D R j c C := hd.trCtors

example {env : VEnv} {Us : List Name} {np nn : Nat} {types : List InductiveType} {iu : Bool}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {Γc : Name → Option VConstant}
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁)
    (h : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTr? Γc Us c.type [] = some (C.typeR D R j, t'))
    (mk : (∀ env₁, env.addIndTypesC D K = some env₁ →
        ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
        ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
          TrIndCtorR env₁ Us D R j c C) →
      TrIndDeclN env Us np types iu nn D K R) :
    TrIndDeclN env Us np types iu nn D K R := mk (trCtors_of_ctorTr hΓc h)

end Lean4Lean
