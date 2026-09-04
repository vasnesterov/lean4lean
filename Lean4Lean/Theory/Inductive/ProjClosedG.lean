import Lean4Lean.Theory.Inductive.ProjGen

/-!
# `ProjClosedG`: the closedness hypothesis the *generalised* projection term needs

`VInductDecl'.ProjClosed` (`Theory/Inductive/Structure.lean`) records that a structure's
stored telescopes are closed at their declared arities, which is what makes `projTerm`
commute with `lift'`/`instN`/`instL`.  It has three fields, and they are enough for
`projCore`, whose motive and minor blocks mention only the *projected* pair `(T, C)` and
whose minor binds only `C`'s fields.

`projCoreG` (`ProjGen.lean`) pads both blocks to full length, so its minor block runs over
**every** constructor of **every** block member, and each minor binds that constructor's
induction hypotheses as well as its fields.  Two things therefore change:

* the three fields have to be quantified over the whole block, and
* `ihTypes` splices in a recursive field's stored `ξ` (`VIndRecArg.binders`) and `π`
  (`.args`), which the three fields **do not mention at all**.

The second point is not a guess: `ProjClosedGap.projClosedG_needs_recArgs`
(`ProjGenWitness.lean`) is a block satisfying all three `ProjClosed` fields whose
`minorBinders` is *not* `ClosedTele` at the spine arity, and
`ProjClosedGap.projClosed_ok_without_recArgs` is the positive control showing the failure is
exactly the recursive-field data.  So `ProjClosedG` below has a **fourth** field, and
`closedTele_minorBinders` is the consumer that fourth field exists for.

**Register.**  That witness is a counterexample to an implication between *predicates*.  It
is not a well-formed declaration (`VIndField.WF.pos`'s `some r` branch forces `r.binders`
closed at `np + i`), so no real block breaks — and indeed `projClosedG_of_wf` below derives
the fourth field from exactly that clause.  What the witness shows is that the fourth field
cannot be *omitted* from the predicate.
-/

namespace Lean4Lean

open VExpr VEnv

/-! ## A missing telescope lemma -/

/-- Weakening a telescope raises its closedness bound by the weakening's width, at any cut.
(`ClosedN.liftN` entrywise; the cut is irrelevant because `ClosedN.liftN` is unconditional.) -/
theorem VExpr.ClosedTele.liftTele :
    ∀ {As : List VExpr} {k j n : Nat}, ClosedTele As k → ClosedTele (VExpr.liftTele n As j) (k+n)
  | [], _, _, _, _ => trivial
  | _ :: As, k, j, n, h => ⟨h.1.liftN, by
      have := ClosedTele.liftTele (As := As) (k := k+1) (j := j+1) (n := n) h.2
      exact (show k+1+n = k+n+1 from by omega) ▸ this⟩

/-! ## The predicate -/

/-- **The closedness hypothesis of the generalised projection term.**

Fields 1–3 are `VInductDecl'.ProjClosed`'s three, quantified over the whole block.  Field 4
is what `ihTypes` needs and what `ProjClosed` has no way to say.

Derived, not assumed: `projClosedG_of_wf` below. -/
structure VInductDecl'.ProjClosedG (D : VInductDecl') : Prop where
  /-- The parameter telescope is closed at its own arities. -/
  params : ClosedTele D.params 0
  /-- Every block member's index telescope lives over the parameters. -/
  indices : ∀ (t : Nat) (T' : VIndType), D.types[t]? = some T' → ClosedTele T'.indices D.np
  /-- Every constructor's field telescope lives over the parameters. -/
  fields : ∀ (t : Nat) (T' : VIndType), D.types[t]? = some T' → ∀ C' ∈ T'.ctors,
    ClosedTele (C'.fields.map (·.type)) D.np
  /-- **The new field.**  A recursive field's stored `ξ` lives over `params ++ fields<i`, and
  its stored `π` over `params ++ fields<i ++ ξ`. -/
  recArgs : ∀ (t : Nat) (T' : VIndType), D.types[t]? = some T' → ∀ C' ∈ T'.ctors,
    ∀ (i : Nat) (r : VIndRecArg), (i, r) ∈ C'.recFields →
    ClosedTele r.binders (D.np + i) ∧
    ∀ a ∈ r.args, a.ClosedN (D.np + i + r.binders.length)

/-- The wide predicate restricts to the narrow one at any block member. -/
theorem VInductDecl'.ProjClosedG.toProjClosed {D : VInductDecl'} (H : D.ProjClosedG)
    {t : Nat} {T' : VIndType} (hT : D.types[t]? = some T') {C' : VIndCtor} (hC : C' ∈ T'.ctors) :
    D.ProjClosed T' C' where
  params := H.params
  indices := H.indices t T' hT
  fields := H.fields t T' hT C' hC

/-! ## The derivation

`VEnv.IsStructure.projClosed` (`Theory/Inductive/StructureClosed.lean`) derives the three
narrow fields from `IsStructure` plus `Ordered env`.  This is the same derivation at every
block member, plus the fourth field.

Three environments appear, and keeping them apart is the whole difficulty:

* `env₀`, where the block was checked — `params` and `indices` are judgements here;
* `env₁ = env₀.addIndTypes D`, where the *constructors* are checked — `fields`'s `WF` and,
  crucially, `recArgs`'s `VIndField.WF.pos` are judgements here;
* `env`, the current one, which is the only one carrying `Ordered`.

`VEnv.OnTypes … ClosedN` is **antitone** (`OnTypes.mono`), and `env₀ ≤ env₁ ≤ env`, so the
closedness fact transports down to both.  `VExpr.ClosedTele.of_onCtx₀` and
`OnCtx.ctxClosed₀` (both `StructureClosed.lean`) are exactly `Ordered`-free forms of
`of_onCtx`/`ctxClosed` taking that fact instead. -/

theorem VInductDecl'.projClosedG_of_wf {env env₀ env' : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) (hWF : D.WF env₀) (hadd : env₀.addInduct' D = some env')
    (hle : env' ≤ env) : D.ProjClosedG := by
  obtain ⟨env₁, env₂, env₃, h1, h2, h3, h4⟩ := VEnv.addInduct'_stages hadd
  have hle₀ : env₀ ≤ env := (VEnv.addInduct'_le hadd).trans hle
  have hle₁ : env₁ ≤ env :=
    ((VEnv.addIndCtors_le h2).trans ((VEnv.addIndRecs_le h3).trans
      (h4 ▸ VEnv.addIndRules_le))).trans hle
  have hc₀ : OnTypes env₀ (fun _ e A => e.ClosedN ∧ A.ClosedN) := henv.closed.mono hle₀ id
  have hc₁ : OnTypes env₁ (fun _ e A => e.ClosedN ∧ A.ClosedN) := henv.closed.mono hle₁ id
  have hctorsAll : ∀ (t : Nat) (T' : VIndType), D.types[t]? = some T' → ∀ C' ∈ T'.ctors,
      (t, C') ∈ D.ctorsAll := by
    intro t T' hT C' hC
    simp only [VInductDecl'.ctorsAll, List.mem_flatMap, List.mem_map]
    exact ⟨(T', t), List.mk_mem_zipIdx_iff_getElem?.2 hT, C', hC, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := VExpr.ClosedTele.of_onCtx₀ (Γ := []) hc₀ (by simpa using hWF.params)
    simpa using this
  · intro t T' hT
    have := VExpr.ClosedTele.of_onCtx₀ hc₀ (hWF.types T' (List.mem_of_getElem? hT)).indices
    simpa [VInductDecl'.np] using this
  · intro t T' hT C' hC
    have hCwf := hWF.ctors env₁ h1 t T' hT C' hC
    have hconst : env.constants C'.name = some ⟨D.uvars, C'.type D t⟩ :=
      hle.constants (VEnv.addInduct'_ctors hadd (hctorsAll t T' hT C' hC))
    have hcl : VExpr.ClosedN (C'.type D t) 0 := henv.closedC hconst
    rw [VIndCtor.type] at hcl
    have := (VExpr.closedTele_append.1 (VExpr.closedN_mkPi.1 hcl).1).2
    simpa [hCwf.params_len, VInductDecl'.np] using this
  · intro t T' hT C' hC i r hr
    obtain ⟨F, hF, hFr⟩ : ∃ F, C'.fields[i]? = some F ∧ F.recArg = some r := by
      simp only [VIndCtor.recFields, List.mem_filterMap, List.mem_zipIdx_iff_getElem?,
        Option.map_eq_some_iff] at hr
      obtain ⟨⟨F, i'⟩, hFi, r', hr', heq⟩ := hr
      cases heq
      exact ⟨F, hFi, hr'⟩
    have hilt : i < C'.fields.length := (List.getElem?_eq_some_iff.1 hF).1
    have hCwf := hWF.ctors env₁ h1 t T' hT C' hC
    have hFwf := hCwf.fields i F hF
    have hpos := hFwf.pos
    rw [hFr] at hpos
    obtain ⟨-, -, -, -, honctx, hres, -, -⟩ := hpos
    have hlenΓ : (((C'.fields.take i).map (·.type)).reverse ++ D.params.reverse).length
        = i + D.np := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hilt), VInductDecl'.np]
    refine ⟨?_, ?_⟩
    · have := VExpr.ClosedTele.of_onCtx₀ hc₁ honctx
      rw [hlenΓ] at this
      exact (show i + D.np = D.np + i from by omega) ▸ this
    · have hctx : CtxClosed (r.binders.reverse ++
          (((C'.fields.take i).map (·.type)).reverse ++ D.params.reverse)) :=
        OnCtx.ctxClosed₀ hc₁ honctx
      have hcl := (hres.closedN' hc₁ hctx).1
      rw [VIndRecArg.canonResult, VInductDecl'.tyApp, VExpr.closedN_mkApp] at hcl
      intro a ha
      have := hcl.2 a (List.mem_append_right _ ha)
      simp only [List.length_append, List.length_reverse, hlenΓ] at this
      exact (show D.np + i + r.binders.length = r.binders.length + (i + D.np) from by omega) ▸
        (by simpa using this)

/-- **`ProjClosedG` from the widened shape predicate**, exactly as
`VEnv.IsStructure.projClosed` gives the narrow one from the narrow predicate. -/
theorem VEnv.IsStructureG.projClosedG {env : VEnv} {S : Lean.Name} {D : VInductDecl'}
    {j : Nat} {T : VIndType} {C : VIndCtor} (henv : env.Ordered)
    (H : env.IsStructureG S D j T C) : D.ProjClosedG :=
  let ⟨_, _, hWF, hadd, hle⟩ := H.decl
  VInductDecl'.projClosedG_of_wf henv hWF hadd hle

/-- …and from the narrow one, via `IsStructure.toG`.  So `ProjClosedG` is available exactly
where `ProjClosed` is, and strictly more informative. -/
theorem VEnv.IsStructure.projClosedG {env : VEnv} {S : Lean.Name} {D : VInductDecl'}
    {T : VIndType} {C : VIndCtor} (henv : env.Ordered)
    (H : env.IsStructure S D T C) : D.ProjClosedG :=
  H.toG.projClosedG henv

/-! ## The consumer the fourth field exists for

`VExpr.lift'_instAllTele` — the step **every** `projCoreG` commutation lemma of block A runs
on — asks for `ClosedTele ((D.minorBinders q C').map (·.instL lvls)) (D.np + D.nm + q)`.
This is that statement, and it is the audit `docs/handoff-projections.md` §0.9 asked for
before the rest of block A is attempted: if the fourth field did not suffice, the predicate
would still be wrong, and finding that out costs one lemma rather than all of block A. -/

/-- `shift` entrywise raises a telescope's closedness bound by `off + d`, at any cut. -/
theorem VExpr.ClosedTele.shiftTele :
    ∀ {As : List VExpr} {k off d i j : Nat}, ClosedTele As k →
      ClosedTele (VExpr.shiftTele off d i As j) (k + off + d)
  | [], _, _, _, _, _, _ => trivial
  | _ :: As, k, off, d, i, j, h => ⟨h.1.liftN.liftN, by
      have := ClosedTele.shiftTele (As := As) (k := k+1) (off := off) (d := d) (i := i)
        (j := j+1) h.2
      exact (show k+1+off+d = k+off+d+1 from by omega) ▸ this⟩

/-- **One induction hypothesis is closed at the minor's arity.**  This is where the fourth
field of `ProjClosedG` is consumed, and the only place it is needed. -/
theorem VInductDecl'.closedN_ihType {D : VInductDecl'} {C' : VIndCtor} {q s i : Nat}
    {r : VIndRecArg} (hnm : 0 < D.nm) (hilt : i < C'.fields.length)
    (hb : VExpr.ClosedTele r.binders (D.np + i))
    (ha : ∀ a ∈ r.args, a.ClosedN (D.np + i + r.binders.length)) :
    (D.ihType q C' i r s).ClosedN (D.np + D.nm + q + C'.fields.length + s) := by
  rw [VInductDecl'.ihType, VExpr.closedN_mkPi]
  refine ⟨?_, ?_⟩
  · have h1 : VExpr.ClosedTele (D.atRecTele r.binders) (D.np + i) :=
      VExpr.ClosedTele.map_instL hb
    have h2 := VExpr.ClosedTele.shiftTele (As := D.atRecTele r.binders) (k := D.np + i)
      (off := D.nm + q) (d := C'.fields.length - i + s) (i := i) (j := 0) h1
    exact (show D.np + i + (D.nm + q) + (C'.fields.length - i + s)
      = D.np + D.nm + q + C'.fields.length + s from by omega) ▸ h2
  · have hlen : (VExpr.shiftTele (D.nm + q) (C'.fields.length - i + s) i
        (D.atRecTele r.binders) 0).length = r.binders.length := by
      simp [VInductDecl'.atRecTele]
    rw [hlen, VExpr.closedN_mkApp]
    refine ⟨?_, ?_⟩
    · show _ < _
      omega
    · intro a hmem
      rcases List.mem_append.1 hmem with hmem | hmem
      · obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hmem
        have := ((ha a' ha').instL (ls := D.selfLvls)).liftN
          (n := D.nm + q) (j := i + r.binders.length) |>.liftN
          (n := C'.fields.length - i + s) (j := r.binders.length)
        exact (show D.np + i + r.binders.length + (D.nm + q) + (C'.fields.length - i + s)
          = D.np + D.nm + q + C'.fields.length + s + r.binders.length from by omega) ▸ this
      · rw [List.mem_singleton] at hmem
        subst hmem
        rw [VExpr.closedN_mkApp_bvars (by omega)]
        show _ < _
        omega

/-- **The minor's binder telescope is closed at the spine arity** — at *any* constructor of
*any* block member, recursive fields included.  `VExpr.lift'_instAllTele`'s hypothesis. -/
theorem VInductDecl'.closedTele_minorBinders {D : VInductDecl'} (H : D.ProjClosedG)
    {t : Nat} {T' : VIndType} (hT : D.types[t]? = some T') {C' : VIndCtor} (hC : C' ∈ T'.ctors)
    (q : Nat) (lvls : List VLevel) :
    VExpr.ClosedTele ((D.minorBinders q C').map (VExpr.instL lvls)) (D.np + D.nm + q) := by
  have hnm : 0 < D.nm := Nat.lt_of_le_of_lt (Nat.zero_le t) (List.getElem?_eq_some_iff.1 hT).1
  refine VExpr.ClosedTele.map_instL ?_
  rw [VInductDecl'.minorBinders]
  refine VExpr.closedTele_append.2 ⟨?_, ?_⟩
  · have h1 : VExpr.ClosedTele (D.atRecTele (C'.fields.map (·.type))) D.np :=
      VExpr.ClosedTele.map_instL (H.fields t T' hT C' hC)
    have h2 := VExpr.ClosedTele.liftTele (As := D.atRecTele (C'.fields.map (·.type)))
      (k := D.np) (j := 0) (n := D.nm + q) h1
    exact (show D.np + (D.nm + q) = D.np + D.nm + q from by omega) ▸ h2
  · have hlen : (VExpr.liftTele (D.nm + q) (D.atRecTele (C'.fields.map (·.type))) 0).length
        = C'.fields.length := by simp [VInductDecl'.atRecTele]
    rw [hlen]
    refine VExpr.closedTele_iff.2 fun s A hA => ?_
    rw [VInductDecl'.ihTypes_getElem?, Option.map_eq_some_iff] at hA
    obtain ⟨⟨i, r⟩, hir, rfl⟩ := hA
    have hmem : (i, r) ∈ C'.recFields := List.mem_of_getElem? hir
    obtain ⟨hb, ha⟩ := H.recArgs t T' hT C' hC i r hmem
    have hilt : i < C'.fields.length := by
      simp only [VIndCtor.recFields, List.mem_filterMap, List.mem_zipIdx_iff_getElem?,
        Option.map_eq_some_iff] at hmem
      obtain ⟨⟨F, i'⟩, hFi, r', _, heq⟩ := hmem
      cases heq
      exact (List.getElem?_eq_some_iff.1 hFi).1
    exact VInductDecl'.closedN_ihType hnm hilt hb ha


end Lean4Lean
