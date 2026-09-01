import Lean4Lean.Verify.Typing.ProjGenSwap

/-!
# The two padded blocks: reading them at a slot, and typing them as a spine

`docs/handoff-projections.md`'s stale banner (2026-09-01) names the two statements that
remain between `iota_law_gen` (`Theory/Inductive/IotaGen.lean`) and wall 2:

1. **`padMinors_getElem_eq` does not exist.**  The motive block has
   `padMotives_getElem_eq`/`_ne` (`ProjGen.lean`); the minor block has no counterpart, and
   `iota_law_gen`'s `hminor : mins[q]? = some minor` is exactly that fact.
2. **Neither padded block has a `HasArgs`.**  The individual entries are typed
   (`padMotive_hasType`, `padMinor_hasType'`/`_gen`, `realMinor_hasType_atPadMotives`,
   `projMotiveTermG_hasType_swapped`) but nothing assembles either block into the recursor's
   spine, which is what `iota_law_gen`'s `hspine` needs at `nm ≥ 2`.

This file is item 1 in full, and the *motive* half of item 2.
-/

namespace Lean4Lean

open VExpr

namespace VInductDecl'

/-! ## Reading the minor block at a slot

`padMinorsAux` threads an accumulator, so entry `q` is stated over the spine
`ps ++ mots ++ acc` with `acc` the entries built *before* it.  The two lemmas below say what
that `acc` is — the block's own `take q` — which is what makes the accumulator harmless in a
consumer that only has the finished block in hand. -/

/-- **The accumulator is a prefix of the result.**  Every entry `padMinorsAux` adds goes after
`acc`, so the finished block starts with it. -/
theorem padMinorsAux_prefix (D : VInductDecl') (lvls : List VLevel) (ps mots : List VExpr)
    (X : VExpr) (i j : Nat) :
    ∀ (l : List (Nat × VIndCtor)) (q : Nat) (acc : List VExpr),
      ∃ rest, D.padMinorsAux lvls ps mots X i j l q acc = acc ++ rest ∧ rest.length = l.length
  | [], _, acc => ⟨[], by simp [padMinorsAux]⟩
  | (t, C') :: rest, q, acc => by
    obtain ⟨r, hr, hrlen⟩ := padMinorsAux_prefix D lvls ps mots X i j rest (q+1)
      (acc ++ [if t = j then D.realMinor lvls (ps ++ mots ++ acc) i q C'
        else D.padMinor lvls (ps ++ mots ++ acc) X q C'])
    refine ⟨(if t = j then D.realMinor lvls (ps ++ mots ++ acc) i q C'
      else D.padMinor lvls (ps ++ mots ++ acc) X q C') :: r, ?_, by simp [hrlen]⟩
    rw [padMinorsAux, hr]
    simp

/-- **The minor block at a slot.**  Entry `acc.length + m` of the block built from `l` is the
real minor when `l[m]`'s type index is the projected one and the padding minor otherwise, and
in both cases its spine is `ps ++ mots ++` **the block's own prefix** at that slot. -/
theorem padMinorsAux_getElem (D : VInductDecl') (lvls : List VLevel) (ps mots : List VExpr)
    (X : VExpr) (i j : Nat) :
    ∀ (l : List (Nat × VIndCtor)) (q : Nat) (acc : List VExpr) (m t : Nat) (C' : VIndCtor),
      l[m]? = some (t, C') →
      (D.padMinorsAux lvls ps mots X i j l q acc)[acc.length + m]?
        = some (if t = j then
              D.realMinor lvls (ps ++ mots ++
                (D.padMinorsAux lvls ps mots X i j l q acc).take (acc.length + m)) i (q+m) C'
            else
              D.padMinor lvls (ps ++ mots ++
                (D.padMinorsAux lvls ps mots X i j l q acc).take (acc.length + m)) X (q+m) C')
  | [], _, _, _, _, _, h => by simp at h
  | (t₀, C₀) :: rest, q, acc, 0, t, C', h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨r, hr, -⟩ := D.padMinorsAux_prefix lvls ps mots X i j rest (q+1)
      (acc ++ [if t₀ = j then D.realMinor lvls (ps ++ mots ++ acc) i q C₀
        else D.padMinor lvls (ps ++ mots ++ acc) X q C₀])
    rw [padMinorsAux, hr, Nat.add_zero, Nat.add_zero]
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.take_left]
    simp
  | (t₀, C₀) :: rest, q, acc, m+1, t, C', h => by
    simp only [List.getElem?_cons_succ] at h
    have hIH := D.padMinorsAux_getElem lvls ps mots X i j rest (q+1)
      (acc ++ [if t₀ = j then D.realMinor lvls (ps ++ mots ++ acc) i q C₀
        else D.padMinor lvls (ps ++ mots ++ acc) X q C₀]) m t C' h
    rw [List.length_append, List.length_singleton,
      show acc.length + 1 + m = acc.length + (m+1) from by omega] at hIH
    rw [padMinorsAux, hIH, show q + 1 + m = q + (m+1) from by omega]

end VInductDecl'

/-! ### The two named readings -/

variable {D : VInductDecl'} {T : VIndType} {C : VIndCtor}

/-- **`padMinors_getElem_eq`.**  Minor `q` of `projCoreG`'s block *is* the real minor of
constructor `q`, at the spine the earlier minors extend — `iota_law_gen`'s `hminor`. -/
theorem VInductDecl'.padMinors_getElem_eq (D : VInductDecl') (lvls : List VLevel)
    (ps mots : List VExpr) (X : VExpr) (i j q : Nat) (hq : D.ctorsAll[q]? = some (j, C)) :
    (D.padMinors lvls ps mots X i j)[q]?
      = some (D.realMinor lvls
          (ps ++ mots ++ (D.padMinors lvls ps mots X i j).take q) i q C) := by
  have h := D.padMinorsAux_getElem lvls ps mots X i j D.ctorsAll 0 [] q j C hq
  simpa [padMinors] using h

/-- …and at a constructor of any **other** block member it is the padding minor.  The
counterpart of `padMotives_getElem_ne`, and what keeps `padMinor_hasType_gen` non-vacuous at
the block builder. -/
theorem VInductDecl'.padMinors_getElem_ne (D : VInductDecl') (lvls : List VLevel)
    (ps mots : List VExpr) (X : VExpr) (i j q t : Nat) (C' : VIndCtor) (hq : D.ctorsAll[q]? = some (t, C'))
    (hne : t ≠ j) :
    (D.padMinors lvls ps mots X i j)[q]?
      = some (D.padMinor lvls
          (ps ++ mots ++ (D.padMinors lvls ps mots X i j).take q) X q C') := by
  have h := D.padMinorsAux_getElem lvls ps mots X i j D.ctorsAll 0 [] q t C' hq
  simpa [padMinors, hne] using h

/-! ## The motive's binder context, without the motive block

`padMotiveCtx_wf`/`motiveCtxG_wf` (`ProjGen.lean`, `ProjGenMotive.lean`) derive the motive's
own binder context from `hspine` — the parameter spine **and the `j` earlier motives**.  At
`j = 0` that is `hpsA` alone, which is why the narrow chain never noticed; at `j > 0` it makes
the motive block's assembly **circular**: the padding entries need `X` typed, `X` is the real
motive applied to its spine, and the real motive's typing needs the binder context, which by
that route needs the earlier padding entries.

The way out is that the motive's declared type does **not** depend on the earlier motives:
`motiveType j` is `liftN j` of the same type at no offset, so its instantiation at `ps ++ ms`
is `ms`-free — visibly so, since `motiveType_instL_instAll_gen`'s right-hand side does not
mention `ms`.  The two lemmas below rebuild that right-hand side from `hpsA` alone. -/

variable {env : VEnv} {U : Nat} {S : Lean.Name} {us : List VLevel}

open VInductDecl' in
/-- The **unlifted** motive type — `motiveType j` with the `liftTele j` over the earlier
motives removed — instantiated at the parameter spine.  Its normal form is
`motiveType_instL_instAll_gen`'s, verbatim: the earlier motives contribute nothing. -/
theorem motiveTypeAt_instL_instAll (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us : List VLevel} {ps : List VExpr} {i j : Nat}
    (hT : D.types.getD j default = T)
    (hus : us.length = D.uvars) (hps : ps.length = D.np) :
    VExpr.instAll ((VExpr.mkPi (D.atRecTele T.indices)
          (.forallE (D.tyApp' j T.indices.length (bvars 0 T.indices.length))
            (.sort D.elimLvl))).instL (D.projLvls C us i)) ps
      = VExpr.mkPi (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
          (.forallE ((VExpr.const T.name us).mkApp
              (ps.map (·.liftN T.indices.length) ++ VExpr.bvars 0 T.indices.length))
            (.sort (D.elimLvl.inst (D.projLvls C us i)))) := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  simp only [VInductDecl'.atRecTele, VInductDecl'.tyApp', hT,
    VExpr.instL_mkPi, VExpr.instL, VExpr.instL_mkApp,
    VExpr.map_instL_bvars, List.map_append, VExpr.instAll_mkPi, VExpr.instAll_forallE,
    VExpr.instAll_sort, VExpr.instAll_mkApp, VExpr.instAll_const,
    List.map_map, Function.comp_def, VExpr.instL_instL, hself,
    List.length_map, Nat.zero_add]
  rw [VExpr.map_instAll_bvars_top (Nat.le_refl _) (by simp [hps]),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add _)),
    List.take_of_length_le (by simp [hps])]

/-- **The motive's declared type is a type, from the parameter spine alone**, at an arbitrary
block member.  `motiveG_declType_isType` (`ProjGen.lean`) with `hspine` replaced by `hpsA`:
the `j` earlier motives are not needed, and dropping them is what breaks the circularity
above. -/
theorem motiveG_declType_isType' (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (h3 : us.length = D.uvars) {j : Nat}
    (hTj : D.types[j]? = some T) {i : Nat} {Γ ps : List VExpr}
    (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.IsType U Γ
      (VExpr.mkPi (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps)
        (.forallE ((VExpr.const T.name us).mkApp
            (ps.map (·.liftN T.indices.length) ++ VExpr.bvars 0 T.indices.length))
          (.sort (D.elimLvl.inst (D.projLvls C us i))))) := by
  have hR := hI.toRecCtx
  have hmem : T ∈ D.types := List.mem_of_getElem? hTj
  have hTd : D.types.getD j default = T := by rw [List.getD_eq_getElem?_getD, hTj]; rfl
  have W : Ctx.LiftN 0 0 (D.atRecTele D.params).reverse (D.atRecTele D.params).reverse := by
    simpa using Ctx.LiftN.zero (Γ := (D.atRecTele D.params).reverse) (n := 0) [] rfl
  have hmaj := VInductDecl'.tyApp'_hasType hR hTj (m := 0) W (by simpa using hR.onCtxParams)
  have h0 : env.IsType D.recUvars ((D.atRecTele D.params).reverse)
      (VExpr.mkPi (D.atRecTele T.indices)
        (.forallE (D.tyApp' j T.indices.length (bvars 0 T.indices.length))
          (.sort D.elimLvl))) :=
    VEnv.IsType.mkPi (by simpa using hR.onCtxIndices hmem)
      (VEnv.IsType.forallE ⟨_, by simpa using hmaj⟩
        ⟨_, VEnv.HasType.sort (Γ := _) D.elimLvl_wf⟩)
  obtain ⟨u, h0⟩ := h0
  have h1 := VEnv.HasType.instL (ls := D.projLvls C us i) (U' := U)
    (VInductDecl'.projLvls_wf h7 i) h0
  rw [List.map_reverse, VInductDecl'.atRecTele_params_instL (C := C) h3] at h1
  simp only [VExpr.instL] at h1
  have hOn := onCtxParams_instL (D := D) (us := us) henv hI h7
  have h2 := VEnv.IsDefEq.weakR henv (OnCtx.ctxClosed henv hOn) h1 Γ
  have h4 := VEnv.HasType.instAll henv hpsA h2
  rw [VExpr.instAll_sort, motiveTypeAt_instL_instAll D T C hTd h3 hps] at h4
  exact ⟨_, h4⟩

/-- The same, at the declared type as the recursor's spine presents it: instantiated at the
parameters **and any `j` earlier motives**.  `motiveType_instL_instAll_gen` is what makes the
`ms` disappear. -/
theorem motiveG_declType_isType_ms (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (h3 : us.length = D.uvars) {j : Nat}
    (hTj : D.types[j]? = some T) {i : Nat} {Γ ps ms : List VExpr}
    (hps : ps.length = D.np) (hms : ms.length = j)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.IsType U Γ
      (VExpr.instAll ((D.motiveType j).instL (D.projLvls C us i)) (ps ++ ms)) := by
  rw [motiveType_instL_instAll_gen D T C
    (by rw [List.getD_eq_getElem?_getD, hTj]; rfl) h3 hps hms]
  exact motiveG_declType_isType' (C := C) (i := i) henv hI h7 h3 hTj hps hpsA

/-- **`motiveCtxG_wf` without the motive block.**  The block builder needs the motive's binder
context *before* it has a block, and `motiveCtxG_wf`'s `hspine` cannot supply it at `j > 0`. -/
theorem motiveCtxG_wf' (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (h3 : us.length = D.uvars) {j : Nat}
    (hTj : D.types[j]? = some T) (C : VIndCtor) (i : Nat) {Γ ps : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    OnCtx (((VExpr.const T.name us).mkApp
        (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length))
      :: ((VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (env.IsType U) := by
  obtain ⟨hOn, hfa⟩ := VEnv.IsType.mkPi_inv henv hΓ
    (motiveG_declType_isType' (C := C) (i := i) henv hI h7 h3 hTj hps hpsA)
  exact ⟨hOn, (hfa.forallE_inv henv).1⟩

/-! ## `X`, and the motive block as a spine

`padMotive`'s only non-bookkeeping premise is `hX`: the projected field's type, in the shape
`mot ιs e`, at the **elimination** level.  It is the one thing the padding entries need from
the *real* motive, and with `motiveCtxG_wf'` in hand it costs no block. -/

/-- **The real motive applied to the index spine and the major premise is a type at the
elimination level.**  This is `padMotive_hasType`/`padMinor_hasType_gen`'s `hX`, and the
`projTermG` spine's `X`. -/
theorem projMotiveG_app_hasType (henv : VEnv.WF env) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors) (hname : T.name = S)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps is : List VExpr} {e : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (his : is.length = T.indices.length)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hisA : env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) is)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ is))) :
    env.HasType U Γ
      ((T.projMotive C us ps is i
          (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
            (bvars 1 is.length) j i)).mkApp (is ++ [e]))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  have hord := henv.ordered
  have hΔ := motiveCtxG_wf' hord hI h7 h3 hTj C i hΓ hps hpsA
  have hmotT := projMotiveTermG_hasType_swapped (ms := List.replicate j (VExpr.sort .zero))
    henv hI H hTj hC hname h3 h7 hi hlvi hIH hps (by simp) hpsA hΔ
  rw [motiveType_instL_instAll_gen D T C
    (by rw [List.getD_eq_getElem?_getD, hTj]; rfl) h3 hps (by simp)] at hmotT
  have hctorInst : VExpr.instAll ((VExpr.const T.name us).mkApp
      (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)) is 0
      = (VExpr.const S us).mkApp (ps ++ is) := by
    have hcancel : ∀ p : VExpr, VExpr.instAll (p.liftN T.indices.length) is 0 = p := by
      intro p; rw [← his]; exact VExpr.instAll_liftN _ _ _
    rw [VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append, List.map_map,
      VExpr.map_instAll_bvars' his, hname]
    simp [Function.comp_def, hcancel]
  have hArgs : env.HasArgs U Γ
      (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps
        ++ [(VExpr.const T.name us).mkApp
              (ps.map (·.liftN T.indices.length) ++ bvars 0 T.indices.length)])
      (is ++ [e]) := VEnv.HasArgs.concat hisA (by rw [hctorInst]; exact he)
  rw [VIndType.projMotiveG_eq' D T C us his]
  have h := VEnv.HasType.mkApp' hArgs (by simpa using hmotT)
  rwa [VExpr.instAll_sort] at h

/-- **The motive block is the recursor's motive spine**, prefix by prefix.  The real motive
sits at slot `j` (`padMotives_getElem_eq`, `projMotiveTermG_hasType_swapped`) and a padding
motive at every other (`padMotives_getElem_ne`, `padMotive_hasType`); the induction is on the
slot, and each step's `hspine` premise **is** the previous prefix.

This is `docs/handoff-projections.md`'s block B for the motive half, and the half of
`iota_law_gen`'s `hspine` that the narrow route got from `motives_eq` — which asserts a
singleton. -/
theorem padMotives_hasArgs_take (henv : VEnv.WF env) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors) (hname : T.name = S)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps is : List VExpr} {e : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (his : is.length = T.indices.length)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hisA : env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) is)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ is))) :
    ∀ t, t ≤ D.nm →
      env.HasArgs U Γ
        ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
          ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
        (ps ++ (D.padMotives T C us ps is i j
          (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
            (bvars 1 is.length) j i) e).take t)
  | 0, _ => by
    simpa [VInductDecl'.atRecTele_params_instL (C := C) h3] using hpsA
  | t+1, ht => by
    have hjlt : j < D.nm := (List.getElem?_eq_some_iff.1 hTj).1
    have htlt : t < D.nm := by omega
    have hIHt := padMotives_hasArgs_take henv hI H hTj hC hname h3 h7 hi hlvi hIH hΓ hps his
      hpsA hisA he t (by omega)
    have hlen : (D.padMotives T C us ps is i j
        (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
          (bvars 1 is.length) j i) e).length = D.nm := D.length_padMotives ..
    have htake : (D.padMotives T C us ps is i j
          (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
            (bvars 1 is.length) j i) e).take (t+1)
        = (D.padMotives T C us ps is i j
            (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
              (bvars 1 is.length) j i) e).take t
          ++ [(D.padMotives T C us ps is i j
              (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
                (bvars 1 is.length) j i) e).getD t default] := by
      have hlt : t < (D.padMotives T C us ps is i j
        (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
          (bvars 1 is.length) j i) e).length := by rw [hlen]; omega
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have htakelen : ((D.padMotives T C us ps is i j
        (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
          (bvars 1 is.length) j i) e).take t).length = t := by
      rw [List.length_take, hlen]; omega
    have hentry : env.HasType U Γ
        ((D.padMotives T C us ps is i j
          (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
            (bvars 1 is.length) j i) e).getD t default)
        (VExpr.instAll ((D.motiveType t).instL (D.projLvls C us i))
          (ps ++ (D.padMotives T C us ps is i j
            (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
              (bvars 1 is.length) j i) e).take t)) := by
      by_cases htj : t = j
      · subst htj
        rw [List.getD_eq_getElem?_getD, D.padMotives_getElem_eq T C us ps is i t _ e htlt,
          Option.getD_some, VIndType.projMotiveG_eq' D T C us his]
        exact projMotiveTermG_hasType_swapped henv hI H hTj hC hname h3 h7 hi hlvi hIH hps
          htakelen hpsA (motiveCtxG_wf' henv.ordered hI h7 h3 hTj C i hΓ hps hpsA)
      · obtain ⟨T'', hT''⟩ : ∃ T'', D.types[t]? = some T'' :=
          ⟨_, List.getElem?_eq_getElem htlt⟩
        rw [List.getD_eq_getElem?_getD,
          D.padMotives_getElem_ne T C us ps is i j _ e htlt htj, Option.getD_some,
          show D.types.getD t default = T'' from by rw [List.getD_eq_getElem?_getD, hT'']; rfl]
        exact padMotive_hasType (C := C) henv.ordered hI h7 h3 (by omega) hT'' hΓ hps
          htakelen hIHt
          (projMotiveG_app_hasType henv hI H hTj hC hname h3 h7 hi hlvi hIH hΓ hps his
            hpsA hisA he)
    have hcat := VEnv.HasArgs.concat hIHt
      (A := (D.motiveType t).instL (D.projLvls C us i)) (by simpa using hentry)
    rw [List.range_succ, List.map_append, List.map_append, htake]
    simpa [List.append_assoc] using hcat

/-- **The motive block, whole.**  `padMotives_hasArgs_take` at `t = D.nm`. -/
theorem padMotives_hasArgs (henv : VEnv.WF env) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors) (hname : T.name = S)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps is : List VExpr} {e : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (his : is.length = T.indices.length)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hisA : env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) is)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ is))) :
    env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ D.motives.map (VExpr.instL (D.projLvls C us i)))
      (ps ++ D.padMotives T C us ps is i j
        (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
          (bvars 1 is.length) j i) e) := by
  have h := padMotives_hasArgs_take henv hI H hTj hC hname h3 h7 hi hlvi hIH hΓ hps his
    hpsA hisA he D.nm (Nat.le_refl _)
  rwa [List.take_of_length_le (by rw [D.length_padMotives]; exact Nat.le_refl _),
    show (List.range D.nm).map D.motiveType = D.motives from rfl] at h

/-! ## The minor block

Everything the *padding* minors need is in `ProjGen.lean` already, except that
`padMinor_hasType_gen`'s `hspine` premise carries the same circularity as
`padMotiveCtx_wf`'s: it asks for the parameter-and-earlier-motive spine **under the minor's
own binders**.  The three variants below take `hpsA` instead, through `motiveCtxG_wf'`; they
are otherwise the existing proofs verbatim. -/

variable {T' : VIndType}

/-- `padMotive_app_beta` with `hspine` replaced by `hpsA` (`motiveCtxG_wf'`). -/
theorem padMotive_app_beta' (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat}
    (hT : D.types[t]? = some T') {i : Nat} {Γ ps bs : List VExpr} {X : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hbs : env.HasArgs U Γ
      (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps
        ++ [(VExpr.const T'.name us).mkApp
              (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)]) bs) :
    env.IsDefEq U Γ ((D.padMotive T' us ps X).mkApp bs)
      (.forallE X (X.liftN 1)) (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  obtain ⟨hOn, uc, hAty⟩ := motiveCtxG_wf' (T := T') henv hI h7 hus hT C i hΓ hps hpsA
  have hbody := padMotive_body_hasType (T' := T') (C := C) (ps := ps) henv h7 hX
  have hlen : bs.length = T'.indices.length + 1 := by
    have := hbs.length_eq; simp at this; omega
  have hrev : (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps
        ++ [(VExpr.const T'.name us).mkApp
              (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)]).reverse ++ Γ
      = (VExpr.const T'.name us).mkApp
          (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)
        :: ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse ++ Γ) := by simp
  have hOnAs : OnCtx ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps
        ++ [(VExpr.const T'.name us).mkApp
              (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)]).reverse ++ Γ)
      (env.IsType U) := by rw [hrev]; exact ⟨hOn, uc, hAty⟩
  have key := VEnv.IsDefEq.betaMkLams henv hOnAs hbs (by rw [hrev]; exact hbody)
  rw [VExpr.mkLams_append, VExpr.instAll_sort, padMotive_body_instAll hlen] at key
  exact key

/-- `padMinor_beta` with `hspine` replaced by `hpsA`. -/
theorem padMinor_beta' (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat}
    (hT : D.types[t]? = some T') (htlt : t < D.nm)
    {i q : Nat} {C' : VIndCtor} {lvls : List VLevel}
    {Δ ps mots acc : List VExpr} {X : VExpr}
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length)
    (hget : mots[t]? = some (D.padMotive T' us ps X))
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hΔ : OnCtx Δ (env.IsType U))
    (hpsA : env.HasArgs U Δ (D.params.map (VExpr.instL us))
      (ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)))
    (hX : env.HasType U Δ
      (X.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)
      (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hbs : env.HasArgs U Δ
      (VExpr.instAllTele (T'.indices.map (VExpr.instL us))
          (ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length))
        ++ [(VExpr.const T'.name us).mkApp
              ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)).map
                  (·.liftN T'.indices.length)
                ++ bvars 0 T'.indices.length)])
      (D.minorBodyArgs lvls q C' (ps ++ mots ++ acc))) :
    env.IsDefEq U Δ
      (VExpr.instAll ((D.minorBody q t C').instL lvls) (ps ++ mots ++ acc)
        ((D.minorBinders q C').map (VExpr.instL lvls)).length)
      (.forallE (X.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)
        ((X.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length).liftN 1))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  rw [D.minorBody_instAll_spine hget hps hmots hacc htlt, D.padMotive_liftN T' us hcl]
  exact padMotive_app_beta' (C := C) henv hI h7 hus hT hΔ (by simpa using hps) hpsA hX hbs

/-- **The padding minor is well-typed, from `hpsA` alone.**  `padMinor_hasType_gen`
(`ProjGen.lean`) with its `hspine`/`hms` premises replaced by the parameter spine, which is
what the block builder can actually supply. -/
theorem padMinor_hasType_gen' (henv : env.Ordered) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat}
    (hT : D.types[t]? = some T') (htlt : t < D.nm)
    {i q : Nat} {C' : VIndCtor} {lvls : List VLevel}
    (hC' : C' ∈ T'.ctors) (hCall : (t, C') ∈ D.ctorsAll)
    {Γ ps mots acc : List VExpr} {X : VExpr}
    (hself : D.selfLvls.map (VLevel.inst lvls) = us)
    (hget : mots[t]? = some (D.padMotive T' us ps X))
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hΓ : OnCtx Γ (env.IsType U))
    (hdecl : env.IsType U Γ
      (VExpr.instAll ((D.minorType q t C').instL lvls) (ps ++ mots ++ acc)))
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U Γ (D.padMinor lvls (ps ++ mots ++ acc) X q C')
      (VExpr.instAll ((D.minorType q t C').instL lvls) (ps ++ mots ++ acc)) := by
  have hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length := by
    rw [hps]; exact VExpr.ClosedTele.map_instL (H.indices t T' hT)
  have hW : Ctx.LiftN ((D.minorBinders q C').map (VExpr.instL lvls)).length 0 Γ
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ) :=
    Ctx.LiftN.zero (Γ := Γ)
      (VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse (by simp)
  obtain ⟨hOn, -⟩ := VEnv.IsType.mkPi_inv henv hΓ
    (by rwa [D.minorType_eq_mkPi q t C', VExpr.instL_mkPi, VExpr.instAll_mkPi,
      Nat.zero_add] at hdecl)
  have hpsA' := VEnv.HasArgs.weakN henv hW hpsA
  rw [VExpr.liftTele_eq_self (VExpr.ClosedTele.map_instL H.params) (Nat.zero_le _)] at hpsA'
  have hbeta := padMinor_beta' (C := C) (i := i) henv hI h7 hus hT htlt hcl hget hps hmots
    hacc hOn hpsA' (VEnv.HasType.weakN henv hW hX)
    (padMinor_hbs_gen henv hI hus h7 hT hC' hCall hps hmots hacc hself hcl hpsA)
  exact padMinor_hasType (D := D) henv hΓ hdecl hX ⟨_, hbeta⟩

/-! ### The minor's declared type

`minor_declType_isType` (`Theory/Inductive/StructureClosed.lean`) is stated at `q = t = 0` and
reads the motive block off `motives_eq`, i.e. off a singleton.  `VInductDecl'.minorType_isType`
(`Theory/Inductive/Lemmas.lean`) is already general in `q` and `t`; what was missing is the
take-prefix context fact and the instantiation. -/

theorem VInductDecl'.onCtxMinorsTake (hR : D.RecCtx env) (q : Nat) :
    OnCtx ((D.minors.take q).reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars) := by
  have h := VInductDecl'.onCtxMinors hR
  rw [← List.take_append_drop q D.minors, List.reverse_append,
    List.append_assoc (D.minors.drop q).reverse (D.minors.take q).reverse D.motives.reverse,
    List.append_assoc (D.minors.drop q).reverse
      ((D.minors.take q).reverse ++ D.motives.reverse) (D.atRecTele D.params).reverse] at h
  exact OnCtx.append_right h

/-- **The declared type of minor `q` is a type at the use site**, at an arbitrary constructor
of an arbitrary block member, over the parameter spine, the *whole* motive block and the
earlier minors. -/
theorem minor_declType_isType_gen (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U)
    {t q i : Nat} {C' : VIndCtor}
    (hTt : D.types[t]? = some T') (htlt : t < D.nm) (hC' : C' ∈ T'.ctors)
    (hCall : (t, C') ∈ D.ctorsAll) (hq : q ≤ D.nmin)
    {Γ ps mots acc : List VExpr}
    (hspine : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ D.motives.map (VExpr.instL (D.projLvls C us i))
        ++ (D.minors.take q).map (VExpr.instL (D.projLvls C us i))) (ps ++ mots ++ acc)) :
    env.IsType U Γ
      (VExpr.instAll ((D.minorType q t C').instL (D.projLvls C us i))
        (ps ++ mots ++ acc)) := by
  have hR := hI.toRecCtx
  obtain ⟨u, hmin⟩ := VInductDecl'.minorType_isType hR hTt htlt hC' hCall (q := q)
    (M := (D.minors.take q).reverse)
    (by rw [List.length_reverse, List.length_take, VInductDecl'.length_minors]; omega)
    (VInductDecl'.onCtxMinorsTake hR q)
  have hOn0 := VInductDecl'.onCtxMinorsTake (D := D) (env := env) hR q
  have h1 := VEnv.HasType.instL (ls := D.projLvls C us i) (U' := U)
    (VInductDecl'.projLvls_wf h7 i) hmin
  have hOn := OnCtx.instL (env := env) (ls := D.projLvls C us i) (U' := U)
    (VInductDecl'.projLvls_wf h7 i) hOn0
  simp only [List.map_append, List.map_reverse] at h1 hOn
  rw [List.append_assoc, ← List.reverse_append, ← List.reverse_append] at h1 hOn
  simp only [VExpr.instL] at h1
  have h2 := VEnv.IsDefEq.weakR henv (OnCtx.ctxClosed henv hOn) h1 Γ
  have h4 := VEnv.HasType.instAll henv hspine h2
  rw [VExpr.instAll_sort] at h4
  exact ⟨_, h4⟩

/-! ### The minor block as a spine

The one entry this cannot type itself is the **real** minor, at the projected block member:
its typing is `realMinor_hasType_atPadMotives`, whose `hiota` premise is the ι-law/swap step
at field `i`, which needs the *whole* recursor spine at the **earlier** fields — see the
correction at `docs/vacuity-ledger.md` row 111a.  So it is a premise here, `hreal`, and the
strong induction on the field index is what discharges it.

**Instrument 7, and row 107e's warning.**  `hreal` is a hypothesis, and no instrument in this
tree sees a hypothesis, so it is worth saying exactly what it is and is not.  It is *not* a
restatement of the conclusion: it is one entry of a `D.nmin`-entry block, at the slots whose
type index is `j`, and every other slot is discharged here outright.  At a narrow block
(`nmin = 1`, `ctorsAll = [(0, C)]`) it is exactly `projMinor_hasType`'s conclusion, which is
proved — so the premise is satisfiable, and `padMinors_hasArgs_narrow` below fires it. -/

theorem padMinors_hasArgs_take (henv : env.Ordered) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars)
    {i j : Nat} {Γ ps mots : List VExpr} {X : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np) (hmots : mots.length = D.nm)
    (hmotsNe : ∀ t T'', t < D.nm → t ≠ j → D.types[t]? = some T'' →
      mots[t]? = some (D.padMotive T'' us ps X))
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hmotA : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ D.motives.map (VExpr.instL (D.projLvls C us i))) (ps ++ mots))
    (hreal : ∀ q C', D.ctorsAll[q]? = some (j, C') →
      env.HasType U Γ
        (D.realMinor (D.projLvls C us i)
          (ps ++ mots ++ (D.padMinors (D.projLvls C us i) ps mots X i j).take q) i q C')
        (VExpr.instAll ((D.minorType q j C').instL (D.projLvls C us i))
          (ps ++ mots ++ (D.padMinors (D.projLvls C us i) ps mots X i j).take q))) :
    ∀ q, q ≤ D.nmin →
      env.HasArgs U Γ
        ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
          ++ D.motives.map (VExpr.instL (D.projLvls C us i))
          ++ (D.minors.take q).map (VExpr.instL (D.projLvls C us i)))
        (ps ++ mots ++ (D.padMinors (D.projLvls C us i) ps mots X i j).take q)
  | 0, _ => by simpa using hmotA
  | q+1, hq => by
    have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
      rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
    have hIHq := padMinors_hasArgs_take henv hI H h7 hus hΓ hps hmots hmotsNe hpsA hX hmotA
      hreal q (by omega)
    have hqlt : q < D.nmin := by omega
    obtain ⟨⟨t, C'⟩, hqC⟩ : ∃ tC, D.ctorsAll[q]? = some tC :=
      ⟨_, List.getElem?_eq_getElem hqlt⟩
    obtain ⟨T'', hT'', hC'⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hqC)
    have htlt : t < D.nm := (List.getElem?_eq_some_iff.1 hT'').1
    have hblen : (D.padMinors (D.projLvls C us i) ps mots X i j).length = D.nmin :=
      D.length_padMinors ..
    have hacc : ((D.padMinors (D.projLvls C us i) ps mots X i j).take q).length = q := by
      rw [List.length_take, hblen]; omega
    have htake : (D.padMinors (D.projLvls C us i) ps mots X i j).take (q+1)
        = (D.padMinors (D.projLvls C us i) ps mots X i j).take q
          ++ [(D.padMinors (D.projLvls C us i) ps mots X i j).getD q default] := by
      have hlt : q < (D.padMinors (D.projLvls C us i) ps mots X i j).length := by
        rw [hblen]; omega
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have hminA : (D.minors.getD q default) = D.minorType q t C' := by
      rw [List.getD_eq_getElem?_getD, D.minors_getElem? q, hqC]; rfl
    have hdecl := minor_declType_isType_gen (C := C) (i := i) henv hI h7 hT'' htlt hC'
      (List.mem_of_getElem? hqC) (by omega) hIHq
    have hentry : env.HasType U Γ
        ((D.padMinors (D.projLvls C us i) ps mots X i j).getD q default)
        (VExpr.instAll ((D.minorType q t C').instL (D.projLvls C us i))
          (ps ++ mots ++ (D.padMinors (D.projLvls C us i) ps mots X i j).take q)) := by
      by_cases htj : t = j
      · subst htj
        rw [List.getD_eq_getElem?_getD,
          D.padMinors_getElem_eq (D.projLvls C us i) ps mots X i t q hqC, Option.getD_some]
        exact hreal q C' hqC
      · rw [List.getD_eq_getElem?_getD,
          D.padMinors_getElem_ne (D.projLvls C us i) ps mots X i j q t C' hqC htj,
          Option.getD_some]
        exact padMinor_hasType_gen' (C := C) (i := i) henv hI H h7 hus hT'' htlt hC'
          (List.mem_of_getElem? hqC) hself (hmotsNe t T'' htlt htj hT'') hps hmots hacc hΓ
          hdecl hX hpsA
    have hcat := VEnv.HasArgs.concat hIHq
      (A := (D.minorType q t C').instL (D.projLvls C us i)) (by simpa using hentry)
    have hmintake : D.minors.take (q+1)
        = D.minors.take q ++ [D.minorType q t C'] := by
      have hlt : q < D.minors.length := by rw [VInductDecl'.length_minors]; omega
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp only [Option.toList_some, ← hminA, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [hmintake, List.map_append, htake]
    simpa [List.append_assoc] using hcat

/-- **The whole motive-and-minor block is the recursor's spine.**  `padMinors_hasArgs_take` at
`q = D.nmin`. -/
theorem padMinors_hasArgs (henv : env.Ordered) (hI : D.IotaCtx env) (H : D.ProjClosedG)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars)
    {i j : Nat} {Γ ps mots : List VExpr} {X : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np) (hmots : mots.length = D.nm)
    (hmotsNe : ∀ t T'', t < D.nm → t ≠ j → D.types[t]? = some T'' →
      mots[t]? = some (D.padMotive T'' us ps X))
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hmotA : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ D.motives.map (VExpr.instL (D.projLvls C us i))) (ps ++ mots))
    (hreal : ∀ q C', D.ctorsAll[q]? = some (j, C') →
      env.HasType U Γ
        (D.realMinor (D.projLvls C us i)
          (ps ++ mots ++ (D.padMinors (D.projLvls C us i) ps mots X i j).take q) i q C')
        (VExpr.instAll ((D.minorType q j C').instL (D.projLvls C us i))
          (ps ++ mots ++ (D.padMinors (D.projLvls C us i) ps mots X i j).take q))) :
    env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ D.motives.map (VExpr.instL (D.projLvls C us i))
        ++ D.minors.map (VExpr.instL (D.projLvls C us i)))
      (ps ++ mots ++ D.padMinors (D.projLvls C us i) ps mots X i j) := by
  have h := padMinors_hasArgs_take henv hI H h7 hus hΓ hps hmots hmotsNe hpsA hX hmotA hreal
    D.nmin (Nat.le_refl _)
  rw [List.take_of_length_le (Nat.le_of_eq (VInductDecl'.length_minors (D := D))),
    List.take_of_length_le (Nat.le_of_eq (D.length_padMinors ..))] at h
  exact h

/-- **`iota_law_gen`'s `hspine`, from the block spine and the field spine.**  The ι-rule's
binder context is `params ++ motives ++ minors ++ fields`, and the `liftTele (nm + nmin)` over
the two blocks is exactly what the block's own arguments cancel.  This is the producer
`iota_law_gen` had none of at `nm ≥ 2`; at a narrow block the same append is
`projMinor_hasType`'s `hspine`, built from `motives_eq`/`minors_eq`. -/
theorem iotaCtx_hasArgs (hus : us.length = D.uvars) {i : Nat} {C' : VIndCtor}
    {Γ ps mots mins fs : List VExpr}
    (hmots : mots.length = D.nm) (hmins : mins.length = D.nmin)
    (hblock : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ D.motives.map (VExpr.instL (D.projLvls C us i))
        ++ D.minors.map (VExpr.instL (D.projLvls C us i))) (ps ++ mots ++ mins))
    (hfsA : env.HasArgs U Γ
      (VExpr.instAllTele (C'.fields.map fun F => F.type.instL us) ps) fs) :
    env.HasArgs U Γ ((D.iotaCtx C').map (VExpr.instL (D.projLvls C us i)))
      (ps ++ mots ++ mins ++ fs) := by
  have hfeq : (C'.fields.map fun F => F.type.instL us)
      = (C'.fields.map (·.type)).map (VExpr.instL us) := by
    simp [List.map_map, Function.comp_def]
  rw [VInductDecl'.iotaCtx, List.map_append, List.map_append, List.map_append]
  refine VEnv.HasArgs.append hblock ?_
  rw [VExpr.instL_liftTele, VInductDecl'.atRecTele_instL (C := C) hus, ← hfeq,
    List.append_assoc,
    VExpr.instAllTele_liftTele_append (bs := mots ++ mins) (by simp [hmots, hmins])]
  exact hfsA

/-! ## Firing and collapse

**Instrument 7 on `padMinors_getElem_eq`.**  Its hypothesis is `D.ctorsAll[q]? = some (j, C)`,
which is `iota_law_of_gen`'s own `hqC`; at a narrow block it holds at `q = j = 0`, and the
lemma then returns the block's single entry.  `padMinors_narrow` (`ProjGen.lean`) says that
entry is `C.projMinor`, and the test below re-derives that **through** the new reading — so a
version of `padMinorsAux_getElem` that read the accumulator at the wrong slot would fail it.

**And, exactly as `docs/vacuity-ledger.md` row 111c says of `iota_law_of_gen`, this test cannot
see every slot error**: at `nmin = 1` the block has one entry and `take 0 = []`, so the
accumulator's *length* is not exercised.  What exercises it is `padMinorsAux_getElem`'s own
statement — the spine it names is `take (acc.length + m)`, a definite list, so a wrong offset
makes the equation **false** rather than merely unfired. -/

theorem padMinors_getElem_eq_narrow (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us lvls : List VLevel} {ps : List VExpr} {X mot : VExpr} {i : Nat}
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    (D.padMinors lvls ps [mot] X i 0)[0]? = some (C.projMinor us ps i) := by
  have hnm : D.nm = 1 := by simp [VInductDecl'.nm, htypes]
  have hqC : D.ctorsAll[0]? = some ((0 : Nat), C) := by
    simp [VInductDecl'.ctorsAll, htypes, hctors]
  rw [D.padMinors_getElem_eq lvls ps [mot] X i 0 0 hqC, List.take_zero,
    D.realMinor_norec (us := us) (q := 0) hrec (by simp [hnm]) rfl hself]

/-- **`padMinors_narrow` re-derived from the new reading**, independently of its own proof: a
one-entry block is determined by its length and its head.  This is the collapse test proper —
it is the statement that fails if `padMinorsAux_getElem` reads the wrong slot and
`padMinors_narrow` is right. -/
theorem padMinors_narrow_of_getElem (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us lvls : List VLevel} {ps : List VExpr} {X mot : VExpr} {i : Nat}
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    D.padMinors lvls ps [mot] X i 0 = [C.projMinor us ps i] := by
  have hnmin : D.nmin = 1 := by
    simp [VInductDecl'.nmin, VInductDecl'.ctorsAll, htypes, hctors]
  have hlen : (D.padMinors lvls ps [mot] X i 0).length = 1 := by
    rw [D.length_padMinors, hnmin]
  have h0 := padMinors_getElem_eq_narrow D T C (ps := ps) (X := X) (mot := mot) (i := i)
    htypes hctors hrec hself
  refine List.ext_getElem? fun m => ?_
  match m with
  | 0 => rw [h0]; rfl
  | m+1 =>
    rw [List.getElem?_eq_none (by rw [hlen]; omega), List.getElem?_eq_none (by simp)]

/-! ## The recursor application at the padded spine

`VInductDecl'.recApp_hasType''` (`Theory/Inductive/RecApp.lean`) is **already general in the
block**: it takes a full motive block `ms`, a full minor block `mins`, `hmot : ms[u]? = some
mot`, and its `hspine` is exactly the shape `padMinors_hasArgs` produces.  So the step
`projCore_hasType` (`Theory/Inductive/StructureClosed.lean`) performs at a singleton block is
available at the padded one with no new content — only the two blocks' `HasArgs`, which is
what this file supplies. -/

theorem projCoreG_hasType_of_block (hI : D.IotaCtx env)
    {j : Nat} (hTj : D.types[j]? = some T) (hname : T.name = S)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} {Γ ps is earlier mots mins : List VExpr} {e : VExpr}
    (hps : ps.length = D.np) (his : is.length = T.indices.length)
    (hmots : mots.length = D.nm) (hmins : mins.length = D.nmin) (hjlt : j < D.nm)
    (hmot : mots[j]? = some (T.projMotive C us ps is i earlier))
    (hisA : env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) is)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ is)))
    (hblock : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ D.motives.map (VExpr.instL (D.projLvls C us i))
        ++ D.minors.map (VExpr.instL (D.projLvls C us i))) (ps ++ mots ++ mins)) :
    env.HasType U Γ
      ((VExpr.const (Lean.mkRecName T.name) (D.projLvls C us i)).mkApp
        (ps ++ mots ++ mins ++ is ++ [e]))
      ((T.projMotive C us ps is i earlier).mkApp (is ++ [e])) := by
  have hidx : env.HasArgs U Γ
      (VExpr.instAllTele
        (VExpr.liftTele (D.nm + D.nmin)
          ((D.atRecTele T.indices).map (VExpr.instL (D.projLvls C us i))))
        (ps ++ (mots ++ mins)) 0) is := by
    rw [VInductDecl'.atRecTele_instL (C := C) h3,
      VExpr.instAllTele_liftTele_append (bs := mots ++ mins) (by simp [hmots, hmins])]
    exact hisA
  have he' : env.HasType U Γ e
      ((VExpr.const T.name (D.selfLvls.map (VLevel.inst (D.projLvls C us i)))).mkApp
        (ps ++ is)) := by
    rw [VInductDecl'.selfLvls_projLvls (C := C) h3 i, hname]; exact he
  have hblock' : env.HasArgs U Γ
      (((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
          ++ D.motives.map (VExpr.instL (D.projLvls C us i)))
        ++ D.minors.map (VExpr.instL (D.projLvls C us i))) (ps ++ (mots ++ mins)) := by
    rw [← List.append_assoc]; exact hblock
  have h := D.recApp_hasType'' hI hTj hjlt (VInductDecl'.projLvls_wf (C := C) h7 i)
    (VInductDecl'.projLvls_length (C := C) h3 i) hps hmots hmins hblock' hmot his hidx he'
  rwa [show ps ++ (mots ++ mins) ++ (is ++ [e]) = ps ++ mots ++ mins ++ is ++ [e] from by
    simp [List.append_assoc]] at h

/-- **What wall 2 now reduces to, compiled.**  Given the real minor's typing — `hreal`, i.e.
`realMinor_hasType_atPadMotives`'s `hiota` discharged — `projCoreG`'s recursor application is
typed at the projected motive applied to the index spine and the major premise.  Both padded
blocks are built here; nothing else is assumed.

The residual is therefore **exactly** `hreal` at field index `i`, and by
`docs/vacuity-ledger.md` row 111a that is one strong induction on the field index, whose
`IHmin` supplies this same lemma at `k < i`. -/
theorem projCoreG_hasType_of_hreal (henv : VEnv.WF env) (hI : D.IotaCtx env)
    (H : D.ProjClosedG) {j : Nat} (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hname : T.name = S) (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {i : Nat} (hi : i < C.fields.length)
    (hlvi : (C.fields.getD i default).lvl.inst us ≈ D.elimLvl.inst (D.projLvls C us i))
    (hIH : ∀ k, k < i → C.FieldUsed D 0 k → ProjHasTypeG env U S D T C us j k)
    {Γ ps is : List VExpr} {e : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np)
    (his : is.length = T.indices.length)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hisA : env.HasArgs U Γ (VExpr.instAllTele (T.indices.map (VExpr.instL us)) ps) is)
    (he : env.HasType U Γ e ((VExpr.const S us).mkApp (ps ++ is)))
    (hreal : ∀ q C', D.ctorsAll[q]? = some (j, C') →
      env.HasType U Γ
        (D.realMinor (D.projLvls C us i)
          (ps ++ D.padMotives T C us ps is i j
              (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
                (bvars 1 is.length) j i) e
            ++ (D.padMinors (D.projLvls C us i) ps
                (D.padMotives T C us ps is i j
                  (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
                    (bvars 1 is.length) j i) e)
                ((T.projMotive C us ps is i
                  (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
                    (bvars 1 is.length) j i)).mkApp (is ++ [e])) i j).take q) i q C')
        (VExpr.instAll ((D.minorType q j C').instL (D.projLvls C us i))
          (ps ++ D.padMotives T C us ps is i j
              (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
                (bvars 1 is.length) j i) e
            ++ (D.padMinors (D.projLvls C us i) ps
                (D.padMotives T C us ps is i j
                  (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
                    (bvars 1 is.length) j i) e)
                ((T.projMotive C us ps is i
                  (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
                    (bvars 1 is.length) j i)).mkApp (is ++ [e])) i j).take q))) :
    env.HasType U Γ
      (D.projCoreG T C us ps is i j
        (D.projArgsG T C us (ps.map (·.liftN (is.length+1))) (bvars 1 is.length) j i) e)
      ((projMotiveTermG D T C us ps i j).mkApp (is ++ [e])) := by
  have hjlt : j < D.nm := (List.getElem?_eq_some_iff.1 hTj).1
  have hX := projMotiveG_app_hasType henv hI H hTj hC hname h3 h7 hi hlvi hIH hΓ hps his
    hpsA hisA he
  have hmotA := padMotives_hasArgs henv hI H hTj hC hname h3 h7 hi hlvi hIH hΓ hps his
    hpsA hisA he
  have hmotsNe : ∀ t T'', t < D.nm → t ≠ j → D.types[t]? = some T'' →
      (D.padMotives T C us ps is i j
        (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
          (bvars 1 is.length) j i) e)[t]?
        = some (D.padMotive T'' us ps
            ((T.projMotive C us ps is i
              (D.projArgsG T C us (ps.map (·.liftN (is.length+1)))
                (bvars 1 is.length) j i)).mkApp (is ++ [e]))) := by
    intro t T'' htlt htj hT''
    rw [D.padMotives_getElem_ne T C us ps is i j _ e htlt htj,
      show D.types.getD t default = T'' from by rw [List.getD_eq_getElem?_getD, hT'']; rfl]
  have hblock := padMinors_hasArgs (C := C) henv.ordered hI H h7 h3 hΓ hps
    (D.length_padMotives ..) hmotsNe hpsA (by rw [VIndType.projMotiveG_eq' D T C us his] at hX ⊢; exact hX) hmotA hreal
  have h := projCoreG_hasType_of_block hI hTj hname h3 h7 hps his
    (D.length_padMotives ..) (D.length_padMinors ..) hjlt
    (D.padMotives_getElem_eq T C us ps is i j _ e hjlt) hisA he hblock
  rw [VIndType.projMotiveG_eq' D T C us his] at h
  simp only [VInductDecl'.projCoreG]
  rw [VIndType.projMotiveG_eq' D T C us his]
  exact h

end Lean4Lean
