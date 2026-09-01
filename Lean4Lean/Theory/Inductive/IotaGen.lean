import Lean4Lean.Theory.Inductive.StructureClosed

/-!
# The ι law at an arbitrary constructor of an arbitrary block

`iota_law` (`Theory/Inductive/StructureClosed.lean`) is the ι rule at the **first**
constructor of a **singleton** block: it takes `hnm : D.nm = 1`, `hnmin : D.nmin = 1`,
`hTd : D.types.getD 0 default = T` and `hrec : C.recFields = []`, and reads its motive and
minor premises off a two-element spine `[mot, minor]`.  All four hypotheses vanish at
`VEnv.IsStructureG` (`Verify/Typing/ProjGen.lean`), which is why
`docs/handoff-projections.md` §0**.7 item 1 lists the general form as the substantive
remainder of `hiota` — the residual premise of `realMinor_hasType_gen'`
(`Verify/Typing/ProjGenMinor.lean`) — and hence of `projTermG_hasType`, wall 2 of
`Verify/TypeChecker/EtaStructG.lean` and ledger row 105a.

This file is that general form.

## What was actually narrow, measured rather than assumed

**Three of the four typing ingredients were already general.**  `iotaLhs_hasType`,
`iotaLamBody_hasType` and `iotaLam_hasType` (`Theory/Inductive/Lemmas.lean`) all take
`D.types[j]? = some T` and `D.ctorsAll[q]? = some (j, C)` at arbitrary `j`, `q`; so does
`onCtxIota`.  Nothing in them had to be redone, and writing `_gen` versions of them would
have been the §0**.3 mistake a second time.

What *was* narrow is the three **computation** lemmas that read the spine — and the
`VEnv.IsStructure` packaging, which is replaced here by the four facts it was used for
(`hTt`, `hC`, `hqC` and the ι-rule's presence in `env.defeqs`).  So the general law is
stated over no structure predicate at all, which is also what lets it live in `Theory/`:
`IsStructureG` is defined under `Verify/`, and `Theory/` cannot import `Verify/`.

* `map_instAll_bvars_seg` — the one new piece of arithmetic: a `bvars` block at an
  **arbitrary** window of the substitution, where `map_instAll_bvars_top` covered only the
  top one.  With `nm = nmin = 1` the motive and minor blocks were single variables read by
  `instAll_bvar_get`; at general lengths they are segments.
* `iotaLhs_instAll_gen`, `iotaRhsBody_instAll_gen`, `iotaLamBody_instAll_gen`.

## What the general law does *not* assume, and the one thing it keeps

`C.recFields = []` is **dropped**: the induction-hypothesis values survive in the conclusion
as an explicit instantiated block, and `iota_law_gen_norec` is the corollary that collapses
it when there are none.  That matters because `realMinor_hasType_gen` is already
`noRec`-free (ledger row 107d), so a `noRec`-carrying ι law would have been the binding
constraint on the whole chain.

`hself : D.selfLvls.map (VLevel.inst ls) = us` replaces `us.length = D.uvars`: the level list
is arbitrary rather than `D.projLvls C us k`, which is one further generalisation the narrow
statement did not have and which `projLvls` satisfies (`selfLvls_inst`).

`iota_law_of_gen` re-derives the narrow `iota_law`, hypothesis for hypothesis, from the
general one — the collapse test.  **And it cannot see a slot error**, which is worth saying
rather than leaving for the next reader to assume: at `nm = nmin = 1` every segment is a
single element, so a version of `iotaLhs_instAll_gen` that read the minors where the motives
are would pass it.  What excludes that is different and stronger — the three computation
lemmas are *equations about a definite substitution*, so a wrong slot makes them **false**,
and they are proved.  The collapse test's job is the complementary one: that the general
statement still **meets** the narrow one, which a proved-but-differently-shaped
generalisation need not.

## What is left, and it is not this file

The general ι law is stated with `hspine` — the recursor's whole binder telescope well typed
at `ps ++ mots ++ mins ++ fs` — as a premise, exactly as the narrow one is.  At a **narrow**
block `projMinor_hasType` (`Verify/Typing/Lemmas.lean`) builds that spine itself, from
`motives_eq`/`minors_eq`, both of which say the block's motive and minor lists are
*singletons*.  At a general block the corresponding facts do not exist yet:

* **`padMinors_getElem_eq` is absent.**  `padMotives_getElem_eq`/`_ne`
  (`Verify/Typing/ProjGen.lean`) read the motive block at a slot; there is **no** counterpart
  for `padMinors`, so nothing yet says that minor `q` of `projCoreG`'s block *is*
  `D.realMinor lvls (ps ++ mots ++ (padMinors …).take q) i q C` when `D.ctorsAll[q]? = some
  (j, C)`.  `iota_law_gen`'s `hminor` premise is exactly that fact.
* **The two blocks have no `HasArgs`.**  `padMotive_hasType` and `padMinor_hasType'` type the
  individual padding entries and `realMinor_hasType_atPadMotives` types the real one, but no
  lemma assembles either block into `env.HasArgs U Γ (D.motives.map (VExpr.instL lvls)) mots`
  or the minors' dependent analogue.  That assembly is `docs/handoff-projections.md`'s block
  B, and it is what `hspine` needs at `nm ≥ 2`.

So the honest firing status of everything here is: it fires at a **narrow** block, through
`iota_law_of_gen` into the narrow `iota_law`'s own consumer; at a member of a **mutual** block
its `hspine` premise has no producer at all today.  The wall named as ledger row 105a's wall 2
is therefore one step shorter and not down.

## Audit

`#print axioms`, with `Lean4Lean/Experimental/ConeJoin.lean` co-imported (which is also the
duplicate-name check), and forward hole cones by the `scripts/hole-cone.lean` sweep:

| declaration | axioms | cone | holes |
|---|---|---|---|
| `map_instAll_bvars_seg` | `[propext, Quot.sound]` | 1674 | none |
| `iotaLhs_instAll_gen` | `[propext, Quot.sound]` | 1835 | none |
| `iotaRhsBody_instAll_gen` | `[propext, Quot.sound]` | 1662 | none |
| `iotaLamBody_instAll_gen` | `[propext, Quot.sound]` | 1795 | none |
| `iotaRule_mem` | `[propext, Quot.sound]` | 870 | none |
| `iota_law_gen` | `[propext, Classical.choice, Quot.sound]` | 3034 | none |
| `iota_law_gen_norec` | `[propext, Classical.choice, Quot.sound]` | 3035 | none |
| `iota_law_of_gen` | `[propext, Classical.choice, Quot.sound]` | 3145 | none |

The narrow `iota_law` is `[propext, Classical.choice, Quot.sound]` with cone 3135 and no
holes, so **the generalisation costs nothing on either axis** — same axiom set, no new hole,
and eleven constants of cone, all of them `padMinors`-free arithmetic.

**Two hypotheses of the narrow `iota_law` turn out to be dead**, found by the collapse test
rather than looked for: `iota_law_of_gen` needs neither `h7 : ∀ l ∈ us, l.WF U` nor
`hTd : D.types.getD 0 default = T` (the latter follows from `H.types`), and the compiler's
unused-binder linter is what said so.  They are kept in `iota_law_of_gen`'s statement, marked
`_h7`/`_hTd`, precisely so that the collapse is hypothesis for hypothesis.
-/


namespace Lean4Lean

namespace VExpr

/-- A `bvars` block sitting at an arbitrary window inside the substitution picks out the
segment `as[d …  d+n)`, each weakened past the `k` binders below the window.  Generalises
`map_instAll_bvars_top` (`d = 0`) and `map_instAll_bvars_bot`. -/
theorem map_instAll_bvars_seg {as : List VExpr} {lo n k d : Nat}
    (hk : k ≤ lo) (h : k + as.length = lo + n + d) :
    (bvars lo n).map (instAll · as k) = ((as.drop d).take n).map (liftN k · 0) := by
  refine List.ext_getElem? fun m => ?_
  rw [List.getElem?_map, List.getElem?_map, getElem?_bvars, List.getElem?_take]
  rcases Nat.lt_or_ge m n with hm | hm
  · rw [if_pos hm, if_pos hm]
    obtain ⟨a, ha⟩ : ∃ a, as[d + m]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [List.getElem?_drop, ha, Option.map_some, Option.map_some, Option.some.injEq]
    exact instAll_bvar_get ha (by omega)
  · rw [if_neg (by omega), if_neg (by omega)]
    rfl

end VExpr

open VExpr

/-- **The ι-rule's left-hand side at a concrete spine, at an arbitrary block member.**
`iotaLhs_instAll` (`StructureClosed.lean`) with `nm = nmin = 1` dropped: the motive and minor
blocks are whole lists `mots`/`mins` of the declared lengths, and the projected type sits at
an arbitrary index `t`. -/
theorem VInductDecl'.iotaLhs_instAll_gen (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us ls : List VLevel} {ps mots mins fs : List VExpr} {t : Nat}
    (hTd : D.types.getD t default = T)
    (hself : D.selfLvls.map (VLevel.inst ls) = us)
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hmins : mins.length = D.nmin)
    (hfs : fs.length = C.fields.length)
    (hlvl : ls.length = D.recUvars) :
    VExpr.instAll ((D.iotaLhs t C).instL ls) (ps ++ mots ++ mins ++ fs)
      = (VExpr.const (Lean.mkRecName T.name) ls).mkApp
          (ps ++ mots ++ mins
            ++ C.args.map (fun a =>
                 VExpr.instAll (VExpr.instAll (a.instL us) ps C.fields.length) fs)
            ++ [(VExpr.const C.name us).mkApp (ps ++ fs)]) := by
  have hsp : (ps ++ mots ++ mins ++ fs).length
      = D.np + D.nm + D.nmin + C.fields.length := by
    simp [hps, hmots, hmins, hfs]; omega
  -- the four variable blocks
  have e1 : (bvars (C.fields.length + (D.nm + D.nmin)) D.np).map
      (VExpr.instAll · (ps ++ mots ++ mins ++ fs) 0) = ps := by
    rw [VExpr.map_instAll_bvars_seg (d := 0) (Nat.zero_le _) (by rw [Nat.zero_add, hsp]; omega)]
    simp [List.take_left' hps]
  have e2 : (bvars (C.fields.length + D.nmin) D.nm).map
      (VExpr.instAll · (ps ++ mots ++ mins ++ fs) 0) = mots := by
    rw [VExpr.map_instAll_bvars_seg (d := D.np) (Nat.zero_le _) (by rw [Nat.zero_add, hsp]; omega)]
    simp [List.append_assoc, List.drop_left' hps, List.take_left' hmots]
  have e3 : (bvars C.fields.length D.nmin).map
      (VExpr.instAll · (ps ++ mots ++ mins ++ fs) 0) = mins := by
    rw [VExpr.map_instAll_bvars_seg (d := D.np + D.nm) (Nat.zero_le _)
      (by rw [Nat.zero_add, hsp]; omega)]
    rw [show ps ++ mots ++ mins ++ fs = (ps ++ mots) ++ (mins ++ fs) from by simp,
      List.drop_left' (by simp [hps, hmots]), List.take_left' hmins]
    simp
  have e5 : (bvars 0 C.fields.length).map
      (VExpr.instAll · (ps ++ mots ++ mins ++ fs) 0) = fs := by
    rw [VExpr.map_instAll_bvars_seg (d := D.np + D.nm + D.nmin) (Nat.zero_le _)
      (by rw [Nat.zero_add, hsp]; omega)]
    rw [show ps ++ mots ++ mins ++ fs = (ps ++ mots ++ mins) ++ fs from by simp,
      List.drop_left' (by simp [hps, hmots, hmins]; omega), List.take_of_length_le (by simp [hfs])]
    simp
  -- the constructor's result indices
  have e4 : ∀ a : VExpr,
      VExpr.instAll (VExpr.liftN (D.nm + D.nmin) (a.instL us) C.fields.length)
          (ps ++ mots ++ mins ++ fs)
        = VExpr.instAll (VExpr.instAll (a.instL us) ps C.fields.length) fs := by
    intro a
    rw [show ps ++ mots ++ mins ++ fs = (ps ++ (mots ++ mins)) ++ fs from by simp,
      VExpr.instAll_append (as := ps ++ (mots ++ mins)) (bs := fs), hfs, Nat.zero_add,
      VExpr.instAll_append (as := ps) (bs := mots ++ mins),
      show (mots ++ mins).length = D.nm + D.nmin from by simp [hmots, hmins],
      VExpr.liftN_instAll (as := ps) (X := a.instL us) (k := C.fields.length),
      show D.nm + D.nmin = (mots ++ mins).length from by simp [hmots, hmins],
      VExpr.instAll_liftN]
  simp only [VInductDecl'.iotaLhs, hTd, VInductDecl'.ctorApp',
    VInductDecl'.atRec, VExpr.instL_mkApp, VExpr.instL, List.map_append, List.map_map,
    Function.comp_def, VExpr.instL_instL, hself, VExpr.map_instL_bvars,
    VExpr.instAll_mkApp, VExpr.instAll_const, VExpr.instL_liftN,
    VLevel.params_inst hlvl, List.map_cons, List.map_nil]
  rw [e1, e2, e3, e5]
  simp only [e4]


open VExpr

/-- `iotaRhsBody_instAll` at an arbitrary minor index. -/
theorem VInductDecl'.iotaRhsBody_instAll_gen (D : VInductDecl') (C : VIndCtor)
    {ls : List VLevel} {spine : List VExpr} {q : Nat} (hcl : VExpr.ClosedN (D.iotaLam q C) 0)
    (hn : spine.length = (D.iotaCtx C).length) :
    VExpr.instAll (((D.iotaLam q C).mkApp (bvars 0 (D.iotaCtx C).length)).instL ls) spine
      = ((D.iotaLam q C).instL ls).mkApp spine := by
  rw [VExpr.instL_mkApp, VExpr.map_instL_bvars, VExpr.instAll_mkApp,
    (hcl.instL (ls := ls)).instAll_eq, VExpr.map_instAll_bvars' hn]

/-- **`iotaLam`'s body at a concrete spine, at an arbitrary minor of an arbitrary block.**
`iotaLamBody_instAll` (`StructureClosed.lean`) with `nm = nmin = 1` and `C.recFields = []`
both dropped: the minor is read out of the whole minor block `mins` at index `q`, and the
induction-hypothesis values survive as an explicit instantiated block. -/
theorem VInductDecl'.iotaLamBody_instAll_gen (D : VInductDecl') (C : VIndCtor)
    {ls : List VLevel} {ps mots mins fs : List VExpr} {minor : VExpr} {q : Nat}
    (hq : mins[q]? = some minor)
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hmins : mins.length = D.nmin)
    (hfs : fs.length = C.fields.length) :
    VExpr.instAll
        (((VExpr.bvar (C.fields.length + (D.nmin - 1 - q))).mkApp
            (bvars 0 C.fields.length ++ D.ihValues C)).instL ls)
        (ps ++ mots ++ mins ++ fs)
      = minor.mkApp (fs ++ (D.ihValues C).map
          (fun v => VExpr.instAll (v.instL ls) (ps ++ mots ++ mins ++ fs))) := by
  have hqlt : q < D.nmin := by
    rw [← hmins]
    exact (List.getElem?_eq_some_iff.1 hq).1
  have hsp : (ps ++ mots ++ mins ++ fs).length
      = D.np + D.nm + D.nmin + C.fields.length := by
    simp [hps, hmots, hmins, hfs]; omega
  have hget : (ps ++ mots ++ mins ++ fs)[D.np + D.nm + q]? = some minor := by
    rw [show ps ++ mots ++ mins ++ fs = (ps ++ mots) ++ (mins ++ fs) from by simp,
      List.getElem?_append_right (by simp [hps, hmots]),
      show D.np + D.nm + q - (ps ++ mots).length = q from by simp [hps, hmots],
      List.getElem?_append_left (by rw [hmins]; exact hqlt)]
    exact hq
  have e5 : (bvars 0 C.fields.length).map
      (VExpr.instAll · (ps ++ mots ++ mins ++ fs) 0) = fs := by
    rw [VExpr.map_instAll_bvars_seg (d := D.np + D.nm + D.nmin) (Nat.zero_le _)
      (by rw [Nat.zero_add, hsp]; omega)]
    rw [show ps ++ mots ++ mins ++ fs = (ps ++ mots ++ mins) ++ fs from by simp,
      List.drop_left' (by simp [hps, hmots, hmins]; omega),
      List.take_of_length_le (by simp [hfs])]
    simp
  simp only [VExpr.instL_mkApp, VExpr.instL, List.map_append, VExpr.map_instL_bvars,
    VExpr.instAll_mkApp]
  rw [VExpr.instAll_bvar_get hget (by rw [Nat.zero_add, hsp]; omega), e5]
  simp [List.map_map, Function.comp_def]


open VExpr VEnv

/-- **The ι law at an arbitrary constructor of an arbitrary block.** -/
theorem iota_law_gen {env : VEnv} {U : Nat}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us ls : List VLevel}
    (henv : env.Ordered) (hI : D.IotaCtx env) {t q : Nat}
    (hTt : D.types[t]? = some T) (hC : C ∈ T.ctors) (hqC : D.ctorsAll[q]? = some (t, C))
    (hdefeq : env.defeqs (D.iotaRule t q C))
    (hself : D.selfLvls.map (VLevel.inst ls) = us)
    {Γ ps mots mins fs : List VExpr} {minor : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hmins : mins.length = D.nmin)
    (hfs : fs.length = C.fields.length) (hminor : mins[q]? = some minor)
    (hlsWF : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = D.recUvars)
    (hspine : env.HasArgs U Γ ((D.iotaCtx C).map (VExpr.instL ls))
      (ps ++ mots ++ mins ++ fs)) :
    env.IsDefEq U Γ
      ((VExpr.const (Lean.mkRecName T.name) ls).mkApp
        (ps ++ mots ++ mins
          ++ C.args.map (fun a =>
               VExpr.instAll (VExpr.instAll (a.instL us) ps C.fields.length) fs)
          ++ [(VExpr.const C.name us).mkApp (ps ++ fs)]))
      (minor.mkApp (fs ++ (D.ihValues C).map
        (fun v => VExpr.instAll (v.instL ls) (ps ++ mots ++ mins ++ fs))))
      (VExpr.instAll ((D.iotaType t C).instL ls) (ps ++ mots ++ mins ++ fs)) := by
  have hTd : D.types.getD t default = T := by
    rw [List.getD_eq_getElem?_getD, hTt]; rfl
  have hj : t < D.nm := (List.getElem?_eq_some_iff.1 hTt).1
  have hCall : ((t : Nat), C) ∈ D.ctorsAll := List.mem_of_getElem? hqC
  have hclosed : VExpr.ClosedN (D.iotaLam q C) 0 :=
    (VInductDecl'.iotaLam_hasType hI hTt hj hC hqC).closedN henv trivial
  have hn : (ps ++ mots ++ mins ++ fs).length = (D.iotaCtx C).length := by
    simp [VInductDecl'.iotaCtx, VInductDecl'.atRecTele, VInductDecl'.motives,
      VInductDecl'.minors, hps, hmots, hmins, hfs, VInductDecl'.np]
  have hIotaOn : OnCtx ((D.iotaCtx C).reverse) (env.IsType D.recUvars) := by
    rw [D.iotaCtx_reverse' C]; exact VInductDecl'.onCtxIota hI.toRecCtx hTt hC
  have hOn' : OnCtx (((D.iotaCtx C).map (VExpr.instL ls)).reverse) (env.IsType U) := by
    rw [← List.map_reverse]; exact OnCtx.instL hlsWF hIotaOn
  have hcc : CtxClosed (((D.iotaCtx C).map (VExpr.instL ls)).reverse) :=
    OnCtx.ctxClosed henv hOn'
  have hOnCtx : OnCtx (((D.iotaCtx C).map (VExpr.instL ls)).reverse ++ Γ)
      (env.IsType U) := OnCtx.appendR henv hΓ hcc hOn'
  have hlhsTy : env.HasType U
      (((D.iotaCtx C).map (VExpr.instL ls)).reverse ++ Γ)
      ((D.iotaLhs t C).instL ls) ((D.iotaType t C).instL ls) := by
    have h0 := VInductDecl'.iotaLhs_hasType hI hTt hj hC hCall
    rw [← D.iotaCtx_reverse' C] at h0
    have h1 := VEnv.HasType.instL (ls := ls) (U' := U) hlsWF h0
    rw [List.map_reverse] at h1
    exact VEnv.IsDefEq.weakR henv hcc h1 Γ
  have hlamTy : env.HasType U
      (((D.iotaCtx C).map (VExpr.instL ls)).reverse ++ Γ)
      (((VExpr.bvar (C.fields.length + (D.nmin - 1 - q))).mkApp
        (bvars 0 C.fields.length ++ D.ihValues C)).instL ls)
      ((D.iotaType t C).instL ls) := by
    have h0 := VInductDecl'.iotaLamBody_hasType hI hTt hC hqC
    have h1 := VEnv.HasType.instL (ls := ls) (U' := U) hlsWF h0
    rw [List.map_reverse] at h1
    exact VEnv.IsDefEq.weakR henv hcc h1 Γ
  have hrhsTy : env.HasType U
      (((D.iotaCtx C).map (VExpr.instL ls)).reverse ++ Γ)
      (((D.iotaLam q C).mkApp (bvars 0 (D.iotaCtx C).length)).instL ls)
      ((D.iotaType t C).instL ls) := by
    have h0 := VInductDecl'.iotaLam_hasType hI hTt hj hC hqC
    have h1 := VEnv.HasType.instL (ls := ls) (U' := U) hlsWF h0
    simp only [List.map_nil, VExpr.instL_mkPi] at h1
    have h2 := VEnv.IsDefEq.weak0 (Γ := Γ) henv h1
    have h3 := VEnv.HasType.appBVars henv hOnCtx h2
    rw [(hclosed.instL (ls := ls)).liftN_eq (Nat.zero_le _)] at h3
    simpa [VExpr.instL_mkApp, VExpr.map_instL_bvars] using h3
  -- the chain
  have hextra := VEnv.IsDefEq.extra (Γ := Γ) hdefeq hlsWF hlslen
  simp only [VInductDecl'.iotaRule, VExpr.instL_mkLams, VExpr.instL_mkPi] at hextra
  have hstep := VEnv.IsDefEq.mkApp' hspine hextra
  have hL := VEnv.IsDefEq.betaMkLams henv hOnCtx hspine hlhsTy
  have hR := VEnv.IsDefEq.betaMkLams henv hOnCtx hspine hrhsTy
  have hLam := VEnv.IsDefEq.betaMkLams henv hOnCtx hspine hlamTy
  rw [D.iotaLhs_instAll_gen T C hTd hself hps hmots hmins hfs hlslen] at hL
  rw [D.iotaRhsBody_instAll_gen C hclosed hn] at hR
  rw [D.iotaLamBody_instAll_gen C hminor hps hmots hmins hfs] at hLam
  have hlamEq : (D.iotaLam q C).instL ls
      = mkLams ((D.iotaCtx C).map (VExpr.instL ls))
          (((VExpr.bvar (C.fields.length + (D.nmin - 1 - q))).mkApp
            (bvars 0 C.fields.length ++ D.ihValues C)).instL ls) := by
    simp only [VInductDecl'.iotaLam, VExpr.instL_mkLams]
  rw [← hlamEq] at hLam
  exact hL.symm.trans (hstep.trans (hR.trans hLam))


/-- `D.iotaRule t q C` is one of the block's ι-rules exactly when `(t, C)` is entry `q` of
`ctorsAll`. -/
theorem VInductDecl'.iotaRule_mem (D : VInductDecl') {t q : Nat} {C : VIndCtor}
    (hqC : D.ctorsAll[q]? = some (t, C)) : D.iotaRule t q C ∈ D.iotaRules := by
  refine List.mem_map.2 ⟨((t, C), q), ?_, rfl⟩
  exact List.mem_of_getElem? (by rw [List.getElem?_zipIdx, hqC]; simp)

/-- **The ι law with no recursive fields**: the ih block is empty, so the reduct is the minor
premise applied to the fields alone.  This is the shape the projection chain consumes. -/
theorem iota_law_gen_norec {env : VEnv} {U : Nat}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us ls : List VLevel}
    (henv : env.Ordered) (hI : D.IotaCtx env) {t q : Nat}
    (hTt : D.types[t]? = some T) (hC : C ∈ T.ctors) (hqC : D.ctorsAll[q]? = some (t, C))
    (hdefeq : env.defeqs (D.iotaRule t q C))
    (hself : D.selfLvls.map (VLevel.inst ls) = us) (hrec : C.recFields = [])
    {Γ ps mots mins fs : List VExpr} {minor : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hmins : mins.length = D.nmin)
    (hfs : fs.length = C.fields.length) (hminor : mins[q]? = some minor)
    (hlsWF : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = D.recUvars)
    (hspine : env.HasArgs U Γ ((D.iotaCtx C).map (VExpr.instL ls))
      (ps ++ mots ++ mins ++ fs)) :
    env.IsDefEq U Γ
      ((VExpr.const (Lean.mkRecName T.name) ls).mkApp
        (ps ++ mots ++ mins
          ++ C.args.map (fun a =>
               VExpr.instAll (VExpr.instAll (a.instL us) ps C.fields.length) fs)
          ++ [(VExpr.const C.name us).mkApp (ps ++ fs)]))
      (minor.mkApp fs)
      (VExpr.instAll ((D.iotaType t C).instL ls) (ps ++ mots ++ mins ++ fs)) := by
  have h := iota_law_gen henv hI hTt hC hqC hdefeq hself hΓ hps hmots hmins hfs hminor
    hlsWF hlslen hspine
  rwa [VInductDecl'.ihValues, hrec, List.map_nil, List.map_nil, List.append_nil] at h

/-- **Collapse test: the narrow `iota_law` is the general one.**  Hypothesis for hypothesis
`iota_law`'s statement (`Theory/Inductive/StructureClosed.lean`), derived from
`iota_law_gen_norec` at `mots = [mot]`, `mins = [minor]`, `q = 0`,
`ls = D.projLvls C us k`.

This is the only check that the motive and minor **segments** sit at the slots the narrow
single variables occupied: a generalisation off by one block would still typecheck and would
not meet this. -/
theorem iota_law_of_gen {env : VEnv} {U : Nat} {S : Lean.Name}
    {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {us : List VLevel}
    (henv : env.Ordered) (hI : D.IotaCtx env) (H : env.IsStructure S D T C)
    (h3 : us.length = D.uvars) (_h7 : ∀ l ∈ us, l.WF U)
    (hnm : D.nm = 1) (hnmin : D.nmin = 1) (hrec : C.recFields = [])
    {k : Nat} {Γ ps fs : List VExpr} {mot minor : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hps : ps.length = D.np) (hfs : fs.length = C.fields.length)
    (hlsWF : ∀ l ∈ D.projLvls C us k, l.WF U)
    (hlslen : (D.projLvls C us k).length = D.recUvars)
    (_hTd : D.types.getD 0 default = T)
    (hspine : env.HasArgs U Γ ((D.iotaCtx C).map (VExpr.instL (D.projLvls C us k)))
      (ps ++ [mot, minor] ++ fs)) :
    env.IsDefEq U Γ
      ((VExpr.const (Lean.mkRecName T.name) (D.projLvls C us k)).mkApp
        (ps ++ [mot, minor]
          ++ C.args.map (fun a =>
               VExpr.instAll (VExpr.instAll (a.instL us) ps C.fields.length) fs)
          ++ [(VExpr.const C.name us).mkApp (ps ++ fs)]))
      (minor.mkApp fs)
      (VExpr.instAll ((D.iotaType 0 C).instL (D.projLvls C us k))
        (ps ++ [mot, minor] ++ fs)) := by
  have hT0 : D.types[0]? = some T := by rw [H.types]; rfl
  have hC : C ∈ T.ctors := by rw [H.ctors]; exact List.mem_singleton_self _
  have hqC : D.ctorsAll[0]? = some ((0 : Nat), C) := by
    simp [VInductDecl'.ctorsAll, H.types, H.ctors]
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us k)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ h3
  have h := iota_law_gen_norec (mots := [mot]) (mins := [minor]) henv hI hT0 hC hqC
    H.iotaDefeq hself hrec hΓ hps (by simp [hnm]) (by simp [hnmin]) hfs rfl hlsWF hlslen
    (by simpa using hspine)
  simpa using h

end Lean4Lean
