import Lean4Lean.Theory.Inductive.NestedRules

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars liftTele instTele)

/-! ## §T1 `substC` transports the telescope-typing judgements -/

namespace VExpr
theorem map_substC_instTele {σ : CSubst} (hσ : σ.Closed) {a : VExpr} :
    ∀ {As : List VExpr} {k : Nat},
      (instTele a As k).map (VExpr.substC · σ)
        = instTele (a.substC σ) (As.map (VExpr.substC · σ)) k
  | [], _ => rfl
  | A :: As, k => by
    rw [VExpr.instTele_cons, List.map_cons, List.map_cons, VExpr.instTele_cons,
      VExpr.substC_inst hσ, map_substC_instTele hσ (As := As)]
end VExpr

namespace VEnv
variable {env₀ env₁ : VEnv} {σ : CSubst} {U : Nat}

theorem OnCtx.substC (hσ : σ.WF env₀ env₁ U) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env₀.IsType U) →
      OnCtx (Γ.map (VExpr.substC · σ)) (env₁.IsType U)
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ => ⟨OnCtx.substC hσ h1, h2.substC hσ⟩

theorem HasArgs.substC (hσ : σ.WF env₀ env₁ U) {Γ : List VExpr} :
    ∀ {As as : List VExpr}, env₀.HasArgs U Γ As as →
      env₁.HasArgs U (Γ.map (VExpr.substC · σ)) (As.map (VExpr.substC · σ))
        (as.map (VExpr.substC · σ))
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => by
    refine .cons (h1.substC hσ) ?_
    have := HasArgs.substC hσ h2
    rwa [VExpr.map_substC_instTele hσ.closed] at this

theorem HasArgsDF.substC (hσ : σ.WF env₀ env₁ U) {Γ : List VExpr} :
    ∀ {As as as' : List VExpr}, env₀.HasArgsDF U Γ As as as' →
      env₁.HasArgsDF U (Γ.map (VExpr.substC · σ)) (As.map (VExpr.substC · σ))
        (as.map (VExpr.substC · σ)) (as'.map (VExpr.substC · σ))
  | _, _, _, .nil => .nil
  | _, _, _, .cons h1 h2 => by
    refine .cons (h1.substC hσ) ?_
    have := HasArgsDF.substC hσ h2
    rwa [VExpr.map_substC_instTele hσ.closed] at this

/-- The telescope shape: `OnCtx (As.reverse ++ Γ)` transported. -/
theorem OnCtx.substC_tele (hσ : σ.WF env₀ env₁ U) {As Γ : List VExpr}
    (h : OnCtx (As.reverse ++ Γ) (env₀.IsType U)) :
    OnCtx ((As.map (VExpr.substC · σ)).reverse ++ Γ.map (VExpr.substC · σ))
      (env₁.IsType U) := by
  have := OnCtx.substC hσ h
  rwa [List.map_append, List.map_reverse] at this

end VEnv

/-! ## §T2 `TeleDefEq` structure -/

namespace VEnv
theorem TeleDefEq.append {env : VEnv} {U : Nat} :
    ∀ {Γ As As' Bs Bs' : List VExpr}, env.TeleDefEq U Γ As As' →
      env.TeleDefEq U (As.reverse ++ Γ) Bs Bs' →
      env.TeleDefEq U Γ (As ++ Bs) (As' ++ Bs') := by
  intro Γ As As' Bs Bs' h
  induction h with
  | nil => intro hB; simpa using hB
  | @rfl Γ A As As' _ ih =>
    intro hB
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hB
    exact .rfl (ih hB)
  | @cons Γ A A' u As As' hA _ ih =>
    intro hB
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hB
    exact .cons hA (ih hB)

theorem TeleDefEq.of_eq {env : VEnv} {U : Nat} {Γ As As' : List VExpr} (h : As = As') :
    env.TeleDefEq U Γ As As' := h ▸ .refl
end VEnv




/-! ## §T3 Pi-inversion: the substituted telescope's `OnCtx` is free

**Not a new lemma.**  `VEnv.IsType.mkPi_inv` (`Theory/Inductive/StructureClosed.lean:914`)
already peels a whole `mkPi` telescope out of an `IsType` on `env.Ordered` alone, and this
file already imports it through `NestedRules`.  It was re-derived here before that was
noticed — the second time in this cone that the missing step was one import line away, after
`betaMkLams`.  What *is* new is the observation below about what it buys.

**Obligation (B) needs no D-series transport for its telescope typing.**  The `OnCtx` of the
*substituted* recursor telescope in `e₂` — item 2 of §8.9's verdict note, "the D-series moved
across the substitution, bulk not depth" — is not bulk at all:

    hsrc j : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩         -- an `IsType E₂ _ []`
    ⇒ .substC hσ : e₂.IsType D.recUvars [] ((D.recType j).substC σ)
    ⇒ substC_mkPi : … = mkPi (telescope.map (substC · σ)) (body.substC σ)
    ⇒ mkPi_inv he₂ trivial : OnCtx ((telescope.map (substC · σ)).reverse) (e₂.IsType _)
                             ∧ e₂.IsType _ … (body.substC σ)

`hsrc`/`hσ` are hypotheses `recConstsR_wf_of_substC'` already takes, so the whole `OnCtx`
side of (B) is free.  `recTypeTele_substC_onCtx` below is that derivation, once.

For **(C)** the same route runs off `htype` — the rule's substituted `type` is a type in `e₃`
— which `iotaRulesRS_wf_of_substC_of_eq` already identifies as data the strict route never had
to produce.  It does *not* run off `hsrc`: `VDefEq.WF` is two `HasType`s at a `mkLams` and says
nothing about its `type` field.  So (C)'s telescope typing is not free, but it is not a
separate obligation either — it is `htype`, which was already on the list. -/

/-! ### §T3's derivation, once

The general form first: a constant whose declared type is a `mkPi` yields, after `substC` and
on `Ordered` alone, both the substituted telescope's `OnCtx` and the substituted body's
`IsType`.  No D-series transport is involved — `mkPi_inv` peels the source typing itself.

Worth recording alongside: `VEnv.recConstsR_wf_of_substC'` never asks for this, because
`VEnv.IsType.mkPi_congr'` runs `forallE_inv` on the source `IsType` internally.  So the
`OnCtx` half of item 2 of §8.9's verdict list is not merely *free* for (B) — it is already
*discharged inside the bridge*.  What the lemma below is for is a caller that must build the
**body** defeq and therefore needs the context by name. -/

theorem VConstant.WF.substC_mkPi_inv {E e : VEnv} {U : Nat} {σ : CSubst}
    {As : List VExpr} {B : VExpr} (he : e.Ordered) (hσ : σ.WF E e U)
    (hs : VConstant.WF E ⟨U, VExpr.mkPi As B⟩) :
    OnCtx ((As.map (VExpr.substC · σ)).reverse) (e.IsType U) ∧
      e.IsType U ((As.map (VExpr.substC · σ)).reverse) (B.substC σ) := by
  have h : e.IsType U [] ((VExpr.mkPi As B).substC σ) := hs.substC hσ
  rw [VExpr.substC_mkPi] at h
  simpa using VEnv.IsType.mkPi_inv he (Γ := []) trivial h

/-- **The telescope typing of the substituted recursor type, from `hsrc` and `hσ` alone.**
This is `recTypeTele_substC_onCtx`, the derivation §T3 describes. -/
theorem VEnv.recTypeTele_substC_onCtx {E₂ e₂ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {j : Nat} {T : VIndType} (he₂ : e₂.Ordered) (hσ : σ.WF E₂ e₂ D.recUvars)
    (hg : D.types.getD j default = T)
    (hs : VConstant.WF E₂ ⟨D.recUvars, D.recType j⟩) :
    OnCtx (((D.atRecTele D.params ++ D.motives ++ D.minors ++
        VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
        (VExpr.substC · σ)).reverse) (e₂.IsType D.recUvars) ∧
      e₂.IsType D.recUvars
        (((D.atRecTele D.params ++ D.motives ++ D.minors ++
          VExpr.liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).map
          (VExpr.substC · σ)).reverse)
        ((VExpr.forallE (D.tyApp' j (T.indices.length + D.nmin + D.nm)
            (VExpr.bvars 0 T.indices.length))
          ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
            (VExpr.bvars 1 T.indices.length ++ [.bvar 0]))).substC σ) :=
  VConstant.WF.substC_mkPi_inv he₂ hσ (by rw [← hg] at *; exact hs)


/-! ## §T4 A `bvars` spine cannot reach past the context

The correction this section exists for.  `VIndRestore.substC_motiveType_defeq`
(`Theory/Inductive/NestedRules.lean` §8.9) is stated with the entry's conclusion at the
**empty** ambient context, and its `hbv` types the parameter spine `bvars (ni + t) D.np` in a
context of length `ni`.  For `D.np = 0` that spine is `[]` and the hypothesis is `HasArgs.nil`;
for `D.np > 0` its first element is `.bvar (ni + t + D.np - 1)`, which no context of length
`ni` can type.  So the theorem — advertised as "the join, machine-checked, with **no bound on
`D.np`**" — is **vacuous exactly above `D.np = 0`**, the regime it claims to reach.

`substC_motiveType_defeq_of_head` is vacuous there for the same reason one step earlier: its
`hhead` relates `(D.tyApp' t (ni + t) (bvars 0 ni)).substC σ`, whose head spine is that same
out-of-scope block, in that same context.

The repair is not a new lemma but a **generalisation**: the entry has to be related in the
context it actually lives in — `(motives<t ++ params)`-reversed, substituted — which is
precisely what `VEnv.TeleDefEq` asks of the `t`-th entry of the motive block anyway.  §T5 is
that generalisation, and it discharges the offending hypothesis there: the parameter spine's
indices `ni + t … ni + t + np - 1` are exactly the parameters of that ambient context, so
`HasArgs.bvars` produces `hbv` outright (`hasArgs_params_bvars_motiveCtx'`).  Whether the
*remaining* hypotheses are simultaneously satisfiable at that `Γ` is not settled here. -/

namespace VEnv

/-- A typed term is closed at the context length, so a `bvar` spine reaching index
`Γ.length` or beyond cannot be typed. -/
theorem HasArgs.bvars_lt {env : VEnv} {U : Nat} {Γ As : List VExpr} {lo n : Nat}
    (henv : env.Ordered) (hΓ : CtxClosed Γ)
    (h : env.HasArgs U Γ As (VExpr.bvars lo (n + 1))) : lo + n < Γ.length := by
  rw [VExpr.bvars] at h
  cases h with
  | cons h1 _ => exact h1.closedN henv hΓ

/-- **The vacuity, stated.**  With `D.np > 0` the two hypotheses `hOn`/`hbv` of
`VIndRestore.substC_motiveType_defeq` are jointly contradictory. -/
theorem motive_params_spine_false {env : VEnv} {U t np ni : Nat} {P As : List VExpr}
    (henv : env.Ordered) (hnp : 0 < np)
    (hOn : OnCtx (VExpr.liftTele t As 0).reverse (env.IsType U))
    (hlen : As.length = ni)
    (hbv : env.HasArgs U (VExpr.liftTele t As 0).reverse P (VExpr.bvars (ni + t) np)) :
    False := by
  obtain ⟨n, rfl⟩ : ∃ n, np = n + 1 := ⟨np - 1, by omega⟩
  have := HasArgs.bvars_lt henv (hOn.ctxClosed henv) hbv
  rw [List.length_reverse, VExpr.length_liftTele, hlen] at this
  omega

end VEnv

/-! ## §T5 The vacuity machine-checked at the theorem itself, and the repair

§T4 states the vacuity abstractly.  These four theorems state it **at §8.9's own hypotheses**,
verbatim, so the claim is not an analogy: `substC_motiveType_defeq_hyps_false` takes `hOn`
and `hbv` exactly as `VIndRestore.substC_motiveType_defeq` binds them, and
`..._of_head_hyps_false` takes `hOn` and `hhead` exactly as
`substC_motiveType_defeq_of_head` binds them.

Then the repair, which is a **generalisation, not a weakening**: the primed versions take an
extra ambient context `Γ` under the index telescope and conclude at `Γ` instead of `[]`.
`substC_motiveType_defeq_of_head_of_gen` derives §8.9's `Γ = []` statement back out of the
primed one, so nothing is lost.

**What is and is not claimed about the repair.**  `hasArgs_params_bvars_motiveCtx'` *derives*
`hbv` — the hypothesis that is contradictory at `Γ = []` — at the `Γ` the entry actually lives
over, for every `D.np`.  That removes the known obstruction.  It is **not** a proof that the
primed theorems' full hypothesis set is jointly satisfiable: `hOn`, `hOnp` and `hbody` still
have to be produced at that `Γ`, and `hbody`/`hAs` are the data residual
`instAt_indep_of_tyArgs` bounds from below.  So: obstruction removed, satisfiability not
attested. -/

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e : VEnv}
variable {U t : Nat} {T : VIndType}

/-- **`substC_motiveType_defeq`'s own hypotheses, contradictory at `D.np > 0`.**
`hOn` and `hbv` are copied from that theorem's binders. -/
theorem substC_motiveType_defeq_hyps_false (henv : e.Ordered) (hnp : 0 < D.np)
    (hOn : OnCtx (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      (e.IsType U))
    (hbv : e.HasArgs U
      (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      (D.atRecTele D.params) (VExpr.bvars (T.indices.length + t) D.np)) :
    False :=
  VEnv.motive_params_spine_false henv hnp hOn (by simp) hbv

/-- **…and `substC_motiveType_defeq_of_head`'s, one step earlier.**  Here the out-of-scope
parameter block is inside `hhead`'s left endpoint, so the contradiction runs through
`IsDefEq.closedN` rather than `HasArgs`. -/
theorem substC_motiveType_defeq_of_head_hyps_false {w : VLevel}
    (henv : e.Ordered) (hnp : 0 < D.np)
    (hOn : OnCtx (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      (e.IsType U))
    (hhead : e.IsDefEq U
      (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      ((D.tyApp' t (T.indices.length + t) (VExpr.bvars 0 T.indices.length)).substC σ)
      (D.tyAppR' R t (T.indices.length + t) (VExpr.bvars 0 T.indices.length))
      (.sort w)) :
    False := by
  obtain ⟨n, hn⟩ : ∃ n, D.np = n + 1 := ⟨D.np - 1, by omega⟩
  have hcl := hhead.closedN henv (hOn.ctxClosed henv)
  rw [List.length_reverse, VExpr.length_liftTele, List.length_map,
    VInductDecl'.length_atRecTele] at hcl
  simp only [VInductDecl'.tyApp', VExpr.substC_mkApp, List.map_append,
    VExpr.map_substC_bvars, VExpr.closedN_mkApp] at hcl
  have h := hcl.2 (.bvar (T.indices.length + t + n))
    (List.mem_append_left _ (by rw [hn, VExpr.bvars]; exact List.mem_cons_self ..))
  exact absurd (show T.indices.length + t + n < T.indices.length from h) (by omega)

/-! ### The repair: the entry related in the context it lives in -/

/-- **§8.9's head-to-entry step, at a general ambient context.**  Identical to
`substC_motiveType_defeq_of_head` except that the index telescope sits over an arbitrary `Γ`
rather than over nothing; `mkPi_congrU` already takes a general `Γ`, so the proof is the same.
`Γ := []` gives the old statement back. -/
theorem substC_motiveType_defeq_of_head' {Γ : List VExpr} (hσ : σ.Closed) (hfr : R.SubstFree D σ)
    (helim : D.elimLvl.WF U) (hg : D.types.getD t default = T) {w : VLevel}
    (hOn : OnCtx ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      ++ Γ) (e.IsType U))
    (hhead : e.IsDefEq U
      ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse ++ Γ)
      ((D.tyApp' t (T.indices.length + t) (VExpr.bvars 0 T.indices.length)).substC σ)
      (D.tyAppR' R t (T.indices.length + t) (VExpr.bvars 0 T.indices.length))
      (.sort w)) :
    ∃ u, e.IsDefEq U Γ ((D.motiveType t).substC σ)
      ((D.motiveTypeR R t).substC σ) (.sort u) := by
  simp only [VInductDecl'.motiveType, VInductDecl'.motiveTypeR, hg,
    VExpr.substC_mkPi, VExpr.substC_forallE, VExpr.substC_sort,
    VExpr.map_substC_liftTele hσ, substC_tyAppR' hfr, VExpr.map_substC_bvars]
  have key := VEnv.IsDefEq.forallEDF hhead
    (.sortDF (l := D.elimLvl) (l' := D.elimLvl) helim helim rfl)
  exact VEnv.IsDefEq.mkPi_congrU (As' := VExpr.liftTele t
    ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0) .refl hOn ⟨_, key⟩

/-- **…and the join, at a general ambient context.**  `substC_tyApp'_defeq_tyAppR'_comp`
already quantifies over its ambient `Γ`, so lifting the join costs nothing beyond threading
it.  This is the statement §8.9 should have had: at `Γ := []` it is
`substC_motiveType_defeq`, and `substC_motiveType_defeq_hyps_false` says that instance is
empty above `D.np = 0`. -/
theorem substC_motiveType_defeq' (hσ : σ.Closed) (hfr : R.SubstFree D σ)
    (hat : R.SubstAt D K σ) (hcl : ∀ a ∈ R.tyArgs t, a.ClosedN D.np) (henv : e.Ordered)
    (helim : D.elimLvl.WF U) (hT : D.types[t]? = some T) (hK : T.name ∈ K)
    (hg : D.types.getD t default = T)
    {Γ As : List VExpr} {B B' : VExpr} {w : VLevel}
    (hOn : OnCtx ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      ++ Γ) (e.IsType U))
    (hOnp : OnCtx ((D.atRecTele D.params).reverse ++
      ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse ++ Γ))
      (e.IsType U))
    (hbv : e.HasArgs U
      ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse ++ Γ)
      (D.atRecTele D.params) (VExpr.bvars (T.indices.length + t) D.np))
    (hbody : e.HasType U ((D.atRecTele D.params).reverse ++
      ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse ++ Γ))
      (D.atRec (R.tyBody D t)) B)
    (hpi : VExpr.instAll B (VExpr.bvars (T.indices.length + t) D.np) = VExpr.mkPi As B')
    (hAs : e.HasArgs U
      ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse ++ Γ)
      As (VExpr.bvars 0 T.indices.length))
    (hsort : VExpr.instAll B' (VExpr.bvars 0 T.indices.length) = .sort w) :
    ∃ u, e.IsDefEq U Γ ((D.motiveType t).substC σ)
      ((D.motiveTypeR R t).substC σ) (.sort u) := by
  refine substC_motiveType_defeq_of_head' hσ hfr helim hg (w := w) hOn ?_
  have := substC_tyApp'_defeq_tyAppR'_comp (R := R) (D := D) (K := K) (σ := σ) (U := U)
    (j := t) (T := T) hat hcl henv hT hK (k := T.indices.length + t)
    (args := VExpr.bvars 0 T.indices.length) hOnp hbv hbody hpi
    (by rwa [VExpr.map_substC_bvars])
  rwa [VExpr.map_substC_bvars, hsort] at this

/-- **`Γ := []` gives §8.9's statement back**, so `substC_motiveType_defeq_of_head'` is a
generalisation and not a different theorem.  (Its `[]` instance is the one
`substC_motiveType_defeq_of_head_hyps_false` shows is empty above `D.np = 0`.) -/
theorem substC_motiveType_defeq_of_head_of_gen (hσ : σ.Closed) (hfr : R.SubstFree D σ)
    (helim : D.elimLvl.WF U) (hg : D.types.getD t default = T) {w : VLevel}
    (hOn : OnCtx (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      (e.IsType U))
    (hhead : e.IsDefEq U
      (VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
      ((D.tyApp' t (T.indices.length + t) (VExpr.bvars 0 T.indices.length)).substC σ)
      (D.tyAppR' R t (T.indices.length + t) (VExpr.bvars 0 T.indices.length))
      (.sort w)) :
    ∃ u, e.IsDefEq U [] ((D.motiveType t).substC σ)
      ((D.motiveTypeR R t).substC σ) (.sort u) :=
  substC_motiveType_defeq_of_head' (Γ := []) hσ hfr helim hg (by simpa using hOn)
    (by simpa using hhead)

end

/-! ### The generalisation is inhabited where the old one was not

`HasArgs.bvars` (`Theory/Inductive/Lemmas.lean:972`) types a telescope's own variable spine.
At the ambient context the recursor telescope actually gives motive entry `t` — index
telescope over `motives<t` over the parameters — it produces `hbv` outright.  So the
hypothesis that `substC_motiveType_defeq_hyps_false` refutes at `Γ = []` is *derivable* at
the real `Γ`, for every `D.np`. -/

/-- **`hbv`, discharged at the context the motive entry lives in.**  `Ξ` is the (substituted)
index telescope, `M` the motive block below entry `t`; the parameters sit under both, which is
exactly where `bvars (Ξ.length + M.length) D.np` points.  The only side condition is that the
parameter telescope is closed, which makes its `liftTele` the identity — and that is what
`VInductDecl'.WF.params` says. -/
theorem hasArgs_params_bvars_motiveCtx {e : VEnv} {U : Nat} {D : VInductDecl'}
    {Ξ M Γ₀ : List VExpr} {ni t : Nat}
    (hp : VExpr.ClosedTele (D.atRecTele D.params) 0)
    (hΞ : Ξ.length = ni) (hM : M.length = t) :
    e.HasArgs U (Ξ.reverse ++ M.reverse ++ (D.atRecTele D.params).reverse ++ Γ₀)
      (D.atRecTele D.params) (VExpr.bvars (ni + t) D.np) := by
  have h := VEnv.HasArgs.bvars (env := e) (U := U) (Δ := Ξ.reverse ++ M.reverse)
    (As := D.atRecTele D.params) (Γ₀ := Γ₀)
  rw [List.length_append, List.length_reverse, List.length_reverse, hΞ, hM,
    VInductDecl'.length_atRecTele, hp.liftTele_eq (Nat.le_refl 0)] at h
  exact h

/-- **…in exactly the form `substC_motiveType_defeq'` binds `hbv`.**  The ambient `Γ` is the
motive block below entry `t` over the parameter block; the associativity is the only thing
between this and the previous lemma. -/
theorem hasArgs_params_bvars_motiveCtx' {e : VEnv} {U : Nat} {D : VInductDecl'} {T : VIndType}
    {M Γ₀ : List VExpr} {t : Nat} {σ : CSubst}
    (hp : VExpr.ClosedTele (D.atRecTele D.params) 0) (hM : M.length = t) :
    e.HasArgs U
      ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
        ++ (M.reverse ++ ((D.atRecTele D.params).reverse ++ Γ₀)))
      (D.atRecTele D.params) (VExpr.bvars (T.indices.length + t) D.np) := by
  have h := hasArgs_params_bvars_motiveCtx (e := e) (U := U) (D := D)
    (Ξ := VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0)
    (M := M) (Γ₀ := Γ₀) (ni := T.indices.length) (t := t) hp (by simp) hM
  rwa [List.append_assoc, List.append_assoc] at h

/-- **The bound the other way.**  At `D.np = 0` the same `hbv` is *derivable* at every ambient
context, `bvars k 0` being `[]`.  Together with `substC_motiveType_defeq_hyps_false` this
brackets §8.9's reach exactly: `VIndRestore.substC_motiveType_defeq` is inhabited in this
hypothesis at `D.np = 0` and empty in it above, so "no bound on `D.np`" is precisely wrong —
the bound is `D.np = 0`, the same one the three `_of_np_zero` closures already carry. -/
theorem hasArgs_params_bvars_of_np_zero {e : VEnv} {U : Nat} {D : VInductDecl'}
    {Γ : List VExpr} {k : Nat} (hp : D.params = []) :
    e.HasArgs U Γ (D.atRecTele D.params) (VExpr.bvars k D.np) := by
  have h0 : D.np = 0 := by simp [VInductDecl'.np, hp]
  rw [hp, h0]
  exact .nil

end VIndRestore


end Lean4Lean
