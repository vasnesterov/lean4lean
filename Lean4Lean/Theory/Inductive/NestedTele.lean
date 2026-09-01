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


/-! ## §T6 The minor block

§T5 repaired the *motive* entry.  The **minor** entry was untouched, and it is the other
non-reflexive block of `TeleDefEq [] As As'` for obligation (B): with
`As := (atRecTele params ++ motives ++ minors ++ indices).map (substC · σ)`, the parameter and
index blocks are literally the same expression on both sides (`TeleDefEq.refl`), the motive
block is §T5's, and the minor block is this one.

`minorType` and `minorTypeR` differ in exactly **two** positions — machine-checked by the
`simp only` in `substC_minorType_defeq'`, whose two sides reduce to the same expression apart
from them:

1. the field telescope, `liftTele (nm+q) (atRecTele (fields.map (·.type)))` versus
   `liftTele (nm+q) (atRecTele (fieldTypesR D R))` — the ingredient (B)'s minor block shares
   with (C)'s `iotaCtx`;
2. the **last** argument of the conclusion, `ctorApp'` versus `ctorAppR`.

The induction-hypothesis block `D.ihTypes q C`, the motive `bvar` head and the index prefix
`C.args.map (shift …)` are *identical* on the two sides, so they cost `TeleDefEq.refl` and
`IsDefEq.appDF`'s reflexive left factor respectively.  That is why the minor entry needs only
**one** `appDF` and not a `HasArgsDF` over the whole spine: `mkApp_concat` splits the
conclusion at its last argument, which is the only one that moves.

**Three things this settles, and one it does not.**

* `hbv` — the hypothesis §T5 found contradictory at `Γ = []` — is *derivable* at the minor
  entry's real ambient context for **every** `D.np`, by the same `HasArgs.bvars` route
  (`hasArgs_params_bvars_minorCtx'`).  The generic form `hasArgs_params_bvars_ctx` now covers
  both blocks: the parameter spine `bvars k D.np` is typed by the parameter telescope in any
  context whose first `k` entries sit above `(atRecTele D.params).reverse`.
* Bounded the other way: `substC_minorType_hbv_false_of_nil` shows the `Γ = []` instance of
  that same `hbv` is **empty** above `D.np = 0`, exactly as for the motive.  So the minor entry
  had to be stated at a general `Γ` too; it is not an accident of §8.9's motive statement.
* `hfld` is inhabited: `teleDefEq_fld_of_np_zero` derives it from §7.5's strict equation, so
  the general-`Γ` minor bridge subsumes what `D.params = []` already closed.
* What is **not** settled: `hOn`, `hOnp`, `hcbody`, `hAs` and `hfun` at that `Γ`.  `hcbody`,
  `hAs` and `hfun` are the data residual — `hcbody`/`hAs` are §8.9's `hbody`/`hAs` for the
  *constructor* head, and `hfun` is `minorBody_hasType`'s partial application
  (`Theory/Inductive/Lemmas.lean:1550` builds exactly it, one `mkApp_concat` short of the
  conclusion) restated at the substituted environment. -/

namespace VEnv

/-- `HasArgs.bvars_lt` in the form the two blocks use it: a `bvar` spine starting at or beyond
the context length cannot be typed, whatever the telescope. -/
theorem HasArgs.bvars_ctx_false {env : VEnv} {U : Nat} {Γ As : List VExpr} {lo n : Nat}
    (henv : env.Ordered) (hΓ : CtxClosed Γ) (hle : Γ.length ≤ lo)
    (h : env.HasArgs U Γ As (VExpr.bvars lo (n + 1))) : False := by
  have := HasArgs.bvars_lt henv hΓ h
  omega

end VEnv

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e : VEnv}
variable {U t q : Nat} {T : VIndType} {C : VIndCtor}

/-! ### §T6.1 The parameter spine, at any block of the recursor telescope

`hasArgs_params_bvars_motiveCtx` (§T5) specialised the shape to the motive entry.  This is the
statement behind it: whatever sits between the spine and the parameters, `HasArgs.bvars` types
the parameter spine as long as the count matches the intervening length. -/

/-- **`hbv`, generically.**  `Δ` is everything between the spine's position and the parameter
block; `hp` (`VInductDecl'.WF.params`) makes the parameter telescope's `liftTele` the
identity. -/
theorem hasArgs_params_bvars_ctx {Δ Γ₀ : List VExpr} {k : Nat}
    (hp : VExpr.ClosedTele (D.atRecTele D.params) 0) (hΔ : Δ.length = k) :
    e.HasArgs U (Δ ++ ((D.atRecTele D.params).reverse ++ Γ₀))
      (D.atRecTele D.params) (VExpr.bvars k D.np) := by
  have h := VEnv.HasArgs.bvars (env := e) (U := U) (Δ := Δ)
    (As := D.atRecTele D.params) (Γ₀ := Γ₀)
  rw [hΔ, VInductDecl'.length_atRecTele, hp.liftTele_eq (Nat.le_refl 0)] at h
  rw [List.append_assoc] at h
  exact h

/-- …split the way a minor entry's context splits: `nr` induction hypotheses over `nf` fields
over the `nm + q` motives and earlier minors, over the parameters. -/
theorem hasArgs_params_bvars_minorCtx {V Φ M Γ₀ : List VExpr} {nr nf : Nat}
    (hp : VExpr.ClosedTele (D.atRecTele D.params) 0)
    (hV : V.length = nr) (hΦ : Φ.length = nf) (hM : M.length = D.nm + q) :
    e.HasArgs U (V ++ (Φ ++ (M ++ ((D.atRecTele D.params).reverse ++ Γ₀))))
      (D.atRecTele D.params) (VExpr.bvars (nr + nf + (D.nm + q)) D.np) := by
  have h := hasArgs_params_bvars_ctx (D := D) (e := e) (U := U)
    (Δ := V ++ Φ ++ M) (Γ₀ := Γ₀) (k := nr + nf + (D.nm + q)) hp
    (by simp [hV, hΦ, hM]; omega)
  rwa [List.append_assoc, List.append_assoc] at h

/-- **…in exactly the form `substC_minorType_defeq` needs it**, i.e. over the context the
minor entry's conclusion actually lives in: the substituted field telescope and the
induction-hypothesis block, over the entry's own ambient context. -/
theorem hasArgs_params_bvars_minorCtx' {M Γ₀ : List VExpr}
    (hp : VExpr.ClosedTele (D.atRecTele D.params) 0) (hM : M.length = D.nm + q) :
    e.HasArgs U
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (M ++ ((D.atRecTele D.params).reverse ++ Γ₀)))
      (D.atRecTele D.params)
      (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np) := by
  have h := hasArgs_params_bvars_minorCtx (D := D) (e := e) (U := U) (q := q)
    (V := ((D.ihTypes q C).map (VExpr.substC · σ)).reverse)
    (Φ := (VExpr.liftTele (D.nm + q)
      ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))).reverse)
    (M := M) (Γ₀ := Γ₀) (nr := (D.ihTypes q C).length) (nf := C.fields.length)
    hp (by simp) (by simp [VInductDecl'.length_atRecTele]) hM
  rw [List.reverse_append, List.append_assoc]
  exact h

/-! ### §T6.2 …and bounded the other way -/

/-- A parameter spine pointing `nm + q` binders below a context that is only `nr + nf` long
cannot be typed, for `D.np > 0`.  This is `motive_params_spine_false` for the minor block. -/
theorem minor_params_spine_false {Γ' : List VExpr} {nr nf : Nat}
    (henv : e.Ordered) (hnp : 0 < D.np) (hOn : OnCtx Γ' (e.IsType U))
    (hlen : Γ'.length ≤ nr + nf + (D.nm + q))
    (hbv : e.HasArgs U Γ' (D.atRecTele D.params)
      (VExpr.bvars (nr + nf + (D.nm + q)) D.np)) : False := by
  obtain ⟨n, hn⟩ : ∃ n, D.np = n + 1 := ⟨D.np - 1, by omega⟩
  rw [hn] at hbv
  exact VEnv.HasArgs.bvars_ctx_false henv (hOn.ctxClosed henv) hlen hbv

/-- **The `Γ = []` instance of the minor entry's `hbv` is empty above `D.np = 0`**, so the
minor entry had to be stated at a general ambient context for the same reason §8.9's motive
entry did.  (`nm + q = 0` is the only escape, i.e. a one-type block at its first minor.) -/
theorem substC_minorType_hbv_false_of_nil (henv : e.Ordered) (hnp : 0 < D.np)
    (hOn : OnCtx ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse) (e.IsType U))
    (hbv : e.HasArgs U ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse) (D.atRecTele D.params)
      (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)) :
    False :=
  minor_params_spine_false henv hnp hOn
    (by simp [VInductDecl'.length_atRecTele]) hbv

/-- **`hfld` is inhabited.**  At `D.params = []` §7.5's strict field-telescope equation gives
the `TeleDefEq` for free, so the general-`Γ` minor bridge below is a weakening of what
`substC_minors` already closed and cannot be vacuous. -/
theorem teleDefEq_fld_of_np_zero (hp : D.params = []) (hown : R.OwnId D K)
    (hat : R.SubstAt D K σ) (hcl0 : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN 0)
    (hfr : R.SubstFree D σ) (hcanon : C.Canonical D)
    (hpos : ∀ (i : Nat) (F : VIndField) (r : VIndRecArg), C.fields[i]? = some F →
      F.recArg = some r → r.idx < D.nm) {Γ : List VExpr} :
    e.TeleDefEq U Γ
      (VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)))
      (VExpr.liftTele (D.nm + q) ((D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ))) :=
  VEnv.TeleDefEq.of_eq (by
    rw [VIndRestore.substC_atRec_fieldTypes hp hown hat hcl0 hfr hcanon hpos])

/-! ### §T6.3 The minor entry's conclusion: one `appDF`, not a spine congruence -/

/-- **The minor conclusion's defeq.**  Only the last argument moves, so `mkApp_concat` reduces
the whole congruence to `IsDefEq.appDF` with a *reflexive* left factor — `hfun`, the motive
applied to the index prefix, which is literally the intermediate `minorBody_hasType`
(`Theory/Inductive/Lemmas.lean`) builds before its own final `.app`.  `A` is a parameter: it is
where `hfun`'s domain and `hmaj`'s type have to meet, and neither side fixes it. -/
theorem substC_minorBody_defeq {Γ : List VExpr} {A : VExpr} {m k nr nf : Nat}
    {ιs : List VExpr}
    (hfun : e.HasType U Γ ((VExpr.bvar m).mkApp (ιs.map (VExpr.substC · σ)))
      (.forallE A (.sort D.elimLvl)))
    (hmaj : e.IsDefEq U Γ ((D.ctorApp' C k (VExpr.bvars nr nf)).substC σ)
      ((D.ctorAppR R t C k (VExpr.bvars nr nf)).substC σ) A) :
    e.IsDefEq U Γ
      (((VExpr.bvar m).mkApp (ιs ++ [D.ctorApp' C k (VExpr.bvars nr nf)])).substC σ)
      (((VExpr.bvar m).mkApp (ιs ++ [D.ctorAppR R t C k (VExpr.bvars nr nf)])).substC σ)
      (.sort D.elimLvl) := by
  simp only [VExpr.substC_mkApp, VExpr.mkApp_concat, VExpr.substC]
  exact VEnv.IsDefEq.appDF hfun hmaj

/-- **The minor entry, reduced to its two moving parts.**  The `simp only` is the check that
`minorType` and `minorTypeR` agree everywhere else: after it, `mkPi_congrU` needs only the
field-telescope `TeleDefEq` (`TeleDefEq.append`ed with `refl` for the induction-hypothesis
block) and the conclusion's defeq. -/
theorem substC_minorType_defeq' (hσ : σ.Closed) {Γ : List VExpr} {w : VLevel}
    (hfld : e.TeleDefEq U Γ
      (VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)))
      (VExpr.liftTele (D.nm + q) ((D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ))))
    (hOn : OnCtx ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse ++ Γ) (e.IsType U))
    (hbody : e.IsDefEq U ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse ++ Γ)
      (((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a))
          ++ [D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
                (VExpr.bvars (D.ihTypes q C).length C.fields.length)])).substC σ)
      (((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a))
          ++ [D.ctorAppR R t C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
                (VExpr.bvars (D.ihTypes q C).length C.fields.length)])).substC σ)
      (.sort w)) :
    ∃ u, e.IsDefEq U Γ ((D.minorType q t C).substC σ)
      ((D.minorTypeR R q t C).substC σ) (.sort u) := by
  simp only [VInductDecl'.minorType, VInductDecl'.minorTypeR, VExpr.substC_mkPi,
    List.map_append, VExpr.map_substC_liftTele (σ := σ) hσ]
  exact VEnv.IsDefEq.mkPi_congrU (hfld.append VEnv.TeleDefEq.refl) hOn ⟨w, hbody⟩

/-- **The join, on the minor entry — the §T5 chain for the other non-reflexive block.**

`hbv` is discharged internally by `hasArgs_params_bvars_minorCtx'`, so there is **no bound on
`D.np`** here and none hidden in a vacuous hypothesis: the ambient context is the real one,
`M` being the motive block and the earlier minors (`M.length = D.nm + q`).  What is left is
`hOn`/`hOnp` (telescope typing at `e`) and `hcbody`/`hAs`/`hfun` (the data residual). -/
theorem substC_minorType_defeq (hσ : σ.Closed) (hat : R.SubstAt D K σ)
    (hfr : R.SubstFree D σ)
    (hcl : ∀ a ∈ R.tyArgs t, a.ClosedN D.np) (henv : e.Ordered)
    (hT : D.types[t]? = some T) (hK : T.name ∈ K) (hC : C ∈ T.ctors)
    (hpcl : VExpr.ClosedTele (D.atRecTele D.params) 0)
    {M Γ₀ As : List VExpr} {B B' : VExpr} (hM : M.length = D.nm + q)
    (hfld : e.TeleDefEq U (M ++ ((D.atRecTele D.params).reverse ++ Γ₀))
      (VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ)))
      (VExpr.liftTele (D.nm + q) ((D.atRecTele (C.fieldTypesR D R)).map (VExpr.substC · σ))))
    (hOn : OnCtx ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (M ++ ((D.atRecTele D.params).reverse ++ Γ₀))) (e.IsType U))
    (hOnp : OnCtx ((D.atRecTele D.params).reverse ++ ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (M ++ ((D.atRecTele D.params).reverse ++ Γ₀)))) (e.IsType U))
    (hcbody : e.HasType U ((D.atRecTele D.params).reverse ++ ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (M ++ ((D.atRecTele D.params).reverse ++ Γ₀))))
      (D.atRec (R.ctorBody D t C)) B)
    (hpi : VExpr.instAll B
      (VExpr.bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
        = VExpr.mkPi As B')
    (hAs : e.HasArgs U ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (M ++ ((D.atRecTele D.params).reverse ++ Γ₀)))
      As (VExpr.bvars (D.ihTypes q C).length C.fields.length))
    (hfun : e.HasType U ((VExpr.liftTele (D.nm + q)
        ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
        ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (M ++ ((D.atRecTele D.params).reverse ++ Γ₀)))
      ((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll B' (VExpr.bvars (D.ihTypes q C).length C.fields.length))
        (.sort D.elimLvl))) :
    ∃ u, e.IsDefEq U (M ++ ((D.atRecTele D.params).reverse ++ Γ₀))
      ((D.minorType q t C).substC σ) ((D.minorTypeR R q t C).substC σ) (.sort u) := by
  refine substC_minorType_defeq' hσ hfld hOn (w := D.elimLvl) ?_
  refine substC_minorBody_defeq hfun ?_
  have hmaj := substC_ctorApp'_defeq_ctorAppR_comp (R := R) (D := D) (K := K) (σ := σ)
    (U := U) (j := t) (T := T) (C := C) hat hcl henv hT hK hC
    (k := (D.ihTypes q C).length + C.fields.length + (D.nm + q))
    (args := VExpr.bvars (D.ihTypes q C).length C.fields.length)
    hOnp (hasArgs_params_bvars_minorCtx' hpcl hM) hcbody hpi
    (by rwa [VExpr.map_substC_bvars])
  rw [VExpr.map_substC_bvars] at hmaj
  rwa [substC_ctorAppR hfr hT hC, VExpr.map_substC_bvars]

end
end VIndRestore


/-! ## §T7 (C)'s telescope typing is not a fourth obligation

The standing account of (C) is that it "needs `htype` as data".  That is exact for the
**strict** route: `VEnv.iotaRulesRS_wf_of_substC_of_eq` (`Theory/Typing/ConstSubstNested.lean`)
takes `htype : ∀ df ∈ D.iotaRules, e₃.IsType df.uvars [] (df.type.substC σ)` as a hypothesis,
because a `VDefEq.WF` is two `HasType`s and says nothing about the `type` field.

It is **not** exact for the defeq-tolerant `VEnv.iotaRulesRS_wf_of_substC'`, and this section is
the reason.  That bridge's own `type` component is

    e₃.IsDefEq df.uvars [] (df.type.substC σ) df'.type (.sort v)

and a typed defeq at a sort *contains* `htype`: `IsDefEq.hasType.1` is
`HasType _ [] (df.type.substC σ) (.sort v)`, i.e. an `IsType`.  So (C)' does not ask for
`htype`, and more usefully:

**the `type` component discharges the telescope typing the `lhs`/`rhs` components need.**
`VEnv.IsDefEq.mkLams_congr` — the congruence (C) runs the `lhs`/`rhs` through, because those
are `mkLams` over `iotaCtx` — takes `OnCtx (As.reverse ++ Γ)`, and that is exactly what
`IsType.mkPi_inv` peels off the `type` component's left endpoint on `Ordered` alone
(`iotaRule_tele_onCtx_of_type_defeq`).  Ordering matters and there is no circularity: the
`type` component has to be built first, from a source `IsType` (which is `htype`, or the
per-entry `hOn`s below); once built, the other two components' `OnCtx` is free.

`OnCtx.take_of_reverse` is the companion fact for the entry defeqs *inside* the `type`
component: every entry of `TeleDefEq` is stated over a **prefix** of the telescope, and an
`OnCtx` of the whole reversed telescope restricts to every prefix.  So one telescope typing
serves all of `mkPi_congrU`'s per-entry `hOn`s as well.

**And the body defeq is shared with (B).**  `iotaType` and `iotaTypeR` differ in exactly the
same one position as `minorType`'s and `minorTypeR`'s conclusions — the last argument,
`ctorApp'` versus `ctorAppR` — so `substC_iotaType_defeq` below *is*
`substC_minorBody_defeq`, at `nr := 0`.  That is machine-checked: its proof term is the §T6
lemma applied, nothing else. -/

/-- An `OnCtx` of a reversed telescope restricts to every prefix of that telescope — which is
where `TeleDefEq`'s entry defeqs live. -/
theorem OnCtx.take_of_reverse {P : List VExpr → VExpr → Prop} :
    ∀ {As Γ : List VExpr} (k : Nat), OnCtx (As.reverse ++ Γ) P →
      OnCtx ((As.take k).reverse ++ Γ) P := by
  intro As Γ k h
  rw [show As = As.take k ++ As.drop k from (List.take_append_drop k As).symm,
    List.reverse_append, List.append_assoc] at h
  exact OnCtx.append_right h

namespace VEnv
variable {e : VEnv} {U : Nat}

/-- **`mkPi_inv` off a *defeq at a sort* rather than an `IsType`.**  A typed defeq already
carries both endpoints' typing, so no extra hypothesis is needed. -/
theorem IsType.mkPi_inv_of_defeq {Γ As : List VExpr} {B B' : VExpr} {v : VLevel}
    (he : e.Ordered) (hΓ : OnCtx Γ (e.IsType U))
    (h : e.IsDefEq U Γ (VExpr.mkPi As B) B' (.sort v)) :
    OnCtx (As.reverse ++ Γ) (e.IsType U) ∧ e.IsType U (As.reverse ++ Γ) B :=
  VEnv.IsType.mkPi_inv he hΓ ⟨v, h.hasType.1⟩

/-- …and through the substitution, at the empty ambient context — the shape (C)'s `type`
component has. -/
theorem mkPi_substC_onCtx_of_defeq {σ : CSubst} {As : List VExpr} {B B' : VExpr} {v : VLevel}
    (he : e.Ordered) (h : e.IsDefEq U [] ((VExpr.mkPi As B).substC σ) B' (.sort v)) :
    OnCtx ((As.map (VExpr.substC · σ)).reverse) (e.IsType U) ∧
      e.IsType U ((As.map (VExpr.substC · σ)).reverse) (B.substC σ) := by
  rw [VExpr.substC_mkPi] at h
  simpa using IsType.mkPi_inv_of_defeq he (Γ := []) trivial h

end VEnv

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e : VEnv}
variable {U t q j : Nat} {T : VIndType} {C : VIndCtor}

/-- **(C)'s `lhs`/`rhs` telescope typing, out of its own `type` component.**  The `++ []` is
kept because that is the shape `VEnv.IsDefEq.mkLams_congr` binds at `Γ := []`. -/
theorem iotaRule_tele_onCtx_of_type_defeq (he : e.Ordered) {t' : VExpr} {v : VLevel}
    (hty : e.IsDefEq U [] (((D.iotaRule j q C).type).substC σ) t' (.sort v)) :
    OnCtx (((D.iotaCtx C).map (VExpr.substC · σ)).reverse ++ ([] : List VExpr))
        (e.IsType U) ∧
      e.IsType U (((D.iotaCtx C).map (VExpr.substC · σ)).reverse)
        ((D.iotaType j C).substC σ) := by
  have h := VEnv.mkPi_substC_onCtx_of_defeq (As := D.iotaCtx C) (B := D.iotaType j C) he hty
  exact ⟨by simpa using h.1, h.2⟩

/-- **(C)'s `type`-component body defeq is (B)'s minor conclusion defeq**, at `nr := 0`. -/
theorem substC_iotaType_defeq {Γ : List VExpr} {A : VExpr}
    (hfun : e.HasType U Γ
      ((VExpr.bvar (C.fields.length + D.nmin + (D.nm - 1 - j))).mkApp
        ((C.args.map fun a =>
          (D.atRec a).liftN (D.nm + D.nmin) C.fields.length).map (VExpr.substC · σ)))
      (.forallE A (.sort D.elimLvl)))
    (hmaj : e.IsDefEq U Γ
      ((D.ctorApp' C (C.fields.length + (D.nm + D.nmin))
        (VExpr.bvars 0 C.fields.length)).substC σ)
      ((D.ctorAppR R j C (C.fields.length + (D.nm + D.nmin))
        (VExpr.bvars 0 C.fields.length)).substC σ) A) :
    e.IsDefEq U Γ ((D.iotaType j C).substC σ) ((D.iotaTypeR R j C).substC σ)
      (.sort D.elimLvl) :=
  substC_minorBody_defeq hfun hmaj

end
end VIndRestore


/-! ## §T8 `hfun` is not data — the call site builds it and the statement throws it away

§T6's `substC_minorBody_defeq` takes `hfun`, the motive applied to the *index prefix* of the
minor's conclusion, as a hypothesis.  It is not a new residual.

`VInductDecl'.motiveApp_hasType'` (`Theory/Inductive/Lemmas.lean:1493`) builds

    happ := VEnv.HasType.mkApp' hidx hm0     -- `(bvar K).mkApp ιs : ∀ (major), Sort elimLvl`

from `hmot` and `hidx` alone, and then **discards** it in `happ.app hz`: its statement mentions
only the saturated application.  `minorBody_hasType` (`:1550`) inherits that.  So `hfun` is
`hmot` + `hidx`, which are exactly the two hypotheses `minorBody_hasType` already takes.

`motiveApp_partial_hasType` below is that intermediate, stated once and with no `D` in it — a
`Lookup` at a `mkPi Ξ (forallE Dom (.sort l))` plus the telescope's spine gives the partial
application at `forallE (instAll (Dom.liftN (K+1) Ξ.length) ιs 0) (.sort l)`.  Being
`D`-free it instantiates at the **substituted** motive block as readily as at the source one,
because `(D.motiveType t).substC σ` is a `mkPi … (forallE … (.sort D.elimLvl))` on the nose
(`substC_mkPi`/`substC_forallE`/`substC_sort`); `substC_motiveApp_partial` is that instance.

**What is left after this, exactly.**  Composing into §T6 is one line,

    hfun := hmatch ▸ substC_motiveApp_partial hT hmot hidx

so the minor entry's residual is no longer `hfun` but:

* `hmot`/`hidx` — the D-series (`lookup_motive`, `HasArgs`) restated at `e` over the
  *substituted* telescope.  Not a β-gap, not new mathematics.
* `hcbody`/`hAs` — §8.9's `hbody`/`hAs` for the **constructor** head, i.e. §8.7's `hargs`.
* `hmatch` — the **type match**: `instAll B' (bvars nr nf)`, the restored constructor's result
  type, against `instAll (((D.tyApp' t …).substC σ).liftN (k+1) ni) ιs 0`, the substituted
  motive's domain.  This is the one genuinely new obligation the minor entry adds over the
  motive entry, and it is `Faithful.ctor_agree` content: "the restored constructor really
  constructs the substituted type".  `instAt_indep_of_tyArgs` bounds `hcbody`/`hAs` from below
  but says nothing about `hmatch`. -/

namespace VEnv

/-- **The partial motive application `motiveApp_hasType'` builds and discards.**  Stated with no
`VInductDecl'` in it, so it applies to the substituted motive block as well as the source one. -/
theorem motiveApp_partial_hasType {env : VEnv} {U K ni : Nat} {Γ Ξ ιs : List VExpr}
    {Dom : VExpr} {l : VLevel} (hlen : Ξ.length = ni)
    (hmot : Lookup Γ K ((VExpr.mkPi Ξ (VExpr.forallE Dom (.sort l))).liftN (K + 1)))
    (hidx : env.HasArgs U Γ (VExpr.liftTele (K + 1) Ξ 0) ιs) :
    env.HasType U Γ ((VExpr.bvar K).mkApp ιs)
      (.forallE (VExpr.instAll (Dom.liftN (K + 1) ni) ιs 0) (.sort l)) := by
  have hm0 : env.HasType U Γ (.bvar K)
      ((VExpr.mkPi Ξ (VExpr.forallE Dom (.sort l))).liftN (K + 1)) := .bvar hmot
  rw [VExpr.liftN_mkPi, hlen, Nat.zero_add] at hm0
  have happ := VEnv.HasType.mkApp' hidx hm0
  simpa only [VExpr.liftN, VExpr.instAll_forallE, VExpr.instAll_sort] using happ

end VEnv

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {σ : CSubst} {e : VEnv}
variable {U t q j : Nat} {T : VIndType} {C : VIndCtor}

/-- **…at the substituted motive block**, which is what §T6's `hfun` asks for.  `hmot` and
`hidx` are the substituted D-series; nothing else enters. -/
theorem substC_motiveApp_partial {k : Nat} {Γ ιs : List VExpr}
    (hT : D.types[t]? = some T)
    (hmot : Lookup Γ k (((D.motiveType t).substC σ).liftN (k + 1)))
    (hidx : e.HasArgs U Γ
      (VExpr.liftTele (k + 1)
        ((VExpr.liftTele t (D.atRecTele T.indices) 0).map (VExpr.substC · σ)) 0) ιs) :
    e.HasType U Γ ((VExpr.bvar k).mkApp ιs)
      (.forallE (VExpr.instAll
        (((D.tyApp' t (T.indices.length + t) (VExpr.bvars 0 T.indices.length)).substC σ).liftN
          (k + 1) T.indices.length) ιs 0) (.sort D.elimLvl)) := by
  have hmt : (D.motiveType t).substC σ
      = VExpr.mkPi ((VExpr.liftTele t (D.atRecTele T.indices) 0).map (VExpr.substC · σ))
          (VExpr.forallE ((D.tyApp' t (T.indices.length + t)
            (VExpr.bvars 0 T.indices.length)).substC σ) (.sort D.elimLvl)) := by
    simp only [VInductDecl'.motiveType, VInductDecl'.getD_types hT, VExpr.substC_mkPi,
      VExpr.substC_forallE, VExpr.substC_sort]
  rw [hmt] at hmot
  exact VEnv.motiveApp_partial_hasType
    (by simp [VInductDecl'.length_atRecTele]) hmot hidx

end
end VIndRestore


/-! ## §T9 The residual, worked down: `hOn`, `hOnp`, `hmot`, `hidx`, `hmatch`

§T6–§T8 left five things at `np > 0`.  Four of them are now discharged or reduced to a single
global datum; the fifth is not a new obligation at all.  **Every statement here is checked at
`Γ = []` for the §T5 collapse** — the results are recorded per item.

### 1. `hOn` at both levels is free for (B), exactly as §T7 showed it is for (C)

`recConstsR_wf_of_substC'` already takes `hsrc` and `hσ`, and §T3's
`VConstant.WF.substC_mkPi_inv` peels the *outer* telescope off them on `Ordered` alone.  The
missing step was the **second** peel: the motive and minor entries are `mkPi`s sitting inside
one *entry* of that telescope, not segments of it, so `OnCtx.take_of_reverse` does not reach
them.  `VEnv.OnCtx.mkPi_entry_inv` is that step — an `OnCtx` of a reversed telescope whose
`i`-th entry is a `mkPi Bs Cd` yields `OnCtx (Bs.reverse ++ (prefix ++ Γ))` **and** the
entry's body `IsType`, again on `Ordered` alone.  Composed
(`VEnv.recTypeEntry_substC_onCtx`), `hsrc` + `hσ` give every entry defeq's `hOn`.  So `hOn` is
**not an obligation for (B)**: the residual shrinks by one, and the shrink is the same fact
§T7 found for (C) with `htype` in place of `hsrc`.

`[]`-check: `mkPi_entry_inv`'s hypotheses are an `OnCtx` and a `getElem?`; both are satisfiable
at `Γ = []`, and `Γ = []` is in fact the *intended* instance here (a recursor type is checked
at the empty context).  No spine hypothesis, so no `bvars` trap.

### 2. `hOnp` is `hOn` plus one global datum

`hOnp` re-adds the parameter telescope on **top** of the entry's context (the β-step in
`substC_ctorApp'_defeq_ctorAppR_comp` types `mkLams (atRecTele params) body`), so it is not a
prefix of anything.  But the parameters are closed, and `OnCtx.appendR`
(`Theory/Inductive/StructureClosed.lean:713`) already says a closed well-formed telescope stays
well-formed over any well-formed context.  `VEnv.onCtx_params_append` is `appendR` **applied**
— nothing more, and it should not be counted as new content — reducing `hOnp` to `hOn` plus

    hpar : OnCtx ((D.atRecTele D.params).reverse) (e.IsType D.recUvars)

one datum for the whole construction rather than one per entry.  `hpar` is *not* claimed free
here: `VInductDecl'.WF.onCtxParamsAtRec` (`Theory/Inductive/Lemmas.lean:848`) is exactly this
statement at the **source** environment, and transporting it to `e` needs `substC` to be the
identity on `D.params`.  That should hold — `csubst`'s domain is inside the block's own names
(§7.2 `csubst_dom`) and `D.params` are typed *before* the block's types are added
(`VInductDecl'.WF.params`), hence block-free — but `VInductDecl'.WF` carries the typing, not a
`NoBlock D.params` clause, and `VIndRestore.noBlock_noCSubst`
(`Theory/Inductive/RestoreBridge.lean:160`) is stated for `csubstTy`, not `csubst`.  So `hpar`
is the **one** telescope-typing residual left, and it is a side condition about parameters, not
a β-gap.

### 3. `hmot` needs no `VInductDecl'` at all

`lookup_motive` (`Theory/Inductive/Lemmas.lean:1600`) is proved from
`List.map_range_reverse_split`, which is already `D`-free; only the statement mentions `D`.
`Lookup.range_map` below is that statement `D`-free, and `lookup_motive_substC` is its instance
at the **substituted** motive block — `D.motives.map (substC · σ)` is
`(List.range D.nm).map (fun t => (D.motiveType t).substC σ)` by `List.map_map`, so the
substituted `hmot` is pure de Bruijn arithmetic with no environment in it.  Answering the
question §T8's template poses: `hmot` is *not* a statement that needs the source block.

`[]`-check: `Lookup.range_map` has no environment hypothesis and holds for `Δ = Γ₀ = []`; it is
`Lookup`, which is total on a long enough context, so there is nothing to collapse.

### 4. `hidx` is the source D-series plus §T1's transport

`hidx`'s telescope is a `liftTele` of the substituted index telescope.  §T1's
`VEnv.HasArgs.substC` moves a `HasArgs` across the substitution, and
`VExpr.map_substC_liftTele` commutes the `substC` past the `liftTele`; `VEnv.HasArgs.substC_liftTele`
is those two composed.  So `hidx` at `e` is `hidx` at the source (which is
`VIndCtor.WF.args_ty` after the two weakenings, as `minorBody_hasType`'s call site already
does) transported — no new mathematics, and no `np` bound.

`[]`-check: the transport is hypothesis-preserving; its `[]` instance is exactly the source's
`[]` instance, so it introduces no new vacuity.

### 5. `hmatch` is not a new obligation — it is §8.9's *type*-head defeq

The type match does **not** have to be an equation.  `IsDefEq.defeqDF` converts a typed defeq
along a defeq of its type, so `substC_minorBody_defeq` can take `hmaj` at the restored
constructor's result type `A₀` and a conversion `A₀ ≡ A` to the substituted motive's domain
(`substC_minorBody_defeq_of_conv`).  And that conversion is
`VIndRestore.substC_tyApp'_defeq_tyAppR'_comp` (§8.9) — which has **no `np` bound**.

The strict reading is what carries the bound: as an equation, `hmatch` is
`substC_tyApp'_eq_tyAppR'`, which needs `hp : D.params = []` **and** `hcl0`, and `hcl0` is
outright refuted at the parameterised witness (`InductiveDeclExamples.ntree_not_tyArgs_closed0`,
`Theory/Inductive/NestedRules.lean:1105`) while the typed route needs only `ClosedN D.np`, which
that same witness satisfies (`ntree_tyArgs_closedN_np`, `:1116`).  (The analogous *strict*
equation for obligation (A) is refuted outright at a real parameterised block —
`ntreeNode_substC_ne_typeR`, `Theory/Typing/ConstSubstNested.lean:774`, which is about
`C.type`/`C.typeR`, not about `tyApp'`; it is the same phenomenon one obligation over, not this
equation's refutation.)  So `hmatch` is one more instance of "prefer typed
throughout": **refuted strict, free typed.**  What is left of it after the conversion is a
σ-free syntactic identification of the chosen `B'` with `D.tyAppR' R t M ιs` — a choice the
caller makes when it picks `B` in `hcbody`, involving no substitution and no β-step, i.e.
`Faithful.ctor_agree` / `Canonical` bookkeeping.  It is **not** derivable from
`instAt_indep_of_tyArgs`, which bounds `hcbody`/`hAs` from below and says nothing about the
result head.

`[]`-check, and it is the sharp one: `minorBody_hfun_false_of_nil` shows `substC_minorBody_defeq`'s
`hfun` — hence `substC_minorType_defeq'` and `substC_minorType_defeq` — is **empty at `Γ = []`**,
because a `bvar` head cannot be typed in the empty context.  So the minor entry's general-`Γ`
form is *necessary*, not merely convenient; the §T5 collapse would have recurred here had the
statement been written at `[]`.  This is the third place in this corner where `[]` is empty
above the trivial case, after `substC_motiveType_defeq` and the minor `hbv`. -/

namespace VEnv
variable {e : VEnv} {U : Nat}

/-- **The second peel.**  `OnCtx` of a reversed telescope, at an entry that is itself a `mkPi`:
the entry's own telescope and body come out, over the prefix below it.  `Ordered` only. -/
theorem OnCtx.mkPi_entry_inv (he : e.Ordered) {As Γ Bs : List VExpr} {Cd : VExpr} {i : Nat}
    (hOn : OnCtx (As.reverse ++ Γ) (e.IsType U)) (hi : As[i]? = some (VExpr.mkPi Bs Cd)) :
    OnCtx (Bs.reverse ++ ((As.take i).reverse ++ Γ)) (e.IsType U) ∧
      e.IsType U (Bs.reverse ++ ((As.take i).reverse ++ Γ)) Cd := by
  have hlt : i < As.length := (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨L, Rr, hAs, hL⟩ : ∃ L Rr, As = L ++ VExpr.mkPi Bs Cd :: Rr ∧ L.length = i := by
    refine ⟨As.take i, As.drop (i+1), ?_, by simp [Nat.min_eq_left (Nat.le_of_lt hlt)]⟩
    have h1 : As.take (i+1) ++ As.drop (i+1) = As := List.take_append_drop _ _
    have h2 : As.take (i+1) = As.take i ++ [VExpr.mkPi Bs Cd] := by
      rw [List.take_add_one, hi]; rfl
    rw [h2] at h1
    simpa using h1.symm
  subst hAs
  rw [show (L ++ VExpr.mkPi Bs Cd :: Rr).take i = L from by rw [← hL]; simp]
  rw [List.reverse_append, List.reverse_cons] at hOn
  simp only [List.append_assoc, List.singleton_append] at hOn
  refine VEnv.IsType.mkPi_inv he ?_ (OnCtx.head_of_append hOn)
  exact OnCtx.append_right (Δ := [VExpr.mkPi Bs Cd])
    (OnCtx.append_right (Δ := Rr.reverse) hOn)

/-- **(B)'s entry `hOn`, from `hsrc` and `hσ` alone.**  §T3's outer peel composed with the
second peel; no hypothesis beyond the ones `recConstsR_wf_of_substC'` already takes. -/
theorem recTypeEntry_substC_onCtx {E₂ e₂ : VEnv} {D : VInductDecl'} {σ : CSubst}
    {As Bs : List VExpr} {B Cd : VExpr} {i : Nat}
    (he₂ : e₂.Ordered) (hσ : σ.WF E₂ e₂ D.recUvars)
    (hs : VConstant.WF E₂ ⟨D.recUvars, VExpr.mkPi As B⟩)
    (hi : (As.map (VExpr.substC · σ))[i]? = some (VExpr.mkPi Bs Cd)) :
    OnCtx (Bs.reverse ++ (((As.map (VExpr.substC · σ)).take i).reverse ++ ([] : List VExpr)))
        (e₂.IsType D.recUvars) ∧
      e₂.IsType D.recUvars
        (Bs.reverse ++ (((As.map (VExpr.substC · σ)).take i).reverse ++ ([] : List VExpr))) Cd :=
  OnCtx.mkPi_entry_inv he₂ (by simpa using (VConstant.WF.substC_mkPi_inv he₂ hσ hs).1) hi

/-- **`hOnp` from `hOn` plus `hpar`.**  This is `OnCtx.appendR` *applied* — no new content;
it is here only to name the reduction. -/
theorem onCtx_params_append {D : VInductDecl'} {Γ : List VExpr}
    (henv : e.Ordered) (hpcl : VExpr.ClosedTele (D.atRecTele D.params) 0)
    (hpar : OnCtx ((D.atRecTele D.params).reverse) (e.IsType U))
    (hOn : OnCtx Γ (e.IsType U)) :
    OnCtx ((D.atRecTele D.params).reverse ++ Γ) (e.IsType U) :=
  _root_.Lean4Lean.OnCtx.appendR henv hOn (by simpa using hpcl.ctxClosed (Γ := []) trivial) hpar

end VEnv

/-- **`hmot`, with no `VInductDecl'` in it.**  `lookup_motive`'s content, at an arbitrary
mapped range. -/
theorem Lookup.range_map {f : Nat → VExpr} {n j : Nat} (hj : j < n) (Δ Γ₀ : List VExpr) :
    Lookup (Δ ++ ((List.range n).map f).reverse ++ Γ₀) (Δ.length + (n - 1 - j))
      ((f j).liftN (Δ.length + (n - 1 - j) + 1)) := by
  obtain ⟨Ξ, rest, he, hlen⟩ := List.map_range_reverse_split f hj
  have hsplit : Δ ++ ((List.range n).map f).reverse ++ Γ₀
      = (Δ ++ Ξ) ++ f j :: (rest ++ Γ₀) := by rw [he]; simp
  have hΞ : (Δ ++ Ξ).length = Δ.length + (n - 1 - j) := by rw [List.length_append, hlen]
  rw [hsplit, ← hΞ]
  exact Lookup.append _

namespace VInductDecl'

/-- **…and its instance at the substituted motive block**, which is the `hmot` §T8 needs. -/
theorem lookup_motive_substC {D : VInductDecl'} {σ : CSubst} {j : Nat} (hj : j < D.nm)
    (Δ Γ₀ : List VExpr) :
    Lookup (Δ ++ (D.motives.map (VExpr.substC · σ)).reverse ++ Γ₀)
      (Δ.length + (D.nm - 1 - j))
      (((D.motiveType j).substC σ).liftN (Δ.length + (D.nm - 1 - j) + 1)) := by
  have hm : D.motives.map (VExpr.substC · σ)
      = (List.range D.nm).map (fun t => (D.motiveType t).substC σ) := by
    rw [VInductDecl'.motives, List.map_map]; rfl
  rw [hm]
  exact Lookup.range_map hj Δ Γ₀

end VInductDecl'

namespace VEnv

/-- **`hidx` transported.**  §T1's `HasArgs.substC` with the `substC`/`liftTele` commutation. -/
theorem HasArgs.substC_liftTele {env₀ env₁ : VEnv} {σ : CSubst} {U : Nat}
    (hσ : σ.WF env₀ env₁ U) {Γ As as : List VExpr} {n k : Nat}
    (h : env₀.HasArgs U Γ (VExpr.liftTele n As k) as) :
    env₁.HasArgs U (Γ.map (VExpr.substC · σ))
      (VExpr.liftTele n (As.map (VExpr.substC · σ)) k) (as.map (VExpr.substC · σ)) := by
  have := HasArgs.substC hσ h
  rwa [VExpr.map_substC_liftTele hσ.closed] at this

end VEnv

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {σ : CSubst} {e : VEnv}
variable {U t : Nat} {C : VIndCtor}

/-- **`hmatch` as a conversion, not an equation.**  `hmaj` arrives at the restored
constructor's result type `A₀`; `hconv` — which is
`VIndRestore.substC_tyApp'_defeq_tyAppR'_comp`, no `np` bound — moves it to the substituted
motive's domain `A`.  The strict-equation reading of the same step is
`substC_tyApp'_eq_tyAppR'`, whose `hcl0` the parameterised witness refutes
(`ntree_not_tyArgs_closed0`) while the typed route's `ClosedN D.np` it satisfies. -/
theorem substC_minorBody_defeq_of_conv {Γ : List VExpr} {A A₀ : VExpr} {v : VLevel}
    {m k nr nf : Nat} {ιs : List VExpr}
    (hfun : e.HasType U Γ ((VExpr.bvar m).mkApp (ιs.map (VExpr.substC · σ)))
      (.forallE A (.sort D.elimLvl)))
    (hconv : e.IsDefEq U Γ A₀ A (.sort v))
    (hmaj : e.IsDefEq U Γ ((D.ctorApp' C k (VExpr.bvars nr nf)).substC σ)
      ((D.ctorAppR R t C k (VExpr.bvars nr nf)).substC σ) A₀) :
    e.IsDefEq U Γ
      (((VExpr.bvar m).mkApp (ιs ++ [D.ctorApp' C k (VExpr.bvars nr nf)])).substC σ)
      (((VExpr.bvar m).mkApp (ιs ++ [D.ctorAppR R t C k (VExpr.bvars nr nf)])).substC σ)
      (.sort D.elimLvl) :=
  substC_minorBody_defeq hfun (hconv.defeqDF hmaj)

/-- **The `[]`-check on §T6, and it is empty.**  A `bvar` head has no type in the empty
context, so `substC_minorBody_defeq`'s `hfun` — and with it every §T6 statement — is vacuous at
`Γ = []`.  The general-`Γ` form is therefore forced, exactly as for the motive entry. -/
theorem minorBody_hfun_false_of_nil {A : VExpr} {m : Nat} {ιs : List VExpr}
    (henv : e.Ordered) (hfun : e.HasType U [] ((VExpr.bvar m).mkApp ιs) A) : False := by
  have hcl := hfun.closedN henv trivial
  rw [VExpr.closedN_mkApp] at hcl
  exact absurd (show m < 0 from hcl.1) (Nat.not_lt_zero m)

end
end VIndRestore


/-! ## §T10 `hpar` is free, and the σ-free identification is derivable

Two of the three items §T9 left are closed here, and neither needed a new side condition.

### `hpar`: route A, and it is the whole job

§T9 offered three moves.  **Route A wins outright**, and not via the `csubstTy` lemma: the
machinery is `VEnv.Ordered.noCSubst` (`Theory/Typing/ConstSubst.lean:393`) together with
`VEnv.IsDefEq.noCSubst'` (`:351`) — "nothing derivable in `env` mentions a constant `env` does
not declare" — plus `VIndRestore.csubst_freshIn` (`Theory/Inductive/NestedRules.lean:1187`),
which already proves `(R.csubst D K).FreshIn env` from the three staging successes with **no new
side condition**.

So the general fact is `VEnv.OnCtx.noCSubst`: a well-formed context in a well-formed environment
mentions nothing in a fresh `σ`'s domain, hence `VEnv.OnCtx.substC_eq` — `substC` is the
**identity** on it.  Applied to `VInductDecl'.WF.onCtxParamsAtRec`
(`Theory/Inductive/Lemmas.lean:848`) and pushed across by §T1's `OnCtx.substC`, that is
`VInductDecl'.onCtxParamsAtRec_substC`: **`hpar` at `e`, from `D.WF env` and `σ.FreshIn env`
alone.**  Route B (deriving `NoBlock D.params` from the typing) is unnecessary — `noCSubst'`
already *is* that argument, at the right level of generality — and Route C (a named side
condition with two bounds) is not needed.  This also means `RestoreBridge.lean` needed no edit:
the `csubst`-analogue of `noBlock_noCSubst` is not the lemma to want, because
`Ordered.noCSubst` subsumes it for *any* fresh `σ`, `csubst` included.

`[]`-check: `OnCtx.noCSubst` and `OnCtx.substC_eq` at `Γ = []` are `nofun`/`rfl` — true and
uninformative, not contradictory, so nothing collapses.  `onCtxParamsAtRec_substC` is not a
`Γ`-indexed statement at all; its hypotheses (`D.WF env`, `csubst_freshIn`) are exactly what the
nested-ordered audit already carries.

### The σ-free identification: derivable, so no instance had to be built

§T9 asked for a positive `np > 0` instance of `B' = tyAppR'`.  There is a better answer: **it is
a theorem**, from `Faithful.ctor_agree` plus `VIndCtor.WF.params_len`, with no `np` bound and no
environment at all.

`R.instAt D npJ j ci.type` is `mkPi D.params (instAll (splitPis npJ (ci.type.instL …)).2 …)` and
`C.typeR D R j` is `mkPi (C.params ++ C.fieldTypesR D R) (D.tyAppR R j nf C.args)`.  Since
`params_len` gives `C.params.length = D.np = D.params.length`, `VExpr.mkPi_inj`
(`Theory/Inductive/Telescope.lean:237`) reads both components off the agreement equation at
once (`instAt_ctor_body_eq`):

* `D.params = C.params` — F3's syntactic half, for free; and
* the instantiated body **is** `mkPi (C.fieldTypesR D R) (D.tyAppR R j nf C.args)`.

`instAt_ctor_hpi` then computes §8.9's `hpi` outright by `instL_mkPi` + `instAll_mkPi` +
`atRec_tyAppH`: `As` is the restored field telescope instantiated and `B'` is
`D.tyAppR' R j nf (D.atRecTele C.args)` instantiated.  So **`hpi` is not data either**, and
`instAll B' (bvars nr nf)` is a `tyAppR'` on the nose — which is what
`substC_minorBody_defeq_of_conv`'s `hconv` (§8.9's type-head defeq, no `np` bound) then converts
to the substituted motive's domain.  Nothing here is `rfl`-at-`np = 0`: `mkPi_inj` is applied at
a telescope of length `D.np`, and the conclusion is *stronger* the larger `D.np` is.

`[]`-check: `instAt_ctor_body_eq` and `instAt_ctor_hpi` are equations between expressions with
no ambient context, so the `[]` test does not apply; their hypotheses are an equation
(`ctor_agree`) and a length (`params_len`), neither of which degenerates.

### And the ctor head's `hsplit` is a theorem too — the asymmetry with the type head

§8.7's `hsplit` says the presented head's type really has `npJ j` leading pis *syntactically*.
For the **type** head that cannot be proved: F1 makes `T.type` only *definitionally* the
canonical pi-telescope (`VIndType.WF.canon` is an `IsDefEqType`), which is why `hsplit` is a
hypothesis of `tyVal_hasType_of_faithful`.  For the **constructor** head it is mechanical, by
F2: `VIndCtor.type` *is* the telescope on the nose, and
`VIndCtor.splitPis_type_instL` splits it at `C.params.length` by `splitPis_mkPi`.  So the
`hsplit` half of §8.7 is data for one clause and a theorem for the other.

### What is left, and the `PiInv` line

`hargs` — the presented spine `R.tyArgs j` typed against those `npJ j` binders — remains data,
and `instAt_indep_of_tyArgs` (`NestedRules.lean:1509`) says no restoration-independent argument
can produce it.  The route taken here is **forward**: `HasType.const` for the declared constant
plus `HasType.mkApp'` for the spine, which is how `tyVal_hasType_of_faithful` already does it.
The *inverting* route — recovering `HasArgs` from a typed application — is
`HasArgs.of_mkApp'` (`Theory/Typing/PatWF.lean:146`), which takes `env.WF` **and**
`env.PiInv`; it is **not** used anywhere in this file, and given that `ConvPiFromEntry` is false
over `Ordered`, taking it would put this whole cone behind `VEnv.WF`.  So: `hargs` stays data,
and it stays `PiInv`-free. -/

namespace VEnv
variable {env : VEnv} {σ : CSubst} {U : Nat}

/-- **A well-formed context mentions nothing in a fresh `σ`'s domain.**  `IsDefEq.noCSubst'`
iterated along the context. -/
theorem OnCtx.noCSubst (henv : env.Ordered) (hfresh : σ.FreshIn env) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → ∀ B ∈ Γ, B.NoCSubst σ
  | [], _, _, h => absurd h nofun
  | A :: Γ, ⟨h1, _, h2⟩, B, hB => by
    have ih := OnCtx.noCSubst henv hfresh h1
    rcases List.mem_cons.1 hB with rfl | hB
    · exact (VEnv.IsDefEq.noCSubst' (henv.noCSubst hfresh) hfresh h2 ih).1
    · exact ih B hB

/-- …so `substC` is the identity on it. -/
theorem OnCtx.substC_eq (henv : env.Ordered) (hfresh : σ.FreshIn env)
    {Γ : List VExpr} (h : OnCtx Γ (env.IsType U)) :
    Γ.map (VExpr.substC · σ) = Γ := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    rw [List.map_cons, (OnCtx.noCSubst henv hfresh h A (List.mem_cons_self ..)).substC_eq,
      ih h.1]

end VEnv

namespace VInductDecl'

/-- **`hpar`, free.**  The parameter telescope at the recursor's numbering, well-formed in the
substituted environment, from `D.WF env` and a fresh `σ` — no side condition. -/
theorem onCtxParamsAtRec_substC {env e : VEnv} {D : VInductDecl'} {σ : CSubst}
    (henv : env.Ordered) (hD : D.WF env) (hfresh : σ.FreshIn env)
    (hσ : σ.WF env e D.recUvars) :
    OnCtx ((D.atRecTele D.params).reverse) (e.IsType D.recUvars) := by
  have hsrc := hD.onCtxParamsAtRec
  have h := VEnv.OnCtx.substC hσ hsrc
  rwa [VEnv.OnCtx.substC_eq henv hfresh hsrc] at h

end VInductDecl'

namespace VIndCtor

/-- **The ctor head's `hsplit`, as a theorem.**  F2: a constructor's stored type is the
telescope on the nose, so `splitPis` at `C.params.length` is `splitPis_mkPi`.  There is no
counterpart for the *type* head, where F1 leaves `T.type` only definitionally canonical. -/
theorem splitPis_type_instL {C : VIndCtor} {D : VInductDecl'} {j n : Nat} {ls : List VLevel}
    (hlen : C.params.length = n) :
    VExpr.splitPis n ((C.type D j).instL ls)
      = (C.params.map (VExpr.instL ls),
         VExpr.mkPi ((C.fields.map (·.type)).map (VExpr.instL ls))
           ((C.canonResult D j).instL ls)) := by
  rw [VIndCtor.type, VExpr.instL_mkPi, List.map_append, VExpr.mkPi_append,
    show n = (C.params.map (VExpr.instL ls)).length from by rw [List.length_map, hlen],
    VExpr.splitPis_mkPi]

end VIndCtor

namespace VIndRestore
section
variable {R : VIndRestore} {D : VInductDecl'} {C : VIndCtor} {j npJ : Nat}

/-- **`Faithful.ctor_agree` read componentwise.**  `mkPi_inj` at the parameter telescope: the
agreement equation determines *both* `D.params = C.params` and the instantiated body, with no
`np` bound. -/
theorem instAt_ctor_body_eq {ci : VConstant}
    (hlen : D.params.length = C.params.length)
    (hagree : R.instAt D npJ j ci.type = C.typeR D R j) :
    D.params = C.params ∧
      VExpr.instAll (VExpr.splitPis npJ (ci.type.instL (R.tyLvls j))).2 (R.tyArgs j)
        = VExpr.mkPi (C.fieldTypesR D R) (D.tyAppR R j C.fields.length C.args) := by
  rw [VIndRestore.instAt, VIndCtor.typeR, VExpr.mkPi_append] at hagree
  exact VExpr.mkPi_inj hlen hagree

/-- **…and therefore §8.9's `hpi` is derivable, with `B'` a `tyAppR'`.**  This is the σ-free
identification §T9 flagged as the one genuinely new residual of the minor entry: it is not a
residual. -/
theorem instAt_ctor_hpi {ci : VConstant} {k : Nat}
    (hlen : D.params.length = C.params.length)
    (hagree : R.instAt D npJ j ci.type = C.typeR D R j) :
    VExpr.instAll
        (D.atRec (VExpr.instAll (VExpr.splitPis npJ (ci.type.instL (R.tyLvls j))).2
          (R.tyArgs j))) (VExpr.bvars k D.np)
      = VExpr.mkPi (VExpr.instAllTele (D.atRecTele (C.fieldTypesR D R)) (VExpr.bvars k D.np) 0)
          (VExpr.instAll (D.tyAppR' R j C.fields.length (D.atRecTele C.args))
            (VExpr.bvars k D.np) (C.fieldTypesR D R).length) := by
  rw [(instAt_ctor_body_eq hlen hagree).2, VInductDecl'.atRec, VExpr.instL_mkPi,
    VExpr.instAll_mkPi,
    show (D.tyAppR R j C.fields.length C.args).instL D.selfLvls
        = D.tyAppR' R j C.fields.length (D.atRecTele C.args) from VInductDecl'.atRec_tyAppH D]
  simp [VInductDecl'.atRecTele]

end
end VIndRestore


end Lean4Lean
