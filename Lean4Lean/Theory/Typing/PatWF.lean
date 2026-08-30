import Lean4Lean.Theory.Typing.ParamsBuild
import Lean4Lean.Theory.Typing.SpineInv
import Lean4Lean.Theory.Inductive.StructureClosed

/-!
# `VEnv.PatWF` beyond the δ fragment

Work in progress.
-/

namespace Lean4Lean

open VExpr

namespace Pattern

/-- **Inverting a `varN` match.**  The converse of `matches_varN_argPaths`: a term that
matches a `varN` chain over a `const` leaf *is* that constant applied to a spine of the
chain's depth, and the match maps are the readback. -/
theorem matches_varN_inv (c : Lean.Name) :
    ∀ (n : Nat) {e : VExpr} {m1 m2}, Matches (Pattern.varN (.const c) n) e m1 m2 →
      ∃ ls as, as.length = n ∧ e = (VExpr.const c ls).mkApp as ∧
        (∀ x, m1 x = ls) ∧ (argPaths (.const c) n).map m2 = as
  | 0, e, m1, m2, h => by
    cases h
    exact ⟨_, [], rfl, rfl, fun _ => rfl, rfl⟩
  | n+1, e, m1, m2, h => by
    cases h with
    | @var _ _ _ g1 a' h =>
      obtain ⟨ls, as, hlen, rfl, hm1, hm2⟩ := matches_varN_inv c n h
      refine ⟨ls, as ++ [a'], by simp [hlen], VExpr.mkApp_concat.symm, hm1, ?_⟩
      show List.map (fun x : Option (Pattern.varN (Pattern.const c) n).Path => x.elim a' g1)
        (argPaths.argPathsSucc (.const c) n (argPaths (.const c) n)) = _
      rw [argPaths.argPathsSucc, List.map_append, List.map_map, List.map_cons, List.map_nil]
      exact congrArg (· ++ [a']) hm2

/-- **Inverting an ι-shaped match.**  The converse of `matches_iota_paths`. -/
theorem matches_iota_inv (r c : Lean.Name) {m n : Nat} {e : VExpr} {m1 m2}
    (h : Matches (SimplePattern.iota r m c n).toPattern e m1 m2) :
    ∃ ls ls' as bs, as.length = m ∧ bs.length = n ∧
      e = (VExpr.const r ls).mkApp (as ++ [(VExpr.const c ls').mkApp bs]) ∧
      (∀ x, m1 (Sum.inl x) = ls) ∧ (∀ y, m1 (Sum.inr y) = ls') ∧
      (argPaths (.const r) m).map (fun p => m2 (Sum.inl p)) = as ∧
      (argPaths (.const c) n).map (fun p => m2 (Sum.inr p)) = bs := by
  cases h with
  | app h1 h2 =>
    obtain ⟨ls, as, hlen, rfl, hm1, hm2⟩ := matches_varN_inv r m h1
    obtain ⟨ls', bs, hlen', rfl, hm1', hm2'⟩ := matches_varN_inv c n h2
    exact ⟨ls, ls', as, bs, hlen, hlen', VExpr.mkApp_concat.symm, hm1, hm1', hm2, hm2'⟩

end Pattern

namespace VEnv

open VExpr (mkPi mkLams mkApp instAll instTele)

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-! ## Π-injectivity as a named hypothesis

`VEnv.PatWF`'s ι and quot cases both need to reconcile a domain that `HasType.app_inv`
*invents* for a spine's head with the domain the head's declared type *states*.  That is
Π-injectivity and nothing else, so it is carried as the explicit hypothesis
`VEnv.PiInv` (`Theory/Typing/Injectivity.lean`, which is `IsDefEqU.forallE_inv`'s type
verbatim) rather than imported: every theorem below that needs it says so in its statement,
and `VEnv.piInv_axiom` is the single point of contact with the open theorem.

**Nothing in this file cites `IsDefEqU.forallE_inv`.**  The `sorry`-free content is
`PiInv → PatWF`; `piInv_axiom` is what turns it into an unconditional (and `sorryAx`-tainted)
statement, at the call site of the reader's choosing. -/

/-- **Peeling a λ-telescope off a typing.**  The converse of `HasType.mkLams`; the one step
that is not structural is reconciling the body's invented type with the declared codomain,
which is `PiInv`. -/
theorem HasType.mkLams_inv (henv : env.WF) (hpi : env.PiInv U) :
    ∀ {As : List VExpr} {Γ b B}, OnCtx Γ (env.IsType U) →
      env.HasType U Γ (VExpr.mkLams As b) (VExpr.mkPi As B) →
      OnCtx (As.reverse ++ Γ) (env.IsType U) ∧ env.HasType U (As.reverse ++ Γ) b B
  | [], _, _, _, hΓ, h => ⟨hΓ, h⟩
  | A :: As, Γ, b, B, hΓ, h => by
    rw [VExpr.mkLams_cons, VExpr.mkPi_cons] at h
    obtain ⟨hA, hb⟩ := HasType.lam_inv henv.ordered hΓ h
    obtain ⟨T, hT⟩ := hb
    have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, hA⟩
    obtain ⟨u, hAu⟩ := hA
    have hlam : env.HasType U Γ (.lam A (VExpr.mkLams As b)) (.forallE A T) := .lam hAu hT
    obtain ⟨-, _, hTB⟩ := hpi hΓ (hlam.uniqU henv hΓ h)
    have hT' : env.HasType U (A::Γ) (VExpr.mkLams As b) (VExpr.mkPi As B) :=
      HasType.defeqU_r henv hΓA ⟨_, hTB⟩ hT
    rw [VExpr.tele_ctx_cons]
    exact HasType.mkLams_inv henv hpi (As := As) (Γ := A :: Γ) hΓA hT'

/-- **A rule's body, typed under its own telescope, in an arbitrary context.**  What
`IsDefEq.extra_applied` asks for beyond the spine, supplied from `VEnv.WF` plus `PiInv`. -/
theorem rule_body_typing (henv : env.WF) (hpi : env.PiInv U) (hΓ : OnCtx Γ (env.IsType U))
    {df : VDefEq} (hdf : env.defeqs df) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    {As : List VExpr} {body ty : VExpr} (hbody : env.HasType df.uvars [] body df.type)
    (hl : body = mkLams As lhs) (ht : df.type = mkPi As ty) :
    OnCtx ((As.map (VExpr.instL ls)).reverse ++ Γ) (env.IsType U) ∧
      env.HasType U ((As.map (VExpr.instL ls)).reverse ++ Γ) (lhs.instL ls) (ty.instL ls) := by
  rw [hl, ht] at hbody
  have h2 := HasType.instL (ls := ls) hls hbody
  rw [VExpr.instL_mkLams, VExpr.instL_mkPi] at h2
  exact HasType.mkLams_inv henv hpi hΓ (h2.weak0 henv.ordered)

/-- **`IsDefEq.extra_applied`, with only the spine left to supply.** -/
theorem IsDefEq.extra_applied' (henv : env.WF) (hpi : env.PiInv U)
    (hΓ : OnCtx Γ (env.IsType U)) {df : VDefEq} (hdf : env.defeqs df) {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = df.uvars)
    {As : List VExpr} {lhs rhs ty : VExpr}
    (hl : df.lhs = mkLams As lhs) (hr : df.rhs = mkLams As rhs) (ht : df.type = mkPi As ty)
    {as : List VExpr} (hargs : env.HasArgs U Γ (As.map (VExpr.instL ls)) as) :
    env.IsDefEq U Γ (instAll (lhs.instL ls) as) (instAll (rhs.instL ls) as)
      (instAll (ty.instL ls) as) := by
  obtain ⟨hwl, hwr⟩ := henv.ordered.defEqWF hdf
  obtain ⟨hOn, hlty⟩ := rule_body_typing henv hpi hΓ hdf hls hwl hl ht
  obtain ⟨-, hrty⟩ := rule_body_typing henv hpi hΓ hdf hls hwr hr ht
  exact VEnv.IsDefEq.extra_applied henv.ordered hdf hls hlen hl hr ht hOn hargs hlty hrty

/-- **`HasArgs.concat`, inverted.**  Splitting the last argument off a spine, at the
telescope's last entry with the earlier arguments substituted. -/
theorem HasArgs.concat_inv :
    ∀ {As as : List VExpr} {A a}, as.length = As.length →
      env.HasArgs U Γ (As ++ [A]) (as ++ [a]) →
      env.HasArgs U Γ As as ∧ env.HasType U Γ a (VExpr.instAll A as 0)
  | [], as, A, a, hlen, h => by
    cases List.eq_nil_of_length_eq_zero hlen
    let .cons ha .nil := h
    exact ⟨.nil, by simpa using ha⟩
  | A₀ :: As, as, A, a, hlen, h => by
    match as, hlen with
    | a₀ :: as, hlen =>
      have hlen : as.length = As.length := by simpa using hlen
      let .cons h0 h' := h
      simp only [List.append_eq] at h'
      rw [VExpr.instTele_append, Nat.zero_add] at h'
      have ⟨ih1, ih2⟩ := HasArgs.concat_inv (by simpa using hlen) h'
      refine ⟨.cons h0 ih1, ?_⟩
      rw [VExpr.instAll_cons, Nat.zero_add, hlen]
      simpa using ih2

/-- **`HasArgs.of_mkApp` with `PiInv` as a hypothesis.**  `Theory/Typing/SpineInv.lean`'s
version cites `IsDefEqU.forallE_inv` directly; this one takes it as an argument, which is
what keeps `forallE_inv` out of this file's cone.  The proof is that file's, verbatim except
for the one call. -/
theorem HasArgs.of_mkApp' (henv : env.WF) (hpi : env.PiInv U) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (as : List VExpr) {As f B A}, as.length = As.length →
      env.HasType U Γ f (VExpr.mkPi As B) → env.HasType U Γ (f.mkApp as) A →
      env.HasArgs U Γ As as := by
  intro as
  induction as with
  | nil =>
    intro As f B A hlen _ _
    cases List.eq_nil_of_length_eq_zero hlen.symm
    exact .nil
  | cons a as ih =>
    intro As f B A hlen hf h
    match As, hlen with
    | A₀ :: As, hlen =>
      rw [VExpr.mkPi_cons] at hf
      rw [VExpr.mkApp_cons] at h
      obtain ⟨A₀', B₀', hf', ha'⟩ := HasType.mkApp_arg henv.ordered hΓ as h
      obtain ⟨⟨_, hAA⟩, -⟩ := hpi hΓ (hf'.uniqU henv hΓ hf)
      have ha : env.HasType U Γ a A₀ := HasType.defeqU_r henv hΓ ⟨_, hAA⟩ ha'
      have h1 := hf.app ha
      rw [VExpr.inst_mkPi_zero] at h1
      refine .cons ha (ih ?_ h1 h)
      simpa using Nat.succ.inj hlen

/-! ## The quotient rule

The quot case of `PatWF`, in full.  Every constant here is `rfl`-checked against
`Theory/Quot.lean`'s `quotDefEq`, `quotLiftConst` and `quotMkConst`; nothing is transcribed
by hand.

The shape of the argument, which the ι case will repeat:

1. invert the match (`Pattern.matches_iota_inv`) into `Quot.lift.{ls} a₁ … a₅
   (Quot.mk.{ls'} b₁ b₂ b₃)`;
2. invert the *typing* of that spine against `Quot.lift`'s declared telescope
   (`HasArgs.of_mkApp` — **this is the one step that consumes `PiInv`**), and again against
   `Quot.mk`'s;
3. rebuild the spine that saturates the *rule's* telescope: the recursor's first five
   arguments, then the constructor's last field, whose declared domain is the recursor's
   first argument -- and reconciling those two is exactly the `Check`'s parameter clause;
4. fire the rule at that spine (`IsDefEq.extra_applied'`) and read both sides;
5. bridge the fired left-hand side back to `e` by one `appDF` over the major premise, whose
   own congruence is `mkAppDF` at the level equivalence the `Check`'s level clause supplies.

Step 3 and step 5 are where the `Check` clauses are consumed, and they are consumed for
real: with `Check.true` there would be nothing to convert `b₃`'s declared type `b₁` to the
rule's `a₁`, and nothing to bridge `Quot.mk.{ls'}` to `Quot.mk.{ls}`. -/

theorem instAll_bvar_get0 {as : List VExpr} {t B : Nat} {a : VExpr} (h : as[t]? = some a)
    (hB : as.length = B + 1 + t) : VExpr.instAll (.bvar B) as 0 = a := by
  rw [VExpr.instAll_bvar_get h (by omega)]; simp

def quotTele : List VExpr := (VExpr.peelLams quotDefEq.lhs).1
def quotLiftDoms : List VExpr := (VExpr.peelPis quotLiftConst.type).1
def quotMkDoms : List VExpr := (VExpr.peelPis quotMkConst.type).1

theorem quot_lhs_eq : quotDefEq.lhs = VExpr.mkLams quotTele (VExpr.peelLams quotDefEq.lhs).2 := rfl
theorem quot_rhs_eq :
    quotDefEq.rhs = VExpr.mkLams quotTele ((VExpr.bvar 2).app (VExpr.bvar 0)) := rfl
theorem quot_type_eq : quotDefEq.type = VExpr.mkPi quotTele (VExpr.bvar 3) := rfl
theorem quotLift_type_eq : quotLiftConst.type = VExpr.mkPi quotLiftDoms (VExpr.bvar 3) := rfl
theorem quotMk_type_eq : quotMkConst.type = VExpr.mkPi quotMkDoms
  (((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 2)).app (VExpr.bvar 1)) := rfl
theorem quotLiftDoms_eq : quotLiftDoms = quotTele.take 5 ++
    [((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 4)).app (VExpr.bvar 3)] := rfl
theorem quotTele_eq : quotTele = quotTele.take 5 ++ [VExpr.bvar 4] := rfl
theorem quotMkDoms_eq : quotMkDoms = quotMkDoms.take 2 ++ [VExpr.bvar 1] := rfl

theorem patWF_quot (henv : env.WF) (hpi : env.PiInv U)
    (hdf : env.defeqs quotDefEq)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    (hmkc : env.constants ``Quot.mk = some quotMkConst)
    {e A : VExpr} {m1 m2} (hm : quotPat.Matches e m1 m2)
    (hΓ : OnCtx Γ (env.IsType U)) (hT : env.HasType U Γ e A)
    (hck : quotCheck.OK (env.IsDefEqU U Γ) m1 m2) :
    env.IsDefEqU U Γ e (quotRHS.apply m1 m2) := by
  obtain ⟨ls, ls', as, bs, hlen, hlen', rfl, hm1l, hm1r, hasr, hbsr⟩ :=
    Pattern.matches_iota_inv ``Quot.lift ``Quot.mk hm
  obtain ⟨a1, a2, a3, a4, a5, rfl⟩ : ∃ a1 a2 a3 a4 a5, as = [a1,a2,a3,a4,a5] := by
    match as, hlen with | [_,_,_,_,_], _ => exact ⟨_,_,_,_,_, rfl⟩
  obtain ⟨b1, b2, b3, rfl⟩ : ∃ b1 b2 b3, bs = [b1,b2,b3] := by
    match bs, hlen' with | [_,_,_], _ => exact ⟨_,_,_, rfl⟩
  -- the head's level list
  obtain ⟨T0, hT0⟩ := HasType.mkApp_head henv.ordered hΓ _ _ _ hT
  obtain ⟨ci, hci, hlsWF, hlslen⟩ := HasType.const_inv henv.ordered hΓ hT0
  rw [hlift] at hci; cases hci
  -- `Quot.lift`'s declared telescope, and the spine that saturates it
  have hfun : env.HasType U Γ (.const ``Quot.lift ls)
      (VExpr.mkPi (quotLiftDoms.map (VExpr.instL ls)) (VExpr.bvar 3)) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hlift hlsWF hlslen
    rwa [quotLift_type_eq, VExpr.instL_mkPi, show (VExpr.bvar 3).instL ls = .bvar 3 from rfl] at h
  have hargsLift : env.HasArgs U Γ (quotLiftDoms.map (VExpr.instL ls))
      ([a1,a2,a3,a4,a5] ++ [(VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3]]) :=
    HasArgs.of_mkApp' henv hpi hΓ _ rfl hfun hT
  -- readbacks, entry by entry (no substitution: `a1 … b3` stay opaque)
  have hasr0 := hasr; have hbsr0 := hbsr
  rw [argPaths5] at hasr
  rw [argPaths3] at hbsr
  simp only [List.map_cons, List.map_nil] at hasr hbsr
  injection hasr with ha1 hasr; injection hasr with ha2 hasr
  injection hasr with ha3 hasr; injection hasr with ha4 hasr
  injection hasr with ha5 hasr
  injection hbsr with hb1 hbsr; injection hbsr with hb2 hbsr
  injection hbsr with hb3e hbsr
  -- split the major premise off the recursor spine
  rw [quotLiftDoms_eq, List.map_append, List.map_cons, List.map_nil] at hargsLift
  obtain ⟨hAs, hmaj⟩ :=
    HasArgs.concat_inv (env := env) (U := U) (Γ := Γ)
      (As := (quotTele.take 5).map (VExpr.instL ls))
      (A := (((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 4)).app
        (VExpr.bvar 3)).instL ls)
      (as := [a1,a2,a3,a4,a5]) (a := (VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3])
      rfl hargsLift
  rw [show ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 4)).app
        (VExpr.bvar 3)).instL ls)
      = (((VExpr.const `Quot [ls.getD 0 .zero]).app (VExpr.bvar 4)).app (VExpr.bvar 3)) from rfl,
    VExpr.instAll_app, VExpr.instAll_app, VExpr.instAll_const,
    instAll_bvar_get0 (t := 0) rfl rfl, instAll_bvar_get0 (t := 1) rfl rfl] at hmaj
  -- the constructor's level list, and its own spine
  obtain ⟨T1, hT1⟩ := HasType.mkApp_head henv.ordered hΓ _ _ _ hmaj
  obtain ⟨ci', hci', hls'WF, hls'len⟩ := HasType.const_inv henv.ordered hΓ hT1
  rw [hmkc] at hci'; cases hci'
  have hmkfun : env.HasType U Γ (.const ``Quot.mk ls')
      (VExpr.mkPi (quotMkDoms.map (VExpr.instL ls'))
        ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 2)).app
          (VExpr.bvar 1)).instL ls')) := by
    have h := HasType.const (env := env) (U := U) (Γ := Γ) hmkc hls'WF hls'len
    rwa [quotMk_type_eq, VExpr.instL_mkPi] at h
  have hargsMk : env.HasArgs U Γ (quotMkDoms.map (VExpr.instL ls')) [b1,b2,b3] :=
    HasArgs.of_mkApp' henv hpi hΓ _ rfl hmkfun hmaj
  have hargsMk0 := hargsMk
  rw [quotMkDoms_eq, List.map_append, List.map_cons, List.map_nil] at hargsMk
  obtain ⟨hEs, hb3t⟩ :=
    HasArgs.concat_inv (env := env) (U := U) (Γ := Γ)
      (As := (quotMkDoms.take 2).map (VExpr.instL ls'))
      (A := (VExpr.bvar 1).instL ls') (as := [b1,b2]) (a := b3) rfl hargsMk
  rw [show ((VExpr.bvar 1).instL ls') = .bvar 1 from rfl,
    instAll_bvar_get0 (t := 0) rfl rfl] at hb3t
  -- the check clauses
  obtain ⟨hpar, -, hlev⟩ := iotaCheck_OK.1 hck
  rw [show ((Pattern.argPaths (.const ``Quot.lift) 5).take 2).zip
        ((Pattern.argPaths (.const ``Quot.mk) 3).take 2)
      = [(some (some (some (some none))), some (some none)),
         (some (some (some none)), some none)] from rfl] at hpar
  have hcka1 : env.IsDefEqU U Γ a1 b1 := by
    rw [← ha1, ← hb1]
    exact hpar (some (some (some (some none))), some (some none)) (.head _)
  have hcka2 : env.IsDefEqU U Γ a2 b2 := by
    rw [← ha2, ← hb2]
    exact hpar (some (some (some none)), some none) (.tail _ (.head _))
  have hlevel : ls.getD 0 .zero ≈ ls'.getD 0 .zero := by
    have h := hlev (0, 0) (List.mem_singleton_self _)
    rw [show (m1 (Pattern.LPath.head (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern))
        = ls from hm1l _,
      show (m1 (iotaLeafCtor ``Quot.lift ``Quot.mk 5 3)) = ls' from hm1r _] at h
    exact h
  -- the spine that saturates the rule's own telescope
  have hu0WF : ∀ l ∈ [ls.getD 0 VLevel.zero], l.WF U := by
    have hmem : ls.getD 0 VLevel.zero ∈ ls := by
      match ls, hlslen with | _ :: _, _ => exact .head _
    intro l hl
    cases hl with
    | head => exact hlsWF _ hmem
    | tail _ h => cases h
  have hforall2 : List.Forall₂ (· ≈ ·) ls' [ls.getD 0 VLevel.zero] := by
    match ls', hls'len, hlevel with
    | [_], _, hlevel => exact .cons hlevel.symm .nil
  have hb3a1 : env.HasType U Γ b3 a1 :=
    HasType.defeqU_r henv hΓ (IsDefEqU.symm hcka1) hb3t
  have j4 : VExpr.instAll (.bvar 4) [a1,a2,a3,a4,a5] 0 = a1 := instAll_bvar_get0 (t := 0) rfl rfl
  have j3 : VExpr.instAll (.bvar 3) [a1,a2,a3,a4,a5] 0 = a2 := instAll_bvar_get0 (t := 1) rfl rfl
  have hargsTele : env.HasArgs U Γ (quotTele.map (VExpr.instL ls)) [a1,a2,a3,a4,a5,b3] := by
    rw [quotTele_eq, List.map_append, List.map_cons, List.map_nil]
    show env.HasArgs U Γ _ ([a1,a2,a3,a4,a5] ++ [b3])
    refine HasArgs.concat hAs ?_
    rwa [show ((VExpr.bvar 4).instL ls) = .bvar 4 from rfl, j4]
  have hrule := IsDefEq.extra_applied' henv hpi hΓ hdf hlsWF hlslen quot_lhs_eq quot_rhs_eq
    quot_type_eq hargsTele
  -- read the two sides of the fired rule
  have i5 : VExpr.instAll (.bvar 5) [a1,a2,a3,a4,a5,b3] 0 = a1 := instAll_bvar_get0 (t := 0) rfl rfl
  have i4 : VExpr.instAll (.bvar 4) [a1,a2,a3,a4,a5,b3] 0 = a2 := instAll_bvar_get0 (t := 1) rfl rfl
  have i3 : VExpr.instAll (.bvar 3) [a1,a2,a3,a4,a5,b3] 0 = a3 := instAll_bvar_get0 (t := 2) rfl rfl
  have i2 : VExpr.instAll (.bvar 2) [a1,a2,a3,a4,a5,b3] 0 = a4 := instAll_bvar_get0 (t := 3) rfl rfl
  have i1 : VExpr.instAll (.bvar 1) [a1,a2,a3,a4,a5,b3] 0 = a5 := instAll_bvar_get0 (t := 4) rfl rfl
  have i0 : VExpr.instAll (.bvar 0) [a1,a2,a3,a4,a5,b3] 0 = b3 := instAll_bvar_get0 (t := 5) rfl rfl
  rw [instL_peelLams_quotDefEq_lhs hlslen, quotLiftArgs, quotMkArgs,
    show (((VExpr.bvar 2).app (VExpr.bvar 0)).instL ls) = (VExpr.bvar 2).app (VExpr.bvar 0)
      from rfl] at hrule
  simp only [List.map_append, List.map_cons, List.map_nil, VExpr.instAll_mkApp,
    VExpr.instAll_const, VExpr.instAll_app] at hrule
  rw [i5, i4, i3, i2, i1, i0] at hrule
  -- the constructor spine's congruence, from the two parameter clauses and the level clause
  have hconstDF : env.IsDefEq U Γ (.const ``Quot.mk ls')
      (.const ``Quot.mk [ls.getD 0 VLevel.zero]) (quotMkConst.type.instL ls') :=
    .constDF hmkc hls'WF hu0WF hls'len hforall2
  rw [quotMk_type_eq, VExpr.instL_mkPi] at hconstDF
  have hDF : env.HasArgsDF U Γ (quotMkDoms.map (VExpr.instL ls')) [b1,b2,b3] [a1,a2,b3] := by
    let .cons k1 (.cons k2 (.cons k3 .nil)) := hargsMk0
    exact .cons (IsDefEqU.of_l henv hΓ (IsDefEqU.symm hcka1) k1)
      (.cons (IsDefEqU.of_l henv hΓ (IsDefEqU.symm hcka2) k2) (.cons k3 .nil))
  have hmkDF := IsDefEq.mkAppDF hDF hconstDF
  -- the recursor's head, applied to its first five arguments
  have hfun5 : env.HasType U Γ (.const ``Quot.lift ls)
      (VExpr.mkPi ((quotTele.take 5).map (VExpr.instL ls))
        (VExpr.mkPi [(((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 4)).app
          (VExpr.bvar 3)).instL ls] (VExpr.bvar 3))) := by
    rw [← VExpr.mkPi_append]
    rwa [quotLiftDoms_eq, List.map_append, List.map_cons, List.map_nil] at hfun
  have hF := HasType.mkApp' hAs hfun5
  rw [VExpr.instAll_mkPi, VExpr.instAllTele_cons, VExpr.instAllTele_nil,
    show ((((VExpr.const `Quot [VLevel.param 0]).app (VExpr.bvar 4)).app
        (VExpr.bvar 3)).instL ls)
      = (((VExpr.const `Quot [ls.getD 0 .zero]).app (VExpr.bvar 4)).app (VExpr.bvar 3)) from rfl,
    VExpr.instAll_app, VExpr.instAll_app, VExpr.instAll_const, j4, j3] at hF
  have hmajDF : env.IsDefEq U Γ ((VExpr.const ``Quot.mk ls').mkApp [b1,b2,b3])
      ((VExpr.const ``Quot.mk [ls.getD 0 VLevel.zero]).mkApp [a1,a2,b3])
      (((VExpr.const `Quot [ls.getD 0 VLevel.zero]).app a1).app a2) :=
    IsDefEqU.of_l henv hΓ ⟨_, hmkDF⟩ hmaj
  have hcong := IsDefEq.appDF hF hmajDF
  -- the pattern's right-hand side, read back
  have hgoal : Pattern.RHS.apply m1 m2 quotRHS = .app a4 b3 := by
    have hsp := spineRHS_apply (r := ``Quot.lift) (c := ``Quot.mk) (m := 5) (n := 3)
      (head := Pattern.RHS.var (Sum.inl (some none))) (k := 0) (i := 2)
      (m1 := m1) (m2 := m2) hasr0 hbsr0
    refine hsp.trans ?_
    show VExpr.mkApp (m2 (Sum.inl (some none))) [b3] = VExpr.app a4 b3
    rw [show m2 (Sum.inl (some none)) = a4 from ha4]
    rfl
  rw [hgoal]
  exact ⟨_, IsDefEq.trans_l henv hΓ hcong hrule⟩

/-! ## What the quot case closes

`PatWF` quantifies over `Pat env p r`, whose three constructors are δ, ι and quot.  The δ
case is `VEnv.patWF_delta` (`Theory/Typing/ParamsBuild.lean`, unconditional) and the quot
case is `patWF_quot` above, so `PatWF` now holds for every environment that registers no
ι-rule -- **strictly more environments than `DeltaFragment`, which excluded the quotient
rule.**  The ι case is open; see `docs/handoff-patwf.md` for exactly what it still owes. -/

/-- The environments this file's `PatWF` covers: no ι-rule is registered.  Stated as a
negation about `VInductDecl'.iotaRule` rather than about `Pat`, so that it says something
about the environment rather than restating the goal. -/
def IotaFree (env : VEnv) : Prop :=
  ∀ {D : VInductDecl'} {j q : Nat} {C : VIndCtor}, ¬ env.defeqs (D.iotaRule j q C)

/-- **`PatWF` for every ι-free environment**, from `VEnv.WF` and `PiInv`. -/
theorem patWF_of_iotaFree (henv : env.WF) (hpi : env.PiInv U) (hfree : env.IotaFree) :
    env.PatWF U := by
  intro p r e A m1 m2 Γ hp hm hΓ hT hck
  cases hp with
  | delta hv hrule => exact patWF_delta henv hv hrule hm hΓ hT
  | iota _ _ _ _ hrule => exact absurd hrule hfree
  | quot hdf hlift hmk => exact patWF_quot henv hpi hdf hlift hmk hm hΓ hT hck

/-- **`VEnv.Params` for every ι-free environment**, from `VEnv.WF` and `PiInv`. -/
@[instance_reducible] def paramsOfIotaFree {env : VEnv} (henv : env.WF) (U : Nat)
    (hpi : env.PiInv U) (hfree : env.IotaFree) : Params :=
  paramsOfWF henv U (patWF_of_iotaFree henv hpi hfree)

/-! ## Non-vacuity

Two separate questions, kept separate.

**The conclusion is not a reflexivity.**  `quotPat_matches_nontrivial` exhibits a match at
which `quotRHS.apply m1 m2` is *syntactically different* from the matched term, so
`patWF_quot` is not trivially discharged by `IsDefEqU.rfl` at its own hypotheses.
**[machine-checked]**

**A full witness -- a `VEnv.WF` environment carrying `quotDefEq` together with a well-typed
redex -- is NOT constructed here.**  It would need `Quot`, `Quot.mk`, `Quot.lift` and `Eq`
present and the whole environment proved `WF`; `Verify/QuotConsts.lean`'s
`trEnv_addQuot_wit` is where such a witness would come from.  Do not cite this file as
establishing that. -/

theorem quotPat_matches_nontrivial :
    ∃ (e : VExpr), ∃ m1 m2, quotPat.Matches e m1 m2 ∧
      Pattern.RHS.apply m1 m2 quotRHS ≠ e := by
  obtain ⟨m1, m2, hm, -, -, ha, hb⟩ := matches_iota_paths ``Quot.lift ``Quot.mk
    [.zero, .zero] [.zero]
    [.sort .zero, .sort .zero, .sort .zero, .bvar 0, .sort .zero]
    [.sort .zero, .sort .zero, .bvar 1] (m := 5) (n := 3) rfl rfl
  refine ⟨_, m1, m2, hm, ?_⟩
  have hsp := spineRHS_apply (r := ``Quot.lift) (c := ``Quot.mk) (m := 5) (n := 3)
    (head := Pattern.RHS.var (Sum.inl (some none))) (k := 0) (i := 2)
    (m1 := m1) (m2 := m2) ha hb
  have hrhs : Pattern.RHS.apply m1 m2 quotRHS
      = VExpr.app (m2 (Sum.inl (some none))) (VExpr.bvar 1) := hsp
  intro h
  injection hrhs.symm.trans h with _ h2
  exact absurd h2 (by nofun)

end VEnv
end Lean4Lean
