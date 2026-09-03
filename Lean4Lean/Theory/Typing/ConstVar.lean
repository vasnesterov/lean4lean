import Lean4Lean.Theory.Typing.StrengthenAxiom
import Lean4Lean.Theory.Typing.Strong

/-!
# The `const`-to-variable transport

`Theory/Typing/ConstSubst.lean`'s header names two environment transports that `Theory/`
had — `IsDefEq.mono` (weaken along `env ≤ env'`) and `IsDefEq.instL` (instantiate the
universe parameters) — and adds a third, `CSubst`, which replaces a constant by a **closed
term that inhabits its type**.  This file adds the fourth, and the one that corner needed:
replace a constant by a **context variable**, which needs no inhabitant at all.

    env.addConst c ci = some env'  ⟹  a judgement over env' becomes a judgement over env
                                      in a context extended by entries `ci.type.instL ls`

The point is `docs/handoff-weakn.md` §2.1: `StrengtheningAxiom.AxiomConservativity` was
proved to *imply* the strengthening target, but the converse was unbuilt, so the residual
was only known to be *a priori stronger*.  It is stronger for a concrete reason: `constDF`
admits `.const c ls` at **every** well-formed level list `ls`, while one context entry
supplies one instance.  This file closes the converse, so the two are **equivalent**.

## How the level-list problem is solved

Two ingredients, both of which the previous pass recorded as missing:

* **The finitely many level lists.**  Rather than extracting them from the derivation (not
  expressible: a derivation is a `Prop`), the induction *produces* a list `L₂` of the level
  lists its `constDF`-at-`c` nodes use, and its conclusion is universally quantified over
  every `L'` that **covers** `L₂` (`LCov`).  Since every term in the conclusion is computed
  at `L'`, no stability lemma and no context weakening is needed: at a `trans` node the two
  induction hypotheses are instantiated at the *same* `L'` and their middle terms are
  syntactically equal on the nose.
* **`ci.type.instL ls ≡ ci.type.instL ls'` for `ls ≈ ls'`.**  `ConstSubst.lean`'s header
  says this congruence "is not available".  It **is**: `VEnv.IsDefEq.instL_r`
  (`Theory/Typing/Strong.lean`) is exactly it, and is `sorry`-free and non-circular.  It is
  what lets one context entry serve every level list in its `≈`-class, which is what makes
  the finite list finite.

Nothing here mentions `IsDefEqU.weakN_iff`.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## 1. Level lists up to equivalence -/

/-- Pointwise equivalence of level lists — the relation `constDF` relates its two level
lists by. -/
abbrev LEqv (ls ls' : List VLevel) : Prop := List.Forall₂ (· ≈ ·) ls ls'

theorem LEqv.refl (ls : List VLevel) : LEqv ls ls := List.Forall₂.rfl fun _ _ => rfl

theorem LEqv.symm {ls ls' : List VLevel} (h : LEqv ls ls') : LEqv ls' ls := by
  induction h with
  | nil => exact .nil
  | cons h1 _ ih => exact .cons (VLevel.equiv_def'.2 (VLevel.equiv_def'.1 h1).symm) ih

theorem LEqv.trans (h1 : LEqv ls ls') (h2 : LEqv ls' ls'') : LEqv ls ls'' :=
  List.Forall₂.trans (fun _ _ _ ha hb => ha.trans hb) h1 h2

/-- `LWF U L`: every list in `L` is a legal level argument for a constant with `U` universe
parameters, in a derivation with `U` universe parameters. -/
def LWF (U : Nat) (L : List (List VLevel)) : Prop :=
  ∀ ls ∈ L, ls.length = U ∧ ∀ l ∈ ls, l.WF U

theorem LWF.nil : LWF U [] := fun _ h => nomatch h

theorem LWF.append (h1 : LWF U L1) (h2 : LWF U L2) : LWF U (L1 ++ L2) := by
  intro ls h
  rcases List.mem_append.1 h with h | h
  · exact h1 _ h
  · exact h2 _ h

theorem LWF.one (h1 : ls.length = U) (h2 : ∀ l ∈ ls, l.WF U) : LWF U [ls] := by
  intro x hx
  rw [List.mem_singleton.1 hx]
  exact ⟨h1, h2⟩

/-- `LCov L' L`: every list of `L` has an `≈`-equivalent representative in `L'`.  This is
the *only* thing the main induction asks of the level list it is run at. -/
def LCov (L' L : List (List VLevel)) : Prop := ∀ ls ∈ L, ∃ ls' ∈ L', LEqv ls' ls

theorem LCov.left (h : LCov L' (L1 ++ L2)) : LCov L' L1 :=
  fun _ hm => h _ (List.mem_append.2 (.inl hm))

theorem LCov.right (h : LCov L' (L1 ++ L2)) : LCov L' L2 :=
  fun _ hm => h _ (List.mem_append.2 (.inr hm))

/-- The index of `ls` in `L` up to `≈`, or `L.length` if there is none. -/
noncomputable def lvlIdx (L : List (List VLevel)) (ls : List VLevel) : Nat :=
  match L with
  | [] => 0
  | ls' :: L => open Classical in if LEqv ls' ls then 0 else lvlIdx L ls + 1

theorem lvlIdx_congr (h : LEqv ls ls') : ∀ L, lvlIdx L ls = lvlIdx L ls'
  | [] => rfl
  | a :: L => by
    simp only [lvlIdx]
    have : LEqv a ls ↔ LEqv a ls' := ⟨fun hh => hh.trans h, fun hh => hh.trans h.symm⟩
    split <;> split <;> simp_all [lvlIdx_congr h L]

/-- If `L` covers `ls`, the index points at an `≈`-equivalent entry — returned as an explicit
splitting of `L`, which is the form the `Lookup` needs. -/
theorem lvlIdx_split (h : ∃ ls' ∈ L, LEqv ls' ls) :
    ∃ L1 ls' L2, L = L1 ++ ls' :: L2 ∧ L1.length = lvlIdx L ls ∧ LEqv ls' ls := by
  induction L with
  | nil => exact absurd h (by simp)
  | cons a L ih =>
    by_cases ha : LEqv a ls
    · exact ⟨[], a, L, rfl, by simp [lvlIdx, ha], ha⟩
    · have : ∃ ls' ∈ L, LEqv ls' ls := by
        obtain ⟨x, hx, hx2⟩ := h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hx2 ha
        · exact ⟨x, hx, hx2⟩
      obtain ⟨L1, ls', L2, rfl, hlen, heq⟩ := ih this
      exact ⟨a :: L1, ls', L2, rfl, by simp [lvlIdx, ha, hlen], heq⟩

theorem lvlIdx_lt (h : ∃ ls' ∈ L, LEqv ls' ls) : lvlIdx L ls < L.length := by
  obtain ⟨L1, ls', L2, rfl, hlen, _⟩ := lvlIdx_split h
  rw [← hlen]; simp

/-! ## 2. The translation: a constant becomes a context variable

The new entries are placed at the **outer** end of the context — below `Γ`, at indices
`d + G + i` where `d` is the binder depth and `G = Γ.length`.  Bottom placement is what makes
`cvar` leave every `bvar` alone (nothing shifts) and, in particular, makes `cvar` the
identity on `c`-free terms, which is what the endpoints of the target judgement are. -/

namespace VExpr

variable (c : Name) (G : Nat) (L : List (List VLevel))

/-- Replace `.const c ls` by the context variable standing for `ls`'s `≈`-class.  `d` is the
number of binders crossed so far. -/
noncomputable def cvar : VExpr → Nat → VExpr
  | .bvar i, _ => .bvar i
  | .sort u, _ => .sort u
  | .const c' ls, d => if c' = c then .bvar (d + G + lvlIdx L ls) else .const c' ls
  | .app f a, d => .app (cvar f d) (cvar a d)
  | .lam A b, d => .lam (cvar A d) (cvar b (d+1))
  | .forallE A b, d => .forallE (cvar A d) (cvar b (d+1))

variable {c G L}

@[simp] theorem cvar_bvar : cvar c G L (.bvar i) d = .bvar i := rfl
@[simp] theorem cvar_sort : cvar c G L (.sort u) d = .sort u := rfl
@[simp] theorem cvar_app : cvar c G L (.app f a) d = .app (cvar c G L f d) (cvar c G L a d) := rfl
@[simp] theorem cvar_lam :
    cvar c G L (.lam A b) d = .lam (cvar c G L A d) (cvar c G L b (d+1)) := rfl
@[simp] theorem cvar_forallE :
    cvar c G L (.forallE A b) d = .forallE (cvar c G L A d) (cvar c G L b (d+1)) := rfl

theorem cvar_const_self : cvar c G L (.const c ls) d = .bvar (d + G + lvlIdx L ls) := by
  simp [cvar]

theorem cvar_const_other (h : c' ≠ c) : cvar c G L (.const c' ls) d = .const c' ls := by
  simp [cvar, h]

/-- **`cvar` is the identity on `c`-free terms.**  This is what bottom placement buys. -/
theorem cvar_eq_self : ∀ {e : VExpr}, e.ConstsIn (· ≠ c) → ∀ {d}, cvar c G L e d = e
  | .bvar _, _, _ | .sort _, _, _ => rfl
  | .const _ _, h, _ => cvar_const_other h
  | .app .., ⟨h1, h2⟩, _ => by simp [cvar_eq_self h1, cvar_eq_self h2]
  | .lam .., ⟨h1, h2⟩, _ => by simp [cvar_eq_self h1, cvar_eq_self h2]
  | .forallE .., ⟨h1, h2⟩, _ => by simp [cvar_eq_self h1, cvar_eq_self h2]

/-- **`cvar` commutes with lifting**, provided the lift happens strictly inside the region
the new variables sit below (`k ≤ d`). -/
theorem cvar_liftN (hk : k ≤ d) :
    ∀ {e : VExpr} {p : Nat}, cvar c G L (e.liftN p k) (d+p) = (cvar c G L e d).liftN p k := by
  intro e
  induction e generalizing d k with
  | bvar i => intro p; rfl
  | sort => intro p; rfl
  | const c' ls =>
    intro p
    by_cases h : c' = c
    · subst h
      simp only [VExpr.liftN, cvar_const_self, VExpr.liftN]
      rw [liftVar_le (by omega)]
      congr 1; omega
    · simp [VExpr.liftN, cvar_const_other h]
  | app _ _ ih1 ih2 => intro p; simp [VExpr.liftN, ih1 hk, ih2 hk]
  | lam _ _ ih1 ih2 =>
    intro p
    have : d + p + 1 = (d+1) + p := by omega
    simp [VExpr.liftN, ih1 hk, this, ih2 (k := k+1) (d := d+1) (by omega)]
  | forallE _ _ ih1 ih2 =>
    intro p
    have : d + p + 1 = (d+1) + p := by omega
    simp [VExpr.liftN, ih1 hk, this, ih2 (k := k+1) (d := d+1) (by omega)]

theorem cvar_lift : cvar c G L (e.lift) (d+1) = (cvar c G L e d).lift :=
  cvar_liftN (Nat.zero_le _) (p := 1)

/-- **`cvar` commutes with instantiation.** -/
theorem cvar_inst :
    ∀ {e : VExpr} {e₀ : VExpr} {d k : Nat},
      cvar c G L (e.inst e₀ k) (d+k) = (cvar c G L e (d+k+1)).inst (cvar c G L e₀ d) k := by
  intro e
  induction e with
  | bvar i =>
    intro e₀ d k
    show cvar c G L (VExpr.instVar i e₀ k) (d+k) = VExpr.instVar i (cvar c G L e₀ d) k
    unfold VExpr.instVar
    by_cases h1 : i < k
    · simp [h1]
    · by_cases h2 : i = k
      · subst h2
        rw [if_neg h1, if_neg h1, if_pos rfl, if_pos rfl]
        exact cvar_liftN (k := 0) (Nat.zero_le _)
      · simp only [if_neg h1, if_neg h2]; rfl
  | sort => intro e₀ d k; rfl
  | const c' ls =>
    intro e₀ d k
    by_cases h : c' = c
    · subst h
      simp only [VExpr.inst, cvar_const_self, VExpr.inst]
      unfold VExpr.instVar
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega
    · simp [VExpr.inst, cvar_const_other h]
  | app _ _ ih1 ih2 => intro e₀ d k; simp [VExpr.inst, ih1, ih2]
  | lam _ _ ih1 ih2 =>
    intro e₀ d k
    have h1 : d + k + 1 = d + (k+1) := by omega
    have h2 : d + k + 1 + 1 = d + (k+1) + 1 := by omega
    simp only [VExpr.inst, cvar_lam, ih1, h1, h2, ih2]
  | forallE _ _ ih1 ih2 =>
    intro e₀ d k
    have h1 : d + k + 1 = d + (k+1) := by omega
    have h2 : d + k + 1 + 1 = d + (k+1) + 1 := by omega
    simp only [VExpr.inst, cvar_forallE, ih1, h1, h2, ih2]

theorem cvar_inst0 {e e₀ : VExpr} {d : Nat} :
    cvar c G L (e.inst e₀) d = (cvar c G L e (d+1)).inst (cvar c G L e₀ d) :=
  cvar_inst (k := 0)

end VExpr

/-! ## 3. The translated context, and its `Lookup`s -/

/-- The context the translation lands in: the binders crossed so far, translated at their own
depths, on top of `base` (which is `Γ` followed by the new entries). -/
noncomputable def cvarCtx (c : Name) (G : Nat) (L : List (List VLevel)) (base : List VExpr) :
    List VExpr → List VExpr
  | [] => base
  | Y :: Δ => VExpr.cvar c G L Y Δ.length :: cvarCtx c G L base Δ

theorem lookup_mid (hA : A.ClosedN 0) :
    ∀ (pre post : List VExpr), Lookup (pre ++ A :: post) pre.length A
  | [], post => by
    have := Lookup.zero (ty := A) (Γ := post)
    rwa [hA.lift_eq] at this
  | X :: pre, post => by
    have := (lookup_mid hA pre post).succ (A := X)
    rwa [hA.lift_eq] at this

theorem Lookup.appendR (rest : List VExpr) :
    ∀ {Γ i A}, Lookup Γ i A → Lookup (Γ ++ rest) i A
  | _, _, _, .zero => .zero
  | _, _, _, .succ h => (Lookup.appendR rest h).succ

theorem lookup_cvarCtx {c : Name} {G : Nat} {L : List (List VLevel)} {Γ Ts : List VExpr}
    (hΓ : CtxConstsIn (· ≠ c) Γ) :
    ∀ {Δ : List VExpr} {i A}, Lookup (Δ ++ Γ) i A →
      Lookup (cvarCtx c G L (Γ ++ Ts) Δ) i (VExpr.cvar c G L A Δ.length) := by
  intro Δ
  induction Δ with
  | nil =>
    intro i A h
    rw [VExpr.cvar_eq_self (hΓ.lookup h)]
    exact h.appendR _
  | cons Y Δ ih =>
    intro i A h
    simp only [List.length_cons]
    cases h with
    | zero => rw [VExpr.cvar_lift]; exact .zero
    | succ h => rw [VExpr.cvar_lift]; exact (ih h).succ

theorem cvarCtx_split (c : Name) (G : Nat) (L : List (List VLevel)) (base : List VExpr) :
    ∀ Δ : List VExpr, ∃ Δ', Δ'.length = Δ.length ∧ cvarCtx c G L base Δ = Δ' ++ base
  | [] => ⟨[], rfl, rfl⟩
  | Y :: Δ => by
    obtain ⟨Δ', h1, h2⟩ := cvarCtx_split c G L base Δ
    exact ⟨VExpr.cvar c G L Y Δ.length :: Δ', by simp [h1], by simp [cvarCtx, h2]⟩

/-- The new context entries: one per level list, each a closed instance of the axiom's
type. -/
def cvarTs (ci : VConstant) (L : List (List VLevel)) : List VExpr :=
  L.map fun ls => ci.type.instL ls

theorem VEnv.addConst_spec {env env' : VEnv} {c : Name} {ci : VConstant}
    (h : env.addConst c ci = some env') :
    env.constants c = none ∧ env'.defeqs = env.defeqs ∧
      ∀ n, env'.constants n = if c = n then some ci else env.constants n := by
  unfold VEnv.addConst at h; split at h
  · cases h
  · cases h; exact ⟨‹_›, rfl, fun _ => rfl⟩

/-! ## 4. The transport

The conclusion is quantified over **every** `L'` that covers the level lists the derivation
actually used, and every term in it is computed at that `L'`.  That is what makes `trans`
free: both induction hypotheses are instantiated at the same `L'`, so their middle terms are
syntactically identical, and no stability or weakening lemma is needed anywhere. -/

open VEnv in
theorem cvarMain {env env' : VEnv} {c : Name} {ci : VConstant} {Γ : List VExpr} {U : Nat}
    (henv : Ordered env) (hadd : env.addConst c ci = some env')
    (huv : ci.uvars = U) (hciWF : ci.WF env) (hΓc : CtxConstsIn (· ≠ c) Γ) :
    ∀ {Δ e1 e2 A}, env'.IsDefEq U Δ e1 e2 A → ∀ Δ₀, Δ = Δ₀ ++ Γ →
      ∃ L₂, LWF U L₂ ∧ ∀ L', LWF U L' → LCov L' L₂ →
        env.IsDefEq U (cvarCtx c Γ.length L' (Γ ++ cvarTs ci L') Δ₀)
          (VExpr.cvar c Γ.length L' e1 Δ₀.length)
          (VExpr.cvar c Γ.length L' e2 Δ₀.length)
          (VExpr.cvar c Γ.length L' A Δ₀.length) := by
  obtain ⟨hnone, hdefeqs, hconsts⟩ := VEnv.addConst_spec hadd
  have hcfree : ∀ {e : VExpr}, e.ConstsIn env.contains → e.ConstsIn (· ≠ c) := by
    intro e h
    refine h.mono fun n hn => ?_
    rintro rfl
    obtain ⟨_, hx⟩ := hn
    rw [hnone] at hx; simp at hx
  have hty : env.IsType U [] ci.type := huv ▸ hciWF
  obtain ⟨uc, htyd⟩ := hty
  have hclosed : ci.type.ClosedN 0 := htyd.closedN henv trivial
  have hcity : ci.type.ConstsIn (· ≠ c) :=
    hcfree (VEnv.IsDefEq.constsIn henv.constsIn htyd trivial).1
  intro Δ e1 e2 A H
  induction H with
  | @bvar Γ' i A h =>
    rintro Δ₀ rfl
    exact ⟨[], LWF.nil, fun L' _ _ => .bvar (lookup_cvarCtx hΓc h)⟩
  | symm _ ih =>
    rintro Δ₀ rfl
    obtain ⟨L₂, hw, h⟩ := ih Δ₀ rfl
    exact ⟨L₂, hw, fun L' h1 h2 => (h L' h1 h2).symm⟩
  | trans _ _ ih1 ih2 =>
    rintro Δ₀ rfl
    obtain ⟨L1, hw1, h1⟩ := ih1 Δ₀ rfl
    obtain ⟨L2, hw2, h2⟩ := ih2 Δ₀ rfl
    exact ⟨L1 ++ L2, hw1.append hw2,
      fun L' hL hc => (h1 L' hL hc.left).trans (h2 L' hL hc.right)⟩
  | sortDF h1 h2 h3 =>
    rintro Δ₀ rfl
    exact ⟨[], LWF.nil, fun _ _ _ => .sortDF h1 h2 h3⟩
  | @constDF c' ci' ls ls' Γ' h1 h2 h3 h4 h5 =>
    rintro Δ₀ rfl
    by_cases hcc : c' = c
    · subst hcc
      have hci' : ci' = ci := by
        have hx := hconsts c'; rw [h1, if_pos rfl] at hx; exact (Option.some.inj hx)
      subst hci'
      refine ⟨[ls], LWF.one (huv ▸ h4) h2, fun L' hLwf hcov => ?_⟩
      obtain ⟨ls₀, hmem, heq₀⟩ := hcov ls (by simp)
      obtain ⟨L1, ls₁, L2, hLeq, hlen, heqv⟩ := lvlIdx_split ⟨ls₀, hmem, heq₀⟩
      obtain ⟨Δ', hΔ'len, hΔ'eq⟩ := cvarCtx_split c' Γ.length L' (Γ ++ cvarTs ci' L') Δ₀
      have hls₁wf : ∀ l ∈ ls₁, l.WF U :=
        (hLwf ls₁ (by rw [hLeq]; simp)).2
      -- the entry
      have hentry : Lookup (cvarCtx c' Γ.length L' (Γ ++ cvarTs ci' L') Δ₀)
          (Δ₀.length + Γ.length + lvlIdx L' ls) (ci'.type.instL ls₁) := by
        have hsplit : cvarTs ci' L' =
            cvarTs ci' L1 ++ (ci'.type.instL ls₁) :: cvarTs ci' L2 := by
          rw [hLeq]; simp [cvarTs]
        have : cvarCtx c' Γ.length L' (Γ ++ cvarTs ci' L') Δ₀ =
            (Δ' ++ Γ ++ cvarTs ci' L1) ++ (ci'.type.instL ls₁) :: cvarTs ci' L2 := by
          rw [hΔ'eq, hsplit]; simp
        rw [this]
        have hlen2 : (Δ' ++ Γ ++ cvarTs ci' L1).length
            = Δ₀.length + Γ.length + lvlIdx L' ls := by
          simp [hΔ'len, cvarTs, hlen]; omega
        rw [← hlen2]
        exact lookup_mid hclosed.instL _ _
      rw [VExpr.cvar_const_self, VExpr.cvar_const_self,
        VExpr.cvar_eq_self (VExpr.ConstsIn.instL.2 hcity), ← lvlIdx_congr h5 L']
      have hIL := VEnv.IsDefEq.instL_r henv (Γ := []) trivial hls₁wf h2 heqv htyd
      simp only [List.map_nil] at hIL
      exact .defeqDF (VEnv.IsDefEq.weak0 henv hIL) (.bvar hentry)
    · refine ⟨[], LWF.nil, fun L' _ _ => ?_⟩
      have h1' : env.constants c' = some ci' := by
        have hx := hconsts c'; rw [h1, if_neg (Ne.symm hcc)] at hx; exact hx.symm
      rw [VExpr.cvar_const_other hcc, VExpr.cvar_const_other hcc,
        VExpr.cvar_eq_self (VExpr.ConstsIn.instL.2 (hcfree (henv.constsInC h1')))]
      exact .constDF h1' h2 h3 h4 h5
  | appDF _ _ ih1 ih2 =>
    rintro Δ₀ rfl
    obtain ⟨L1, hw1, h1⟩ := ih1 Δ₀ rfl
    obtain ⟨L2, hw2, h2⟩ := ih2 Δ₀ rfl
    refine ⟨L1 ++ L2, hw1.append hw2, fun L' hL hc => ?_⟩
    have := VEnv.IsDefEq.appDF (h1 L' hL hc.left) (h2 L' hL hc.right)
    rwa [← VExpr.cvar_inst0] at this
  | @lamDF Γ' A A' u body body' B _ _ ih1 ih2 =>
    rintro Δ₀ rfl
    obtain ⟨L1, hw1, h1⟩ := ih1 Δ₀ rfl
    obtain ⟨L2, hw2, h2⟩ := ih2 (A :: Δ₀) rfl
    refine ⟨L1 ++ L2, hw1.append hw2, fun L' hL hc => ?_⟩
    have hb := h2 L' hL hc.right
    simp only [cvarCtx, List.length_cons] at hb
    exact .lamDF (h1 L' hL hc.left) hb
  | @forallEDF Γ' A A' u body body' v _ _ ih1 ih2 =>
    rintro Δ₀ rfl
    obtain ⟨L1, hw1, h1⟩ := ih1 Δ₀ rfl
    obtain ⟨L2, hw2, h2⟩ := ih2 (A :: Δ₀) rfl
    refine ⟨L1 ++ L2, hw1.append hw2, fun L' hL hc => ?_⟩
    have hb := h2 L' hL hc.right
    simp only [cvarCtx, List.length_cons] at hb
    exact .forallEDF (h1 L' hL hc.left) hb
  | defeqDF _ _ ih1 ih2 =>
    rintro Δ₀ rfl
    obtain ⟨L1, hw1, h1⟩ := ih1 Δ₀ rfl
    obtain ⟨L2, hw2, h2⟩ := ih2 Δ₀ rfl
    exact ⟨L1 ++ L2, hw1.append hw2,
      fun L' hL hc => .defeqDF (h1 L' hL hc.left) (h2 L' hL hc.right)⟩
  | @beta A Γ' body B e' _ _ ih1 ih2 =>
    rintro Δ₀ rfl
    obtain ⟨L1, hw1, h1⟩ := ih1 (A :: Δ₀) rfl
    obtain ⟨L2, hw2, h2⟩ := ih2 Δ₀ rfl
    refine ⟨L1 ++ L2, hw1.append hw2, fun L' hL hc => ?_⟩
    have hb := h1 L' hL hc.left
    simp only [cvarCtx, List.length_cons] at hb
    have := VEnv.IsDefEq.beta hb (h2 L' hL hc.right)
    rwa [← VExpr.cvar_inst0, ← VExpr.cvar_inst0] at this
  | @eta Γ' e A B _ ih =>
    rintro Δ₀ rfl
    obtain ⟨L1, hw1, h1⟩ := ih Δ₀ rfl
    refine ⟨L1, hw1, fun L' hL hc => ?_⟩
    have := VEnv.IsDefEq.eta (h1 L' hL hc)
    rwa [← VExpr.cvar_lift] at this
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    rintro Δ₀ rfl
    obtain ⟨L1, hw1, h1⟩ := ih1 Δ₀ rfl
    obtain ⟨L2, hw2, h2⟩ := ih2 Δ₀ rfl
    obtain ⟨L3, hw3, h3⟩ := ih3 Δ₀ rfl
    refine ⟨L1 ++ (L2 ++ L3), hw1.append (hw2.append hw3), fun L' hL hc => ?_⟩
    exact .proofIrrel (h1 L' hL hc.left) (h2 L' hL hc.right.left) (h3 L' hL hc.right.right)
  | @extra df ls Γ' h1 h2 h3 =>
    rintro Δ₀ rfl
    refine ⟨[], LWF.nil, fun L' _ _ => ?_⟩
    have hdf : env.defeqs df := hdefeqs ▸ h1
    obtain ⟨hl, hr, ht⟩ := henv.constsInD hdf
    rw [VExpr.cvar_eq_self (VExpr.ConstsIn.instL.2 (hcfree hl)),
      VExpr.cvar_eq_self (VExpr.ConstsIn.instL.2 (hcfree hr)),
      VExpr.cvar_eq_self (VExpr.ConstsIn.instL.2 (hcfree ht))]
    exact .extra hdf h2 h3

/-! ## 5. Contexts extended at the bottom by closed types -/

namespace VEnv

theorem onCtx_closed_append {env : VEnv} {U : Nat} (henv : Ordered env) :
    ∀ {Ts : List VExpr}, (∀ T ∈ Ts, env.IsType U [] T) → OnCtx Ts (env.IsType U)
  | [], _ => trivial
  | T :: Ts, h => ⟨onCtx_closed_append henv fun x hx => h x (List.mem_cons_of_mem _ hx),
      let ⟨u, hu⟩ := h T (List.mem_cons_self ..); ⟨u, HasType.weak0 henv hu⟩⟩

theorem onCtx_append {env : VEnv} {U : Nat} (henv : Ordered env) {Ts : List VExpr}
    (hTs : ∀ T ∈ Ts, env.IsType U [] T) :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → OnCtx (Γ ++ Ts) (env.IsType U)
  | [], _ => onCtx_closed_append henv hTs
  | A :: Γ, ⟨h1, u, h2⟩ =>
    ⟨onCtx_append henv hTs h1, u, IsDefEq.weakR henv (CtxWF.closed henv h1) h2 Ts⟩

/-! ## 6. The residual with a well-formed context, and the equivalence

`AxiomConservativity` quantifies over an **arbitrary** context.  Every use of it has a
well-formed one — `Strengthening1Uninhab` carries `OnCtx Γ` — and the converse *needs* one,
because `StrengtheningTarget`'s only hypothesis is `OnCtx Γ'` and `Γ ++ Ts` cannot be well
formed unless `Γ` is.  So the residual is sharpened here by adding that hypothesis (a
*weaker* obligation, working rule 3's safe direction), in a **separate** definition rather
than by editing the original. -/

/-- **The residual, sharpened**: conservativity of adding one axiom, over a well-formed
context. -/
def AxiomConservativityWF (env : VEnv) (U : Nat) : Prop :=
  ∀ {c : Name} {ci : VConstant} {env' : VEnv} {Γ : List VExpr} {e1 e2 : VExpr},
    env.addConst c ci = some env' → ci.WF env → ci.uvars = U →
    OnCtx Γ (env.IsType U) →
    CtxConstsIn env.contains Γ → e1.ConstsIn env.contains → e2.ConstsIn env.contains →
    env'.IsDefEqU U Γ e1 e2 → env.IsDefEqU U Γ e1 e2

/-- The same with the axiom's type additionally assumed to have no inhabitant. -/
def AxiomConservativityUninhabWF (env : VEnv) (U : Nat) : Prop :=
  ∀ {c : Name} {ci : VConstant} {env' : VEnv} {Γ : List VExpr} {e1 e2 : VExpr},
    env.addConst c ci = some env' → ci.WF env → ci.uvars = U →
    (∀ t, ¬ env.HasType U [] t ci.type) →
    OnCtx Γ (env.IsType U) →
    CtxConstsIn env.contains Γ → e1.ConstsIn env.contains → e2.ConstsIn env.contains →
    env'.IsDefEqU U Γ e1 e2 → env.IsDefEqU U Γ e1 e2

theorem AxiomConservativity.wf (H : AxiomConservativity env U) : AxiomConservativityWF env U :=
  fun h1 h2 h3 _ h5 h6 h7 h8 => H h1 h2 h3 h5 h6 h7 h8

theorem AxiomConservativityWF.uninhab (H : AxiomConservativityWF env U) :
    AxiomConservativityUninhabWF env U :=
  fun h1 h2 h3 _ h5 h6 h7 h8 h9 => H h1 h2 h3 h5 h6 h7 h8 h9

theorem AxiomConservativityUninhab.wf (H : AxiomConservativityUninhab env U) :
    AxiomConservativityUninhabWF env U :=
  fun h1 h2 h3 h4 _ h6 h7 h8 h9 => H h1 h2 h3 h4 h6 h7 h8 h9

variable! (henv : Ordered env) in
/-- `StrengthenAxiom.lean`'s route 1, run from the sharpened residual: the `OnCtx Γ` the
sharpened residual asks for is exactly the one `Strengthening1Uninhab` already carries. -/
theorem AxiomConservativityUninhabWF.strengthening1Uninhab
    (H : AxiomConservativityUninhabWF env U) : Strengthening1Uninhab env U := by
  intro k Γ Γ' e1 e2 W hΓ hΓ' hemp h
  obtain ⟨Γ₀, A₀, hI, hΓ₀, hA₀⟩ := W.exists_instN_typed hΓ'
  have hC : env.IsType U [] (mkForallCtx Γ₀ A₀) := isType_mkForallCtx hΓ₀ hA₀
  have hCemp : ∀ t, ¬ env.HasType U [] t (mkForallCtx Γ₀ A₀) :=
    fun t ht => hemp Γ₀ A₀ _ (hI _) (hasType_appCtx henv ht)
  obtain ⟨c, env', hadd⟩ := henv.exists_addConst ⟨U, mkForallCtx Γ₀ A₀⟩
  have hle : env ≤ env' := VEnv.addConst_le hadd
  have henv' : Ordered env' := .const (ci := ⟨U, mkForallCtx Γ₀ A₀⟩) henv hC hadd
  have hcty : env'.constants c = some ⟨U, mkForallCtx Γ₀ A₀⟩ := by
    rw [VEnv.addConst_constants_eq hadd]; simp
  have hlwf : (mkForallCtx Γ₀ A₀).LevelWF U := by
    obtain ⟨_, hC⟩ := hC; exact (IsDefEq.levelWF hC trivial).1
  have hconst : env'.HasType U [] (.const c (VLevel.params U)) (mkForallCtx Γ₀ A₀) := by
    have h := VEnv.IsDefEq.constDF (Γ := []) (uvars := U) (ls := VLevel.params U)
      (ls' := VLevel.params U) hcty VLevel.params_wf VLevel.params_wf
      (by simp) (List.Forall₂.rfl fun _ _ => rfl)
    rw [show (VConstant.mk U (mkForallCtx Γ₀ A₀)).type = mkForallCtx Γ₀ A₀ from rfl,
      hlwf.instL_id] at h
    exact h
  have h₀ := hasType_appCtx (t := .const c (VLevel.params U)) henv' hconst
  obtain ⟨A, hh⟩ := h
  have hΓc : CtxConstsIn env.contains Γ := ctxConstsIn_of_onCtx henv hΓ
  have hcs := hh.constsIn henv.constsIn (ctxConstsIn_of_onCtx henv hΓ')
  exact H hadd hC rfl hCemp hΓ hΓc (VExpr.ConstsIn.liftN.1 hcs.1)
    (VExpr.ConstsIn.liftN.1 hcs.2.1)
    (IsDefEqU.strengthen_of_instN henv' (hI _) h₀ ⟨_, hh.mono hle⟩)

variable! (henv : VEnv.WF env) in
theorem AxiomConservativityUninhabWF.target (H : AxiomConservativityUninhabWF env U) :
    StrengtheningTarget env U :=
  Strengthening1.target henv
    (Strengthening1Uninhab.strengthening1 henv.ordered (H.strengthening1Uninhab henv.ordered))

/-! ## 7. The converse: the target implies the residual -/

variable! (henv : Ordered env) in
/-- **The `const`-to-variable transport, assembled.**  Given the strengthening target, an
axiom added to `env` is conservative: translate every occurrence of the new constant into a
context variable, one per `≈`-class of level list the derivation uses, and strip those
variables again with the target. -/
theorem StrengtheningTarget.axiomConservativityWF (H : StrengtheningTarget env U) :
    AxiomConservativityWF env U := by
  intro c ci env' Γ e1 e2 hadd hci huv hΓ hΓc he1 he2 h
  have hnone := (VEnv.addConst_spec hadd).1
  have hcfree : ∀ {e : VExpr}, e.ConstsIn env.contains → e.ConstsIn (· ≠ c) := by
    intro e he
    refine he.mono fun n hn => ?_
    rintro rfl
    obtain ⟨_, hx⟩ := hn
    rw [hnone] at hx; simp at hx
  have hciU : env.IsType U [] ci.type := huv ▸ hci
  obtain ⟨A, hd⟩ := h
  obtain ⟨L₂, hLwf, hres⟩ :=
    cvarMain henv hadd huv hci (OnCtx.mono (fun hh => hcfree hh) hΓc) hd [] rfl
  have hmain := hres L₂ hLwf (fun ls hm => ⟨ls, hm, LEqv.refl ls⟩)
  simp only [cvarCtx, List.length_nil, List.nil_append] at hmain
  rw [VExpr.cvar_eq_self (hcfree he1), VExpr.cvar_eq_self (hcfree he2)] at hmain
  have hTsty : ∀ T ∈ cvarTs ci L₂, env.IsType U [] T := by
    intro T hT
    obtain ⟨ls, hls, rfl⟩ := List.mem_map.1 hT
    have := VEnv.IsType.instL (ls := ls) (U' := U) (hLwf ls hls).2 hciU
    simpa using this
  have hΓ' : OnCtx (Γ ++ cvarTs ci L₂) (env.IsType U) := onCtx_append henv hTsty hΓ
  have hΓcl : CtxClosed Γ := CtxWF.closed henv hΓ
  have henv' : Ordered env' := Ordered.const henv hci hadd
  have hcl1 : e1.ClosedN Γ.length := IsDefEq.closedN henv' hd hΓcl
  have hcl2 : e2.ClosedN Γ.length := IsDefEq.closedN henv' hd.symm hΓcl
  refine H (Ctx.LiftN.right hΓcl (cvarTs ci L₂)) hΓ' ?_
  rw [hcl1.liftN_eq (Nat.le_refl _), hcl2.liftN_eq (Nat.le_refl _)]
  exact ⟨_, hmain⟩

variable! (henv : VEnv.WF env) in
/-- **The equivalence.**  The residual of `StrengthenAxiom.lean`'s route 1 — over a
well-formed context — is not merely sufficient for the strengthening target: it is the
*same statement*. -/
theorem axiomConservativityWF_iff_target :
    AxiomConservativityWF env U ↔ StrengtheningTarget env U :=
  ⟨fun H => AxiomConservativityUninhabWF.target henv (AxiomConservativityWF.uninhab H),
   fun H => StrengtheningTarget.axiomConservativityWF henv.ordered H⟩

variable! (henv : VEnv.WF env) in
/-- The same for the **uninhabited** sharpening, which sits between the two. -/
theorem axiomConservativityUninhabWF_iff_target :
    AxiomConservativityUninhabWF env U ↔ StrengtheningTarget env U :=
  ⟨fun H => AxiomConservativityUninhabWF.target henv H,
   fun H => AxiomConservativityWF.uninhab (StrengtheningTarget.axiomConservativityWF henv.ordered H)⟩

variable! (henv : VEnv.WF env) in
/-- **Restricting the residual to uninhabited axioms loses nothing.**  `Strengthen.lean` §12
confines the target to uninhabited entries and `StrengthenAxiom.lean` transports that to the
Π-closure; this says the sharpening was not merely sound but *lossless*. -/
theorem axiomConservativityWF_iff_uninhabWF :
    AxiomConservativityWF env U ↔ AxiomConservativityUninhabWF env U :=
  (axiomConservativityWF_iff_target henv).trans
    (axiomConservativityUninhabWF_iff_target henv).symm

/-! ## 8. Non-vacuity, and the collapse test

**The equivalence is not a repackaging.**  The forward direction is `StrengthenAxiom.lean`'s
route 1 (Π-close the stripped entry, declare it, apply it back); the backward direction is
this file's translation.  `VEnv.addConst_ne` (`StrengthenAxiom.lean` §6) shows the two
environments are always distinct, so the residual's premise cannot degenerate into the
target's; that collapse test is unchanged by the added `OnCtx Γ` hypothesis, which only
*weakens* the residual.

**The context extension does real work.**  The one way this transport could be a tautology is
if the list `L₂` it produces were always empty, so that the `Ctx.LiftN` handed to
`StrengtheningTarget` were the identity.  `cvarMain_needs_entries` rules that out with a
lemma rather than an example: at `L' = []` the translation of a `c`-headed term is
`.bvar Γ.length`, which `IsDefEq.closedN` shows can never be typed in `Γ` itself.

**The residual's premises are satisfiable.**  `AxiomConservativityWF` adds `OnCtx Γ` to
`AxiomConservativity`, and `StrengthenAxiom.axiomConservativity_fires` fires the latter at
`Γ = []`, where `OnCtx` is trivial; so that witness — two `c`-free endpoints joined by a
`trans` through a middle term that is *not* `c`-free — witnesses this one too. -/

/-- **Non-vacuity, backed by a lemma.**  If the derivation uses the new constant, the
transport's context extension cannot be dropped: with no entries at all the translation of
`.const c ls` is the variable one past the end of `Γ`, and nothing is typed at it. -/
theorem cvarMain_needs_entries {env : VEnv} {U : Nat} {Γ : List VExpr} {c : Name}
    {ls : List VLevel} {e2 A : VExpr} (henv : Ordered env) (hΓ : CtxClosed Γ) :
    ¬ env.IsDefEq U Γ (VExpr.cvar c Γ.length [] (.const c ls) 0) e2 A := by
  intro h
  have hcl := IsDefEq.closedN henv h hΓ
  rw [VExpr.cvar_const_self] at hcl
  simp [lvlIdx, VExpr.ClosedN] at hcl

/-- **The axiom *scheme* really is handled by distinct entries.**  This is the check that
would falsify the whole construction: if `lvlIdx` identified `≈`-inequivalent level lists,
one entry would be made to serve two different types.  It does not — `Sort 0` and `Sort 1`
get entries `0` and `1`. -/
theorem lvlIdx_distinguishes :
    ¬ LEqv [VLevel.zero] [VLevel.succ VLevel.zero] ∧
    lvlIdx [[VLevel.zero], [VLevel.succ VLevel.zero]] [VLevel.zero] = 0 ∧
    lvlIdx [[VLevel.zero], [VLevel.succ VLevel.zero]] [VLevel.succ VLevel.zero] = 1 := by
  have hne : ¬ LEqv [VLevel.zero] [VLevel.succ VLevel.zero] := by
    rintro (_ | ⟨h, _⟩)
    have := congrFun (VLevel.equiv_def'.1 h) []
    simp [VLevel.eval] at this
  refine ⟨hne, ?_, ?_⟩
  · simp only [lvlIdx, if_pos (LEqv.refl [VLevel.zero])]
  · rw [lvlIdx, if_neg (fun h => hne (h.trans (LEqv.refl _))),
      lvlIdx, if_pos (LEqv.refl [VLevel.succ VLevel.zero])]

/-- The transport's `Ctx.LiftN` at a one-entry extension is a genuine one-step weakening: the
target is applied at `n = 1`, not at `n = 0`. -/
theorem cvarTs_liftN_fires {env : VEnv} {U : Nat} {Γ : List VExpr} {ci : VConstant}
    {ls : List VLevel} (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) :
    (cvarTs ci [ls]).length = 1 ∧
      Ctx.LiftN 1 Γ.length Γ (Γ ++ cvarTs ci [ls]) := by
  refine ⟨rfl, ?_⟩
  have := Ctx.LiftN.right (CtxWF.closed henv hΓ) (cvarTs ci [ls])
  simpa [cvarTs] using this

end VEnv

end Lean4Lean
