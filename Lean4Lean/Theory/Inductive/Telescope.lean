import Lean4Lean.Theory.VExpr

/-!
# Telescopes of `VExpr`

A *telescope* is a `List VExpr` of binder types written in **declaration order**
(outermost binder first): in `As = [A₁, …, Aₙ]` the type `Aᵢ` lives in the context
`(As.take (i-1)).reverse ++ Γ₀`. The corresponding *context* (innermost-first, as used by
`Lookup`/`OnCtx`) is `As.reverse ++ Γ₀`.

This file is the pure de Bruijn arithmetic underlying the specification of inductive types
(`Lean4Lean/Theory/Inductive.lean`): the constructors `mkPi`/`mkLams`/`mkApp`, the
"variables of a telescope" spine `bvars`, the telescope re-indexing operations
`liftTele`/`instTele`/`shift`/`shiftTele`, and the iterated instantiation `instAll` which
is the β-normal form of a saturated `mkLams`-application.

Everything here is `VExpr`-level; nothing about typing or environments appears.
-/

namespace Lean4Lean
namespace VExpr

/-! ## Definitions -/

/-- `mkPi [A₁,…,Aₙ] B = ∀ A₁ … Aₙ, B`. `Aᵢ` lives in context `(As.take (i-1)).reverse ++ Γ₀`,
`B` in `As.reverse ++ Γ₀`. -/
def mkPi : List VExpr → VExpr → VExpr
  | [], B => B
  | A :: As, B => .forallE A (mkPi As B)

/-- `mkLams [A₁,…,Aₙ] b = fun A₁ … Aₙ => b`. -/
def mkLams : List VExpr → VExpr → VExpr
  | [], b => b
  | A :: As, b => .lam A (mkLams As b)

/-- `f.mkApp [a₁,…,aₙ] = f a₁ … aₙ`. -/
def mkApp (f : VExpr) : List VExpr → VExpr
  | [] => f
  | a :: as => (VExpr.app f a).mkApp as

/-- The arguments that apply a function to a telescope of length `n` whose innermost binder
is at de Bruijn index `lo`: `[.bvar (lo+n-1), …, .bvar lo]` (declaration order). -/
def bvars (lo : Nat) : Nat → List VExpr
  | 0 => []
  | n+1 => .bvar (lo + n) :: bvars lo n

/-- Re-index a declaration-order telescope living over `Γ₀` so that it lives over `Ξ ++ Γ₀`
with `|Ξ| = n`, inserted `k` binders in. `liftTele n As k` lifts the `i`-th entry at `k+i`. -/
def liftTele (n : Nat) : List VExpr → (k :_:= 0) → List VExpr
  | [], _ => []
  | A :: As, k => A.liftN n k :: liftTele n As (k+1)

/-- Instantiate the variable `k+i` of the `i`-th entry of a declaration-order telescope. -/
def instTele (a : VExpr) : List VExpr → (k :_:= 0) → List VExpr
  | [], _ => []
  | A :: As, k => A.inst a k :: instTele a As (k+1)

/-- The composite re-indexing used throughout the inductive construction: a term over
`(fields<i).reverse ++ P.reverse` into a context where `off` binders were inserted between
the fields and `P`, and `d` binders below the fields; `j` is the number of binders *inside*
the term's own scope. -/
def shift (off d i : Nat) (e : VExpr) (j := 0) : VExpr :=
  (e.liftN off (i + j)).liftN d j

/-- `shift` applied entrywise to a declaration-order telescope. -/
def shiftTele (off d i : Nat) : List VExpr → (j :_:= 0) → List VExpr
  | [], _ => []
  | A :: As, j => shift off d i A j :: shiftTele off d i As (j+1)

/-- `instAll e [a₁,…,aₙ] k = ((e.inst a₁ (k+n-1)).inst a₂ (k+n-2)) … .inst aₙ k`.

This is the β-normal form of `(mkLams As b).mkApp as` (with `|as| = |As| = n`) at
`e := b`: see `inst_mkLams` and `instAll_cons`. -/
def instAll : VExpr → List VExpr → (k :_:= 0) → VExpr
  | e, [], _ => e
  | e, a :: as, k => instAll (e.inst a (k + as.length)) as k

/-- `instAll` applied entrywise to a declaration-order telescope. -/
def instAllTele : List VExpr → List VExpr → (k :_:= 0) → List VExpr
  | [], _, _ => []
  | A :: As, as, k => instAll A as k :: instAllTele As as (k+1)

/-- `ClosedN` for a declaration-order telescope: the `i`-th entry is closed at `k+i`.
`ClosedTele As k ↔ ClosedN (mkPi As B) k` modulo the body, see `closedN_mkPi`. -/
def ClosedTele : List VExpr → (k :_:= 0) → Prop
  | [], _ => True
  | A :: As, k => A.ClosedN k ∧ ClosedTele As (k+1)

/-- The number of arguments in an application spine (`Lean.Expr.getAppNumArgs`). -/
def appArity : VExpr → Nat
  | .app f _ => f.appArity + 1
  | _ => 0

/-- The number of leading `forallE` binders. -/
def piArity : VExpr → Nat
  | .forallE _ B => B.piArity + 1
  | _ => 0

/-- The number of leading `lam` binders. -/
def lamArity : VExpr → Nat
  | .lam _ b => b.lamArity + 1
  | _ => 0

/-! ## Defining equations -/

@[simp] theorem mkPi_nil : mkPi [] B = B := rfl
@[simp] theorem mkPi_cons : mkPi (A :: As) B = .forallE A (mkPi As B) := rfl
@[simp] theorem mkLams_nil : mkLams [] b = b := rfl
@[simp] theorem mkLams_cons : mkLams (A :: As) b = .lam A (mkLams As b) := rfl
@[simp] theorem mkApp_nil : mkApp f [] = f := rfl
@[simp] theorem mkApp_cons : mkApp f (a :: as) = mkApp (.app f a) as := rfl

@[simp] theorem bvars_zero : bvars lo 0 = [] := rfl
@[simp] theorem bvars_succ : bvars lo (n+1) = .bvar (lo + n) :: bvars lo n := rfl

@[simp] theorem liftTele_nil : liftTele n [] k = [] := rfl
@[simp] theorem liftTele_cons :
    liftTele n (A :: As) k = A.liftN n k :: liftTele n As (k+1) := rfl

@[simp] theorem instTele_nil : instTele a [] k = [] := rfl
@[simp] theorem instTele_cons :
    instTele a (A :: As) k = A.inst a k :: instTele a As (k+1) := rfl

theorem shift_def : shift off d i e j = (e.liftN off (i + j)).liftN d j := rfl

@[simp] theorem shiftTele_nil : shiftTele off d i [] j = [] := rfl
@[simp] theorem shiftTele_cons :
    shiftTele off d i (A :: As) j = shift off d i A j :: shiftTele off d i As (j+1) := rfl

@[simp] theorem instAll_nil : instAll e [] k = e := rfl
@[simp] theorem instAll_cons :
    instAll e (a :: as) k = instAll (e.inst a (k + as.length)) as k := rfl

@[simp] theorem instAllTele_nil : instAllTele [] as k = [] := rfl
@[simp] theorem instAllTele_cons :
    instAllTele (A :: As) as k = instAll A as k :: instAllTele As as (k+1) := rfl

@[simp] theorem closedTele_nil : ClosedTele [] k := trivial
@[simp] theorem closedTele_cons :
    ClosedTele (A :: As) k ↔ A.ClosedN k ∧ ClosedTele As (k+1) := Iff.rfl

/-! ## Lengths, append and arity -/

@[simp] theorem length_bvars : (bvars lo n).length = n := by induction n <;> simp [*]
@[simp] theorem length_liftTele : (liftTele n As k).length = As.length := by
  induction As generalizing k <;> simp [*]
@[simp] theorem length_instTele : (instTele a As k).length = As.length := by
  induction As generalizing k <;> simp [*]
@[simp] theorem length_shiftTele : (shiftTele off d i As j).length = As.length := by
  induction As generalizing j <;> simp [*]
@[simp] theorem length_instAllTele : (instAllTele As as k).length = As.length := by
  induction As generalizing k <;> simp [*]

@[simp] theorem mkPi_append : mkPi (As ++ Bs) C = mkPi As (mkPi Bs C) := by
  induction As <;> simp [*]

@[simp] theorem mkLams_append : mkLams (As ++ Bs) c = mkLams As (mkLams Bs c) := by
  induction As <;> simp [*]

theorem mkApp_append : mkApp f (as ++ bs) = mkApp (mkApp f as) bs := by
  induction as generalizing f <;> simp [*]

theorem mkApp_concat : mkApp f (as ++ [a]) = .app (mkApp f as) a := by
  rw [mkApp_append]; rfl

theorem liftTele_append :
    liftTele n (As ++ Bs) k = liftTele n As k ++ liftTele n Bs (k + As.length) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [List.cons_append, liftTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

theorem instTele_append :
    instTele a (As ++ Bs) k = instTele a As k ++ instTele a Bs (k + As.length) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [List.cons_append, instTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

theorem shiftTele_append :
    shiftTele off d i (As ++ Bs) j
      = shiftTele off d i As j ++ shiftTele off d i Bs (j + As.length) := by
  induction As generalizing j with
  | nil => simp
  | cons A As ih =>
    simp only [List.cons_append, shiftTele_cons, ih, List.length_cons,
      show j + 1 + As.length = j + (As.length + 1) from by omega]

theorem instAllTele_append :
    instAllTele (As ++ Bs) as k = instAllTele As as k ++ instAllTele Bs as (k + As.length) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [List.cons_append, instAllTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

@[simp] theorem appArity_mkApp : appArity (mkApp f as) = f.appArity + as.length := by
  induction as generalizing f with
  | nil => simp
  | cons a as ih => simp [ih, appArity]; omega

@[simp] theorem piArity_mkPi : piArity (mkPi As B) = As.length + B.piArity := by
  induction As with
  | nil => simp
  | cons A As ih => simp [ih, piArity]; omega

@[simp] theorem lamArity_mkLams : lamArity (mkLams As b) = As.length + b.lamArity := by
  induction As with
  | nil => simp
  | cons A As ih => simp [ih, lamArity]; omega

/-! ## Injectivity and inversion -/

theorem mkApp_inj (hlen : as.length = bs.length) (h : mkApp f as = mkApp g bs) :
    f = g ∧ as = bs := by
  induction as generalizing bs f g with
  | nil => cases bs with
    | nil => exact ⟨h, rfl⟩
    | cons => simp at hlen
  | cons a as ih => cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨h1, h2⟩ := ih hlen h
      injection h1 with h3 h4
      exact ⟨h3, by rw [h4, h2]⟩

/-- Two spines with non-application heads are equal only if head and arguments agree. -/
theorem mkApp_inj_of_arity (hf : f.appArity = 0) (hg : g.appArity = 0)
    (h : mkApp f as = mkApp g bs) : f = g ∧ as = bs := by
  have hlen := congrArg appArity h
  simp [hf, hg] at hlen
  exact mkApp_inj hlen h

theorem mkPi_inj (hlen : As.length = As'.length) (h : mkPi As B = mkPi As' B') :
    As = As' ∧ B = B' := by
  induction As generalizing As' with
  | nil => cases As' with
    | nil => exact ⟨rfl, h⟩
    | cons => simp at hlen
  | cons A As ih => cases As' with
    | nil => simp at hlen
    | cons A' As' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [mkPi_cons] at h
      injection h with h1 h2
      obtain ⟨h3, h4⟩ := ih hlen h2
      exact ⟨by rw [h1, h3], h4⟩

/-- Two pi-telescopes with non-pi bodies are equal only if telescope and body agree. -/
theorem mkPi_inj_of_arity (hB : B.piArity = 0) (hB' : B'.piArity = 0)
    (h : mkPi As B = mkPi As' B') : As = As' ∧ B = B' := by
  have hlen := congrArg piArity h
  simp [hB, hB'] at hlen
  exact mkPi_inj hlen h

theorem mkLams_inj (hlen : As.length = As'.length) (h : mkLams As b = mkLams As' b') :
    As = As' ∧ b = b' := by
  induction As generalizing As' with
  | nil => cases As' with
    | nil => exact ⟨rfl, h⟩
    | cons => simp at hlen
  | cons A As ih => cases As' with
    | nil => simp at hlen
    | cons A' As' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [mkLams_cons] at h
      injection h with h1 h2
      obtain ⟨h3, h4⟩ := ih hlen h2
      exact ⟨by rw [h1, h3], h4⟩

theorem mkLams_inj_of_arity (hb : b.lamArity = 0) (hb' : b'.lamArity = 0)
    (h : mkLams As b = mkLams As' b') : As = As' ∧ b = b' := by
  have hlen := congrArg lamArity h
  simp [hb, hb'] at hlen
  exact mkLams_inj hlen h

@[simp] theorem mkPi_eq_self_iff : mkPi As B = B ↔ As = [] := by
  refine ⟨fun h => ?_, fun h => by rw [h, mkPi_nil]⟩
  have h1 := congrArg piArity h
  cases As with
  | nil => rfl
  | cons A As => simp only [piArity_mkPi, List.length_cons] at h1; omega

@[simp] theorem mkLams_eq_self_iff : mkLams As b = b ↔ As = [] := by
  refine ⟨fun h => ?_, fun h => by rw [h, mkLams_nil]⟩
  have h1 := congrArg lamArity h
  cases As with
  | nil => rfl
  | cons A As => simp only [lamArity_mkLams, List.length_cons] at h1; omega

@[simp] theorem mkApp_eq_self_iff : mkApp f as = f ↔ as = [] := by
  refine ⟨fun h => ?_, fun h => by rw [h, mkApp_nil]⟩
  have h1 := congrArg appArity h
  cases as with
  | nil => rfl
  | cons a as => simp only [appArity_mkApp, List.length_cons] at h1; omega

/-! ## `bvars` -/

theorem bvars_add (m : Nat) : bvars lo (m + n) = bvars (lo + n) m ++ bvars lo n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : m + 1 + n = (m + n) + 1 := by omega
    rw [e1, bvars_succ, ih, bvars_succ, List.cons_append]
    congr 2
    omega

/-- The three-block split used pervasively by the recursor construction: a spine
`params ++ motives ++ minors` sitting immediately above `lo`. -/
theorem bvars_add₃ (m1 m2 m3 : Nat) :
    bvars lo (m1 + m2 + m3)
      = bvars (lo + m2 + m3) m1 ++ bvars (lo + m3) m2 ++ bvars lo m3 := by
  rw [bvars_add, bvars_add, Nat.add_right_comm lo m2 m3]

theorem getElem?_bvars (lo n i : Nat) :
    (bvars lo n)[i]? = if i < n then some (.bvar (lo + n - 1 - i)) else none := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [bvars_succ, List.getElem?_cons_succ, ih]
      simp only [Nat.add_lt_add_iff_right]
      split <;> [skip; rfl]
      congr 2
      omega

theorem bvars_eq_map_range (lo n : Nat) :
    bvars lo n = (List.range n).map fun i => .bvar (lo + n - 1 - i) := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_bvars, List.getElem?_map]
  split
  · rw [List.getElem?_range ‹_›]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem mem_bvars : e ∈ bvars lo n ↔ ∃ i, i < n ∧ e = .bvar (lo + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [bvars_succ, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self _, rfl⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i n with h | h
      · exact .inr ⟨i, h, rfl⟩
      · have : i = n := by omega
        exact .inl (by rw [this])

/-- Lifting at a cut below the telescope shifts all of its variables. -/
theorem map_liftN_bvars_lo (h : k ≤ lo) :
    (bvars lo n).map (liftN m · k) = bvars (m + lo) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bvars_succ, List.map_cons, ih, bvars_succ]
    simp only [liftN, liftVar_le (Nat.le_trans h (Nat.le_add_right ..))]
    congr 2
    omega

/-- Lifting at a cut above the telescope leaves it alone. -/
theorem map_liftN_bvars_hi (h : lo + n ≤ k) :
    (bvars lo n).map (liftN m · k) = bvars lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bvars_succ, List.map_cons, ih (by omega)]
    simp only [liftN, liftVar_lt (show lo + n < k by omega)]

/-- Instantiating below the telescope shifts all of its variables down by one. -/
theorem map_inst_bvars_lo (h : k ≤ lo) :
    (bvars (lo+1) n).map (·.inst a k) = bvars lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bvars_succ, List.map_cons, ih, bvars_succ]
    simp only [inst, instVar, if_neg (show ¬ (lo + 1 + n < k) by omega),
      if_neg (show ¬ (lo + 1 + n = k) by omega)]
    congr 2
    omega

/-- Instantiating above the telescope leaves it alone. -/
theorem map_inst_bvars_hi (h : lo + n ≤ k) :
    (bvars lo n).map (·.inst a k) = bvars lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bvars_succ, List.map_cons, ih (by omega)]
    simp only [inst, instVar, if_pos (show lo + n < k by omega)]

@[simp] theorem map_instL_bvars : (bvars lo n).map (instL ls) = bvars lo n := by
  induction n <;> simp [instL, *]

theorem closedN_bvars (h : lo + n ≤ k) : ∀ e ∈ bvars lo n, ClosedN e k := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := mem_bvars.1 he
  exact show lo + i < k by omega

theorem levelWF_bvars : ∀ e ∈ bvars lo n, LevelWF U e := by
  intro e he
  obtain ⟨_, _, rfl⟩ := mem_bvars.1 he
  trivial

/-! ## `liftN` -/

theorem liftN_mkPi :
    liftN n (mkPi As B) k = mkPi (liftTele n As k) (liftN n B (k + As.length)) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [mkPi_cons, liftN, liftTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

theorem liftN_mkLams :
    liftN n (mkLams As b) k = mkLams (liftTele n As k) (liftN n b (k + As.length)) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [mkLams_cons, liftN, liftTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

theorem liftN_mkApp :
    liftN n (mkApp f as) k = mkApp (liftN n f k) (as.map (liftN n · k)) := by
  induction as generalizing f <;> simp [liftN, *]

theorem liftN_mkApp_bvars_lo (h : k ≤ lo) :
    liftN n (mkApp f (bvars lo m)) k = mkApp (liftN n f k) (bvars (n + lo) m) := by
  rw [liftN_mkApp, map_liftN_bvars_lo h]

theorem liftN_mkApp_bvars_hi (h : lo + m ≤ k) :
    liftN n (mkApp f (bvars lo m)) k = mkApp (liftN n f k) (bvars lo m) := by
  rw [liftN_mkApp, map_liftN_bvars_hi h]

@[simp] theorem liftTele_zero : liftTele 0 As k = As := by
  induction As generalizing k <;> simp [*]

theorem liftTele_liftTele (h1 : k1 ≤ k2) (h2 : k2 ≤ n1 + k1) :
    liftTele n2 (liftTele n1 As k1) k2 = liftTele (n1+n2) As k1 := by
  induction As generalizing k1 k2 with
  | nil => rfl
  | cons A As ih =>
    rw [liftTele_cons, liftTele_cons, liftTele_cons,
      liftN'_liftN' h1 h2, ih (Nat.succ_le_succ h1) (by omega)]

theorem liftTele_succ (As : List VExpr) (n k : Nat) :
    liftTele (n+1) As k = liftTele 1 (liftTele n As k) k := by
  rw [liftTele_liftTele (Nat.le_refl _) (Nat.le_add_left ..)]

theorem liftTele_comm (h : k2 ≤ k1) :
    liftTele n2 (liftTele n1 As k1) k2 = liftTele n1 (liftTele n2 As k2) (n2 + k1) := by
  induction As generalizing k1 k2 with
  | nil => rfl
  | cons A As ih =>
    rw [liftTele_cons, liftTele_cons, liftTele_cons, liftTele_cons,
      liftN'_comm _ _ _ _ _ h, ih (Nat.succ_le_succ h), Nat.add_assoc]

/-- Instantiating a freshly-inserted binder undoes the corresponding lift. -/
theorem instTele_liftTele : instTele a (liftTele 1 As k) k = As := by
  induction As generalizing k with
  | nil => rfl
  | cons A As ih => rw [liftTele_cons, instTele_cons, inst_liftN, ih]

theorem instTele_liftTele' : instTele a (liftTele (n+1) As k) k = liftTele n As k := by
  induction As generalizing k with
  | nil => rfl
  | cons A As ih => rw [liftTele_cons, instTele_cons, inst_liftN', ih, liftTele_cons]

/-! ### Entrywise access -/

theorem getElem?_liftTele (i : Nat) :
    (liftTele n As k)[i]? = (As[i]?).map (liftN n · (k + i)) := by
  induction As generalizing k i with
  | nil => simp
  | cons A As ih =>
    cases i with
    | zero => simp
    | succ i => rw [liftTele_cons, List.getElem?_cons_succ, ih, List.getElem?_cons_succ,
                  show k + 1 + i = k + (i+1) from by omega]

theorem getElem?_instTele (i : Nat) :
    (instTele a As k)[i]? = (As[i]?).map (·.inst a (k + i)) := by
  induction As generalizing k i with
  | nil => simp
  | cons A As ih =>
    cases i with
    | zero => simp
    | succ i => rw [instTele_cons, List.getElem?_cons_succ, ih, List.getElem?_cons_succ,
                  show k + 1 + i = k + (i+1) from by omega]

theorem getElem?_shiftTele (s : Nat) :
    (shiftTele off d i As j)[s]? = (As[s]?).map (shift off d i · (j + s)) := by
  induction As generalizing j s with
  | nil => simp
  | cons A As ih =>
    cases s with
    | zero => simp
    | succ s => rw [shiftTele_cons, List.getElem?_cons_succ, ih, List.getElem?_cons_succ,
                  show j + 1 + s = j + (s+1) from by omega]

theorem getElem?_instAllTele (i : Nat) :
    (instAllTele As as k)[i]? = (As[i]?).map (instAll · as (k + i)) := by
  induction As generalizing k i with
  | nil => simp
  | cons A As ih =>
    cases i with
    | zero => simp
    | succ i => rw [instAllTele_cons, List.getElem?_cons_succ, ih, List.getElem?_cons_succ,
                  show k + 1 + i = k + (i+1) from by omega]

/-! ## `instL` -/

@[simp] theorem instL_mkPi : (mkPi As B).instL ls = mkPi (As.map (instL ls)) (B.instL ls) := by
  induction As <;> simp [instL, *]

@[simp] theorem instL_mkLams : (mkLams As b).instL ls = mkLams (As.map (instL ls)) (b.instL ls) := by
  induction As <;> simp [instL, *]

@[simp] theorem instL_mkApp :
    (mkApp f as).instL ls = mkApp (f.instL ls) (as.map (instL ls)) := by
  induction as generalizing f <;> simp [instL, *]

@[simp] theorem instL_liftTele :
    (liftTele n As k).map (instL ls) = liftTele n (As.map (instL ls)) k := by
  induction As generalizing k <;> simp [*]

@[simp] theorem instL_instTele :
    (instTele a As k).map (instL ls) = instTele (a.instL ls) (As.map (instL ls)) k := by
  induction As generalizing k <;> simp [*]

@[simp] theorem instL_shift : (shift off d i e j).instL ls = shift off d i (e.instL ls) j := by
  simp [shift]

@[simp] theorem instL_shiftTele :
    (shiftTele off d i As j).map (instL ls) = shiftTele off d i (As.map (instL ls)) j := by
  induction As generalizing j <;> simp [*]

/-! ## `inst` -/

theorem inst_mkPi :
    (mkPi As B).inst a k = mkPi (instTele a As k) (B.inst a (k + As.length)) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [mkPi_cons, inst, instTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

theorem inst_mkLams :
    (mkLams As b).inst a k = mkLams (instTele a As k) (b.inst a (k + As.length)) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [mkLams_cons, inst, instTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

theorem inst_mkApp :
    (mkApp f as).inst a k = mkApp (f.inst a k) (as.map (·.inst a k)) := by
  induction as generalizing f <;> simp [inst, *]

/-- The single β-step reduct of `(mkLams As b) a`. -/
theorem inst_mkLams_zero : (mkLams As b).inst a = mkLams (instTele a As) (b.inst a As.length) := by
  rw [inst_mkLams, Nat.zero_add]

/-- The type of `f a` when `f : mkPi (A :: As) B`. -/
theorem inst_mkPi_zero : (mkPi As B).inst a = mkPi (instTele a As) (B.inst a As.length) := by
  rw [inst_mkPi, Nat.zero_add]

theorem inst_mkApp_bvars_lo (h : k ≤ lo) :
    (mkApp f (bvars (lo+1) m)).inst a k = mkApp (f.inst a k) (bvars lo m) := by
  rw [inst_mkApp, map_inst_bvars_lo h]

theorem inst_mkApp_bvars_hi (h : lo + m ≤ k) :
    (mkApp f (bvars lo m)).inst a k = mkApp (f.inst a k) (bvars lo m) := by
  rw [inst_mkApp, map_inst_bvars_hi h]

/-! ## `ClosedN` -/

theorem closedN_mkPi : ClosedN (mkPi As B) k ↔ ClosedTele As k ∧ ClosedN B (k + As.length) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [mkPi_cons, ClosedN, ih, closedTele_cons, List.length_cons, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [show k + 1 + As.length = k + (As.length + 1) by omega]

theorem closedN_mkLams : ClosedN (mkLams As b) k ↔ ClosedTele As k ∧ ClosedN b (k + As.length) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [mkLams_cons, ClosedN, ih, closedTele_cons, List.length_cons, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [show k + 1 + As.length = k + (As.length + 1) by omega]

theorem closedN_mkApp :
    ClosedN (mkApp f as) k ↔ ClosedN f k ∧ ∀ a ∈ as, ClosedN a k := by
  induction as generalizing f with
  | nil => simp
  | cons a as ih => simp only [mkApp_cons, ih, ClosedN, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem closedTele_append :
    ClosedTele (As ++ Bs) k ↔ ClosedTele As k ∧ ClosedTele Bs (k + As.length) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [List.cons_append, closedTele_cons, ih, List.length_cons, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [show k + 1 + As.length = k + (As.length + 1) by omega]

theorem ClosedTele.mono (h : k ≤ k') : ∀ {As}, ClosedTele As k → ClosedTele As k'
  | [], _ => trivial
  | _ :: _, hA => ⟨hA.1.mono h, hA.2.mono (Nat.succ_le_succ h)⟩

theorem ClosedTele.liftTele_eq : ∀ {As}, ClosedTele As k → k ≤ j → liftTele n As j = As
  | [], _, _ => rfl
  | _ :: _, hA, hj => by
    rw [liftTele_cons, hA.1.liftN_eq hj, hA.2.liftTele_eq (Nat.succ_le_succ hj)]

theorem ClosedTele.instTele_eq : ∀ {As}, ClosedTele As k → k ≤ j → instTele a As j = As
  | [], _, _ => rfl
  | _ :: _, hA, hj => by
    rw [instTele_cons, hA.1.instN_eq hj, hA.2.instTele_eq (Nat.succ_le_succ hj)]

theorem closedTele_iff : ∀ {As : List VExpr} {k},
    ClosedTele As k ↔ ∀ i A, As[i]? = some A → ClosedN A (k + i)
  | [], _ => by simp
  | A :: As, k => by
    rw [closedTele_cons, closedTele_iff]
    constructor
    · rintro ⟨h1, h2⟩ i A' hA
      cases i with
      | zero => cases hA; simpa using h1
      | succ i =>
        rw [List.getElem?_cons_succ] at hA
        have := h2 i A' hA
        rwa [show k + (i+1) = k + 1 + i from by omega]
    · intro h
      refine ⟨by simpa using h 0 A rfl, fun i A' hA => ?_⟩
      have := h (i+1) A' (by rwa [List.getElem?_cons_succ])
      rwa [show k + 1 + i = k + (i+1) from by omega]

theorem closedN_mkApp_bvars (h : n ≤ k) :
    ClosedN (mkApp f (bvars 0 n)) k ↔ ClosedN f k := by
  rw [closedN_mkApp]
  exact and_iff_left (closedN_bvars (by omega))

/-! ## `LevelWF` -/

@[simp] theorem levelWF_mkPi :
    LevelWF U (mkPi As B) ↔ (∀ A ∈ As, LevelWF U A) ∧ LevelWF U B := by
  induction As with
  | nil => simp
  | cons A As ih => simp only [mkPi_cons, LevelWF, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

@[simp] theorem levelWF_mkLams :
    LevelWF U (mkLams As b) ↔ (∀ A ∈ As, LevelWF U A) ∧ LevelWF U b := by
  induction As with
  | nil => simp
  | cons A As ih => simp only [mkLams_cons, LevelWF, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

@[simp] theorem levelWF_mkApp :
    LevelWF U (mkApp f as) ↔ LevelWF U f ∧ ∀ a ∈ as, LevelWF U a := by
  induction as generalizing f with
  | nil => simp
  | cons a as ih => simp only [mkApp_cons, ih, LevelWF, List.mem_cons, forall_eq_or_imp, and_assoc]

/-! ## `shift` and `shiftTele` -/

theorem shift_eq' : shift off d i e j = liftN off (liftN d e j) (d + i + j) := by
  rw [shift_def, liftN'_comm _ off d (i+j) j (Nat.le_add_left ..)]
  congr 1
  omega

@[simp] theorem shift_zero_left : shift 0 d i e j = e.liftN d j := by simp [shift]
@[simp] theorem shift_zero_right : shift off 0 i e j = e.liftN off (i + j) := by simp [shift]

@[simp] theorem shiftTele_zero_left : shiftTele 0 d i As j = liftTele d As j := by
  induction As generalizing j <;> simp [*]

theorem shiftTele_zero_right : shiftTele off 0 i As j = liftTele off As (i + j) := by
  induction As generalizing j with
  | nil => rfl
  | cons A As ih => rw [shiftTele_cons, liftTele_cons, shift_zero_right, ih]; rfl

/-- The design document's `liftTele m = shiftTele m 0 0`. -/
theorem liftTele_eq_shiftTele : liftTele m As = shiftTele m 0 0 As := by
  rw [shiftTele_zero_right]

theorem liftTele_liftTele_eq_shiftTele :
    liftTele d (liftTele off As (i + j)) j = shiftTele off d i As j := by
  induction As generalizing j with
  | nil => rfl
  | cons A As ih =>
    rw [liftTele_cons, liftTele_cons, shiftTele_cons, shift_def]
    refine congrArg _ ?_
    rw [show i + j + 1 = i + (j + 1) by omega, ih]

theorem shift_mkPi :
    shift off d i (mkPi As B) j
      = mkPi (shiftTele off d i As j) (shift off d i B (j + As.length)) := by
  rw [shift_def, liftN_mkPi, liftN_mkPi, length_liftTele,
    liftTele_liftTele_eq_shiftTele, shift_def, Nat.add_assoc i j As.length]

theorem shift_mkLams :
    shift off d i (mkLams As b) j
      = mkLams (shiftTele off d i As j) (shift off d i b (j + As.length)) := by
  rw [shift_def, liftN_mkLams, liftN_mkLams, length_liftTele,
    liftTele_liftTele_eq_shiftTele, shift_def, Nat.add_assoc i j As.length]

theorem shift_mkApp :
    shift off d i (mkApp f as) j
      = mkApp (shift off d i f j) (as.map (shift off d i · j)) := by
  rw [shift_def, liftN_mkApp, liftN_mkApp, List.map_map]
  rfl

theorem shift_mkApp_bvars (h : i + j ≤ lo) :
    shift off d i (mkApp f (bvars lo m)) j
      = mkApp (shift off d i f j) (bvars (d + (off + lo)) m) := by
  rw [shift_def, liftN_mkApp_bvars_lo h,
    liftN_mkApp_bvars_lo (show j ≤ off + lo by omega), shift_def]

/-! ## `instAll`: the β-normal form of a saturated `mkLams` -/

@[simp] theorem instAll_sort : instAll (.sort u) as k = .sort u := by
  induction as generalizing k <;> simp [inst, *]

@[simp] theorem instAll_const : instAll (.const c us) as k = .const c us := by
  induction as generalizing k <;> simp [inst, *]

@[simp] theorem instAll_app :
    instAll (.app f a) as k = .app (instAll f as k) (instAll a as k) := by
  induction as generalizing f a k <;> simp [inst, *]

@[simp] theorem instAll_lam :
    instAll (.lam A b) as k = .lam (instAll A as k) (instAll b as (k+1)) := by
  induction as generalizing A b k with
  | nil => rfl
  | cons a as ih =>
    rw [instAll_cons, instAll_cons, instAll_cons]
    simp only [inst, ih]
    rw [show k + as.length + 1 = k + 1 + as.length by omega]

@[simp] theorem instAll_forallE :
    instAll (.forallE A b) as k = .forallE (instAll A as k) (instAll b as (k+1)) := by
  induction as generalizing A b k with
  | nil => rfl
  | cons a as ih =>
    rw [instAll_cons, instAll_cons, instAll_cons]
    simp only [inst, ih]
    rw [show k + as.length + 1 = k + 1 + as.length by omega]

theorem instAll_mkApp :
    instAll (mkApp f bs) as k = mkApp (instAll f as k) (bs.map (instAll · as k)) := by
  induction bs generalizing f <;> simp [*]

theorem instAll_mkPi :
    instAll (mkPi As B) as k
      = mkPi (instAllTele As as k) (instAll B as (k + As.length)) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [mkPi_cons, instAll_forallE, instAllTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

theorem instAll_mkLams :
    instAll (mkLams As b) as k
      = mkLams (instAllTele As as k) (instAll b as (k + As.length)) := by
  induction As generalizing k with
  | nil => simp
  | cons A As ih =>
    simp only [mkLams_cons, instAll_lam, instAllTele_cons, ih, List.length_cons,
      show k + 1 + As.length = k + (As.length + 1) from by omega]

@[simp] theorem instL_instAll :
    (instAll e as k).instL ls = instAll (e.instL ls) (as.map (instL ls)) k := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- A term closed below the instantiation cut is untouched. -/
theorem ClosedN.instAll_eq (h : ClosedN e k) : instAll e as k = e := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih => rw [instAll_cons, h.instN_eq (Nat.le_add_right ..), ih h]

/-- Full β-reduction of a saturated application to a weakening: the arguments are discarded. -/
theorem instAll_liftN (as : List VExpr) (e : VExpr) (k : Nat) :
    instAll (liftN as.length e k) as k = e := by
  induction as generalizing e with
  | nil => simp
  | cons a as ih =>
    rw [instAll_cons, List.length_cons,
      ← liftN'_liftN' (e := e) (n1 := as.length) (n2 := 1) (k1 := k) (k2 := k + as.length)
        (Nat.le_add_right ..) (Nat.le_of_eq (Nat.add_comm ..)),
      inst_liftN, ih]

/-! ### Instantiating by a telescope's own variables

The key "apply a telescope to its own variables" law: `mkLams As b` applied to
`bvars 0 |As|` β-reduces back to `b`.  See `instAll_bvars`. -/

theorem instAll_bvar_high (k n m : Nat) :
    instAll (.bvar (k + n + m)) (bvars 0 n) k = .bvar (k + m) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [bvars_succ, instAll_cons, length_bvars]
    simp only [inst, instVar, if_neg (show ¬ (k + (n+1) + m < k + n) by omega),
      if_neg (show ¬ (k + (n+1) + m = k + n) by omega)]
    rw [show k + (n+1) + m - 1 = k + n + m by omega, ih]

theorem instAll_bvar_lt (h : i < k + n) : instAll (.bvar i) (bvars 0 n) k = .bvar i := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [bvars_succ, instAll_cons, length_bvars]
    simp only [inst, instVar]
    rcases Nat.lt_or_ge i (k + n) with h' | h'
    · rw [if_pos h']; exact ih h'
    · have hi : i = k + n := by omega
      subst hi
      rw [if_neg (Nat.lt_irrefl _), if_pos rfl]
      simp only [liftN, liftVar_base]
      rw [show k + n + (0 + n) = k + n + n by omega, instAll_bvar_high]

/-- **Beta on the identity spine.** If `e` is closed at `k + n` then instantiating its `n`
variables above `k` by the telescope's own variables `bvars 0 n` gives `e` back. -/
theorem instAll_bvars (h : ClosedN e (k + n)) : instAll e (bvars 0 n) k = e := by
  induction e generalizing k with
  | bvar i => exact instAll_bvar_lt h
  | sort => simp
  | const => simp
  | app f a ih1 ih2 => rw [instAll_app, ih1 h.1, ih2 h.2]
  | lam A b ih1 ih2 =>
    rw [instAll_lam, ih1 h.1, ih2 (k := k+1) (by rw [Nat.add_right_comm]; exact h.2)]
  | forallE A b ih1 ih2 =>
    rw [instAll_forallE, ih1 h.1, ih2 (k := k+1) (by rw [Nat.add_right_comm]; exact h.2)]

/-- **The saturation law.**  A term weakened past `n` binders and then instantiated by
those binders' own variables is unchanged — no closedness hypothesis needed.

This is the pure-syntax core of "`f : mkPi As B` applied, inside `As.reverse ++ Γ₀`, to
`bvars 0 |As|`, has type `B`": with `n := |As|` and `k := 0`, applying `liftN_mkPi` turns
the type into `mkPi (liftTele n As n) (liftN n B n)`, and saturating the spine instantiates
the body to `instAll (liftN n B n) (bvars 0 n) = B`. -/
theorem instAll_liftN_bvars (n k : Nat) (e : VExpr) :
    instAll (liftN n e (k + n)) (bvars 0 n) k = e := by
  induction e generalizing k with
  | bvar i =>
    simp only [liftN, liftVar]
    split
    · exact instAll_bvar_lt ‹_›
    · rename_i h
      rw [Nat.not_lt] at h
      rw [show n + i = k + n + (i - k) from by omega, instAll_bvar_high,
        show k + (i - k) = i from by omega]
  | sort => simp [liftN]
  | const => simp [liftN]
  | app f a ih1 ih2 => rw [liftN, instAll_app, ih1, ih2]
  | lam A b ih1 ih2 =>
    rw [liftN, instAll_lam, ih1, show k + n + 1 = k + 1 + n from by omega, ih2]
  | forallE A b ih1 ih2 =>
    rw [liftN, instAll_forallE, ih1, show k + n + 1 = k + 1 + n from by omega, ih2]

theorem instAll_liftN_bvars_zero (n : Nat) (e : VExpr) :
    instAll (liftN n e n) (bvars 0 n) = e := by
  simpa using instAll_liftN_bvars n 0 e

/-- The telescope version of `instAll_liftN_bvars`. -/
theorem instAllTele_liftTele_bvars (n k : Nat) (As : List VExpr) :
    instAllTele (liftTele n As (k + n)) (bvars 0 n) k = As := by
  induction As generalizing k with
  | nil => rfl
  | cons A As ih =>
    rw [liftTele_cons, instAllTele_cons, instAll_liftN_bvars,
      show k + n + 1 = k + 1 + n from by omega, ih]

/-- The closed-term form: `(mkLams As b).mkApp (bvars 0 |As|)` β-reduces to `b`. -/
theorem instAll_bvars_of_closed (h : ClosedN (mkLams As b) 0) :
    instAll b (bvars 0 As.length) = b :=
  instAll_bvars (k := 0) (closedN_mkLams.1 h).2

/-- Same, for a pi-telescope body. -/
theorem instAll_bvars_of_closed_pi (h : ClosedN (mkPi As B) 0) :
    instAll B (bvars 0 As.length) = B :=
  instAll_bvars (k := 0) (closedN_mkPi.1 h).2

end VExpr
end Lean4Lean
