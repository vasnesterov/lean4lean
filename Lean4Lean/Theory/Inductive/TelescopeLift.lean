import Lean4Lean.Theory.Inductive.Telescope

/-!
# `lift'` for the telescope algebra

`Theory/Inductive/Telescope.lean` develops `mkPi`/`mkLams`/`mkApp`/`bvars`/`instAll` against
`liftN`, `inst` and `instL`, but contains **no** `lift'` lemmas at all.  `Ctx.Lift'` is what
`TrProj.weak'` is stated over, so the missing analogues are built here.

Additive, and separate from `Telescope.lean` only to avoid contending for a file another
stream is editing; if the two are ever merged, everything below belongs in the `liftN`
sections it mirrors.

## Layers

1. **`Lift` algebra** — `Fixes` is antitone, and `consN k` fixes the `k` binders it
   introduces.
2. **`lift'` against `inst`** — `VExpr.lift'_inst`, the offset-`k` generalisation of
   `VExpr.lift'_inst_hi` (stated upstream only at offset 0), and `liftN_lift'`.
3. **`lift'` against the telescope operations** — `mkApp`, `bvars`, `mkLams` (via
   `liftTele'`), and the one with real content, `instAll`.

`instAll` is the only one needing a side condition.  `instAll A as k` splices `as` into
`A`'s top `|as|` variables, so unless `A` is closed at `k + |as|` it still has variables
reaching into the ambient context — and those move under a lift on one side of the equation
and not the other.  `VInductDecl'.ProjClosed` is what discharges this at each of
`projCore`'s splice sites; without it the equation is refutable, not merely unprovable.
-/

namespace Lean4Lean

namespace Lift

/-- `Fixes` is antitone in the cut. -/
theorem Fixes.le : ∀ {ρ : Lift} {n m}, n ≤ m → ρ.Fixes m → ρ.Fixes n
  | .refl, 0, _, _, _ => Fixes.zero
  | .refl, _+1, _, _, _ => trivial
  | .skip _, 0, _, _, _ => Fixes.zero
  | .skip _, _+1, m, hnm, h => by
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    exact absurd h (by simp [Fixes])
  | .cons _, 0, _, _, _ => Fixes.zero
  | .cons l, n+1, m, hnm, h => by
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    exact Fixes.le (ρ := l) (by omega) h

/-- `consN k` fixes the `k` binders it introduces. -/
theorem consN_fixes {ρ : Lift} : ∀ {k}, (ρ.consN k).Fixes k
  | 0 => Fixes.zero
  | k+1 => consN_fixes (k := k)

/-- Definitional, but the direction `simp` will not find on its own. -/
theorem liftVar_consN_succ {ρ : Lift} {k i : Nat} :
    (ρ.consN (k+1)).liftVar (i+1) = (ρ.consN k).liftVar i + 1 := rfl

end Lift

namespace VExpr

theorem liftN_eq_lift' {e : VExpr} {k : Nat} : e.liftN k = e.lift' (.skipN .refl k) := by
  simpa using (lift'_consN_skipN (e := e) (n := k) (k := 0)).symm

/-- Weakening by `k` commutes with a lift past `k` binders. -/
theorem liftN_lift' {e : VExpr} {k : Nat} {ρ : Lift} :
    (e.liftN k).lift' (ρ.consN k) = (e.lift' ρ).liftN k := by
  rw [liftN_eq_lift', liftN_eq_lift', ← lift'_comp, ← lift'_comp,
    Lift.skipN_comp_consN, Lift.comp_skipN]
  simp

/-- `lift'_inst_hi` at an arbitrary offset. -/
theorem lift'_inst {e1 e2 : VExpr} {k : Nat} {ρ : Lift} :
    (e1.inst e2 k).lift' (ρ.consN k) = (e1.lift' (ρ.consN (k+1))).inst (e2.lift' ρ) k := by
  induction e1 generalizing k with
  | bvar i =>
    rcases Nat.lt_trichotomy i k with h | h | h
    · rw [inst, instVar, if_pos h]
      simp only [lift']
      rw [Lift.consN_fixes.liftVar_eq h, Lift.consN_fixes.liftVar_eq (Nat.lt_succ_of_lt h),
        inst, instVar, if_pos h]
    · subst h
      rw [inst, instVar, if_neg (Nat.lt_irrefl _), if_pos rfl, liftN_lift']
      simp only [lift']
      rw [Lift.consN_fixes.liftVar_eq (Nat.lt_succ_self _), inst, instVar,
        if_neg (Nat.lt_irrefl _), if_pos rfl]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : k ≤ j := by omega
      have hle : j ≤ (ρ.consN k).liftVar j := Lift.le_liftVar
      rw [inst, instVar, if_neg (by omega), if_neg (by omega)]
      simp only [lift', Lift.liftVar_consN_succ, Nat.add_sub_cancel]
      rw [inst, instVar, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  | sort | const => rfl
  | app _ _ ih1 ih2 => simp only [inst, lift', ih1, ih2]
  | lam _ _ ih1 ih2 => simp only [inst, lift', ih1]; exact congrArg _ (ih2 (k := k+1))
  | forallE _ _ ih1 ih2 => simp only [inst, lift', ih1]; exact congrArg _ (ih2 (k := k+1))

/-! ## Telescope operations -/

@[simp] theorem lift'_mkApp {f : VExpr} {as : List VExpr} {ρ : Lift} :
    (mkApp f as).lift' ρ = mkApp (f.lift' ρ) (as.map (·.lift' ρ)) := by
  induction as generalizing f <;> simp [mkApp, lift', *]

theorem lift'_bvars {lo : Nat} {ρ : Lift} : ∀ {n}, ρ.Fixes (lo + n) →
    (bvars lo n).map (·.lift' ρ) = bvars lo n
  | 0, _ => rfl
  | n+1, h => by
    simp only [bvars, List.map_cons, lift']
    rw [h.liftVar_eq (by omega), lift'_bvars (n := n) (h.le (by omega))]

/-- The telescope of `lift'_mkLams`: entry `j` is lifted past the `j` binders before it. -/
def liftTele' (ρ : Lift) : List VExpr → List VExpr
  | [] => []
  | A :: As => A.lift' ρ :: liftTele' ρ.cons As

@[simp] theorem liftTele'_nil : liftTele' ρ [] = [] := rfl
@[simp] theorem liftTele'_cons :
    liftTele' ρ (A :: As) = A.lift' ρ :: liftTele' ρ.cons As := rfl

@[simp] theorem length_liftTele' : ∀ {As : List VExpr} {ρ}, (liftTele' ρ As).length = As.length
  | [], _ => rfl
  | _ :: _, _ => congrArg Nat.succ length_liftTele'

theorem lift'_mkLams : ∀ {As : List VExpr} {b : VExpr} {ρ : Lift},
    (mkLams As b).lift' ρ = mkLams (liftTele' ρ As) (b.lift' (ρ.consN As.length))
  | [], _, _ => rfl
  | A :: As, b, ρ => by
    simp only [mkLams_cons, lift', liftTele'_cons, List.length_cons]
    refine congrArg _ ?_
    rw [lift'_mkLams (As := As) (b := b) (ρ := ρ.cons)]
    congr 2
    show (ρ.consN 1).consN As.length = _
    rw [Lift.consN_consN, Nat.add_comm]

/-! ## `instAll`

Stated **unconditionally** first, with the lift applied to `A` on the right as well.  That
version front-peels cleanly; the closed corollary below is what `projCore` actually uses.

(Peeling with the closedness hypothesis in place does *not* work: the intermediate
`A.inst a (k + |as|)` is not closed at `k + |as|`, because `a` brings ambient variables in.)
-/

theorem lift'_instAll' {ρ : Lift} : ∀ {as : List VExpr} {A : VExpr} {k},
    (instAll A as k).lift' (ρ.consN k)
      = instAll (A.lift' (ρ.consN (k + as.length))) (as.map (·.lift' ρ)) k
  | [], _, _ => rfl
  | a :: as, A, k => by
    simp only [instAll_cons, List.map_cons, List.length_cons, List.length_map]
    rw [lift'_instAll' (as := as) (A := A.inst a (k + as.length)) (k := k), lift'_inst,
      Nat.add_assoc]

/-- The form `projCore` consumes: when `A` is closed at the cut, the lift on `A` vanishes. -/
theorem lift'_instAll {A : VExpr} {ρ : Lift} {as : List VExpr} {k : Nat}
    (h : A.ClosedN (k + as.length)) :
    (instAll A as k).lift' (ρ.consN k) = instAll A (as.map (·.lift' ρ)) k := by
  rw [lift'_instAll', h.lift'_eq Lift.consN_fixes]

theorem lift'_instAllTele {as : List VExpr} {ρ : Lift} : ∀ {As : List VExpr} {k},
    ClosedTele As (k + as.length) →
    liftTele' (ρ.consN k) (instAllTele As as k) = instAllTele As (as.map (·.lift' ρ)) k
  | [], _, _ => rfl
  | A :: As, k, h => by
    simp only [instAllTele_cons, liftTele'_cons]
    rw [lift'_instAll h.1]
    exact congrArg _ (lift'_instAllTele (as := as) (ρ := ρ) (As := As) (k := k+1)
      (by simpa [Nat.add_right_comm] using h.2))

/-! ## Closedness transported through `instL` -/

theorem ClosedTele.map_instL : ∀ {As : List VExpr} {k ls},
    ClosedTele As k → ClosedTele (As.map (VExpr.instL ls)) k
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1.instL, ClosedTele.map_instL h.2⟩

end VExpr

end Lean4Lean
