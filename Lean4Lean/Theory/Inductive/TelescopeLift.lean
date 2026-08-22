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

## Settled rule for this file: state the unconditional form first

Three times now a substitution lemma about `instAll` has been stated with its closedness
hypothesis in place and turned out to front-peel *wrongly* — `instAll A (a :: as) k`
recurses on `A.inst a (k + |as|)`, which is **not** closed at `k + |as|`, because `a` brings
ambient variables in, so the induction hypothesis is unavailable.  Each time the fix was the
same: state the version with the operation also applied to `A` on the right (no hypothesis),
which front-peels cleanly, and derive the closed corollary in one step.  See
`lift'_instAll'`/`lift'_instAll`, `inst_instAll'`/`inst_instAll`, and — by iterating the
latter rather than peeling — `instAll_instAll` in `StructureClosed.lean`.

If a fourth arrives, write the unconditional form first and do not rediscover this.

*A note on notes.*  Every heuristic recorded during this development needed narrowing after
contact with use, and always the same way: the first formulation encoded the surface form of
the single instance it came from.  "Grep before writing" became **grep for the shape, not the
name** (three lemmas existed under identifiers no name-search would find — one was declared
`_root_.Lean4Lean.OnCtx.instL` inside another namespace).  "State the general version"
needed the boundary condition at `instAllCongrSort`.  Expect the same of the rule above, and
of the next one anyone writes here.

## Side conditions

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

/-- Entry `i` of a telescope closed at `k` is closed at `k + i`. -/
theorem ClosedTele.getElem? {A : VExpr} : ∀ {As : List VExpr} {k i : Nat},
    ClosedTele As k → As[i]? = some A → A.ClosedN (k + i) := by
  intro As
  induction As with
  | nil => intro k i _ hA; simp at hA
  | cons B As ih =>
    intro k i h hA
    cases i with
    | zero => cases hA; simpa using h.1
    | succ i =>
      have := ih (k := k+1) (i := i) h.2 (by simpa using hA)
      rw [← Nat.add_assoc]; simpa [Nat.add_right_comm] using this

/-! ## `instAll` against `inst`

The same development for `inst`, which `TrProj.instN` needs.  Same shape: unconditional
first, closed corollary second. -/

theorem inst_instAll' {a : VExpr} {m : Nat} : ∀ {as : List VExpr} {A : VExpr} {j},
    (instAll A as j).inst a (m + j)
      = instAll (A.inst a (m + j + as.length)) (as.map (·.inst a m)) j
  | [], _, _ => rfl
  | b :: as, A, j => by
    simp only [instAll_cons, List.map_cons, List.length_cons, List.length_map]
    rw [inst_instAll' (as := as) (A := A.inst b (j + as.length)) (j := j),
      show m + j + as.length = m + (j + as.length) from by omega, inst_inst_hi,
      show m + (j + as.length) + 1 = m + j + (as.length + 1) from by omega]

theorem inst_instAll {A a : VExpr} {as : List VExpr} {m j : Nat}
    (h : A.ClosedN (j + as.length)) :
    (instAll A as j).inst a (m + j) = instAll A (as.map (·.inst a m)) j := by
  rw [inst_instAll', h.instN_eq (by omega)]

theorem inst_instAllTele {a : VExpr} {as : List VExpr} {m : Nat} :
    ∀ {As : List VExpr} {j}, ClosedTele As (j + as.length) →
    instTele a (instAllTele As as j) (m + j) = instAllTele As (as.map (·.inst a m)) j
  | [], _, _ => rfl
  | A :: As, j, h => by
    simp only [instAllTele_cons, instTele_cons]
    rw [inst_instAll h.1]
    refine congrArg _ ?_
    have := inst_instAllTele (a := a) (as := as) (m := m) (As := As) (j := j+1)
      (by simpa [Nat.add_right_comm] using h.2)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem inst_bvars {a : VExpr} {lo n k : Nat} (h : lo + n ≤ k) :
    (bvars lo n).map (·.inst a k) = bvars lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bvars, List.map_cons, inst, instVar, if_pos (show lo + n < k by omega)]
    rw [ih (by omega)]

/-! ## Closed telescopes do not move -/

/-- A telescope closed at `k` is fixed by a `liftTele'` whose lift fixes `k`. -/
theorem liftTele'_eq_self : ∀ {As : List VExpr} {ρ : Lift} {k : Nat},
    ClosedTele As k → ρ.Fixes k → liftTele' ρ As = As
  | [], _, _, _, _ => rfl
  | A :: As, ρ, k, h, hρ => by
    rw [liftTele'_cons, h.1.lift'_eq hρ,
      liftTele'_eq_self (As := As) (ρ := ρ.cons) (k := k+1) h.2 hρ]

/-- The same for `instTele`, whose cut must sit at or above the closedness level. -/
theorem instTele_eq_self : ∀ {As : List VExpr} {a : VExpr} {k j : Nat},
    ClosedTele As k → k ≤ j → instTele a As j = As
  | [], _, _, _, _, _ => rfl
  | A :: As, a, k, j, h, hk => by
    rw [instTele_cons, h.1.instN_eq hk,
      instTele_eq_self (As := As) (a := a) (k := k+1) (j := j+1) h.2 (by omega)]

/-! ## Telescope substitution commutes -/

/-- The `lift'` analogue of `VExpr.liftTele_instTele`. -/
theorem liftTele'_instTele : ∀ {As : List VExpr} {a : VExpr} {ρ : Lift} {j : Nat},
    liftTele' (ρ.consN j) (instTele a As j)
      = instTele (a.lift' ρ) (liftTele' (ρ.consN (j+1)) As) j
  | [], _, _, _ => rfl
  | A :: As, a, ρ, j => by
    rw [instTele_cons, liftTele'_cons, liftTele'_cons, instTele_cons, lift'_inst]
    exact congrArg _ (liftTele'_instTele (As := As) (a := a) (ρ := ρ) (j := j+1))

/-- The `inst` analogue of `VExpr.liftTele_instTele`. -/
theorem instTele_instTele : ∀ {As : List VExpr} {a b : VExpr} {m j : Nat},
    instTele b (instTele a As j) (m + j)
      = instTele (a.inst b m) (instTele b As (m + j + 1)) j
  | [], _, _, _, _ => rfl
  | A :: As, a, b, m, j => by
    rw [instTele_cons, instTele_cons, instTele_cons, instTele_cons, inst_inst_hi]
    refine congrArg _ ?_
    have := instTele_instTele (As := As) (a := a) (b := b) (m := m) (j := j+1)
    rw [show m + (j+1) = m + j + 1 from by omega] at this
    rw [this, show m + j + 1 + 1 = m + (j+1) + 1 from by omega]

/-- `lift'_instAllTele` at offset 0, with `consN 0` already reduced so `rw` can match. -/
theorem lift'_instAllTele₀ {as As : List VExpr} {ρ : Lift} (h : ClosedTele As as.length) :
    liftTele' ρ (instAllTele As as) = instAllTele As (as.map (·.lift' ρ)) :=
  lift'_instAllTele (ρ := ρ) (k := 0) (by simpa using h)

/-- `inst_instAllTele` at offset 0, likewise. -/
theorem inst_instAllTele₀ {as As : List VExpr} {a : VExpr} {m : Nat}
    (h : ClosedTele As as.length) :
    instTele a (instAllTele As as) m = instAllTele As (as.map (·.inst a m)) :=
  inst_instAllTele (m := m) (j := 0) (by simpa using h)

/-! ## `Skips` through a telescope

Needed by `TrProj`'s F17 side condition, which is guarded on whether a field's binder is
*used* by the rest of the constructor's telescope — the abstract image of `inferProj`'s
`b.hasLooseBVars` (`Lean4Lean/TypeChecker.lean:252`). -/

/-- If a whole `mkPi` skips a variable window, so does each entry of its telescope, at that
entry's own depth. -/
theorem skips'_mkPi_getElem : ∀ {As : List VExpr} {R : VExpr} {n k m : Nat} {A : VExpr},
    Skips' n (mkPi As R) k → As[m]? = some A → Skips' n A (k + m)
  | B :: As, R, n, k, m, A, h, hm => by
    cases m with
    | zero => cases hm; simpa using h.1
    | succ m =>
      have := skips'_mkPi_getElem (As := As) (R := R) (n := n) (k := k+1) (m := m)
        h.2 (by simpa using hm)
      rw [← Nat.add_assoc]; simpa [Nat.add_right_comm] using this

/-! ## `instAll` above a weakened region -/

/-- `instAll` above a weakened region commutes with the weakening. -/
theorem liftN_instAll {n : Nat} : ∀ {as : List VExpr} {X : VExpr} {k : Nat},
    instAll (liftN n X k) as (k + n) = liftN n (instAll X as k) k
  | [], _, _ => rfl
  | a :: as, X, k => by
    rw [instAll_cons, instAll_cons,
      show k + n + as.length = n + (k + as.length) from by omega,
      ← liftN_instN_lo n X a (k + as.length) k (Nat.le_add_right ..),
      liftN_instAll (as := as) (X := X.inst a (k + as.length)) (k := k)]

end VExpr

end Lean4Lean
