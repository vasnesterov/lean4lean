import Lean4Lean.Verify.Axioms

/-!
# Class (B) attack: `Expr.looseBVarRange_eq` and the `Expr.mkData` pair

Analysis only; nothing here is used by the kernel proofs.  Companion to
`Lean4Lean/Tests/AxiomConsistency.lean` (the `Level` trio) and
`docs/axiom-audit.md` §12-§13.

The three whitelisted axioms in play:

* `Lean.Expr.mkData_eq` (`H : br ≤ 2 ^ 20 - 1`)
* `Lean.Expr.mkAppData_eq` (unconditional)
* `Lean.Expr.looseBVarRange_eq` (`h : e.BVarBounded`) — class (B): it constrains
  the opaque `mkData`/`mkAppData` *through* the definable observation
  `Expr.Data.looseBVarRange`, which has a provable bound.  That is the shape
  that proved `False` in §3.1 before `BVarBounded` was added.

Results, in the three evidence strengths kept separate throughout:

* **§E2 (proved).** `looseBVarRange_eq` is **derivable** from the other two under
  `BVarBounded`.  It need not be an axiom at all.  This is a stronger outcome
  than the `Level` case, where `hasParam_eq` turned out to be *independent*.
* **§E3 (proved).** The side condition is **load-bearing**, and not merely
  sufficient: the unconditional form is refutable outright, with no axiom at all.
* **§E4 (proved).** A model validating `mkData_eq` and `mkAppData_eq`
  simultaneously.  With §E2 this settles joint consistency of the whole trio.

Everything is kernel-checked.  No `bv_decide`, no `native_decide` — §E0 replaces
the four `…_native.bv_decide.ax_N` axioms that `Verify/Expr.lean` currently
mints (see `docs/axiom-audit.md` §12.5).
-/

namespace Lean4Lean.Tests.AxiomConsistencyExpr
open Lean Lean.Expr

set_option allowUnsafeReducibility true
attribute [local reducible] Lean.Expr.Data

/-! ## §E0. Kernel-checked bit facts

`Verify/Expr.lean` proves the corresponding statements with `bv_decide`, which
is not kernel-checked: it compiles the LRAT-certificate check, runs it, and
mints a fresh axiom from the runtime result.  These go through `Nat` instead. -/

private theorem shr (a b : UInt64) : a.shiftRight b = a >>> b := rfl
private theorem shl (a b : UInt64) : a.shiftLeft b = a <<< b := rfl

private theorem add64 {x y : UInt64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b)
    (hab : a + b < 2 ^ 64) : (x + y).toNat = a + b := by
  rw [UInt64.toNat_add, hx, hy]; omega

private theorem shl64 {x n : UInt64} {a k : Nat} (hx : x.toNat = a) (hn : n.toNat % 64 = k)
    (hb : a * 2 ^ k < 2 ^ 64) : (x.shiftLeft n).toNat = a * 2 ^ k := by
  rw [shl, UInt64.toNat_shiftLeft, hx, hn, Nat.shiftLeft_eq]; omega

private theorem btl (b : Bool) : b.toUInt64.toNat < 2 := by cases b <;> simp [Bool.toUInt64]

/-- **Axiom-free.** The cached `looseBVarRange` is a read of a 20-bit field, so
it is `< 2 ^ 20` whatever `mkData` returns.  This is the provable property that
made the unconditional `looseBVarRange_eq` refutable (§E3), and it is also what
makes `mkAppData'`'s `assert!` unreachable.

Replaces `Lean.Expr.Data.looseBVarRange_le` of `Verify/Expr.lean`, which is
currently proved by `bv_decide`. -/
theorem looseBVarRange_lt (c : Expr.Data) : c.looseBVarRange.toNat < 2 ^ 20 := by
  have h : (c : UInt64).toNat < 2 ^ 64 := UInt64.toNat_lt_size c
  simp only [Data.looseBVarRange, shr, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  omega

theorem u32_max (x y : UInt32) : (max x y).toNat = max x.toNat y.toNat := by
  simp only [Max.max]
  split <;> rename_i h <;> rw [UInt32.le_iff_toNat_le] at h <;> split <;> omega

/-- Field read of a value packed as `lo + br·2⁴⁴` with `lo` below the field. -/
private theorem field44 {c : UInt64} {lo br : Nat} (hlo : lo < 2 ^ 44) (hbr : br < 2 ^ 20)
    (hc : c.toNat = lo + br * 2 ^ 44) : (Data.looseBVarRange c).toNat = br := by
  simp only [Data.looseBVarRange, shr, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.shiftRight_eq_div_pow, hc]
  omega

/-- Field read of a value assembled by `|||` from three sub-field pieces and the
field itself.  `>>>` distributes over `|||`, and the three low pieces vanish. -/
private theorem or44 {A B C D : UInt64} {r : Nat}
    (hA : A.toNat < 2 ^ 44) (hB : B.toNat < 2 ^ 44) (hC : C.toNat < 2 ^ 44)
    (hD : D.toNat = r * 2 ^ 44) (hr : r < 2 ^ 20) :
    (Data.looseBVarRange (A ||| B ||| C ||| D)).toNat = r := by
  have e1 : A.toNat >>> 44 = 0 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have e2 : B.toNat >>> 44 = 0 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have e3 : C.toNat >>> 44 = 0 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have e4 : D.toNat >>> 44 = r := by rw [Nat.shiftRight_eq_div_pow, hD]; omega
  simp only [Data.looseBVarRange, shr, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    UInt64.toNat_or, UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
    Nat.shiftRight_or_distrib, e1, e2, e3, e4]
  simp; omega

set_option maxHeartbeats 1000000 in
/-- In range, `mkData'` packs `br` above bit 44 with everything else below it. -/
private theorem mkData'_pack {h : UInt64} {br : Nat} {d : UInt32} {fv ev lv lp : Bool}
    (H : br ≤ 2 ^ 20 - 1) :
    ∃ lo < 2 ^ 44, (mkData' h br d fv ev lv lp : UInt64).toNat = lo + br * 2 ^ 44 := by
  rw [mkData', if_pos H]
  have hD : (if d > 255 then (255 : UInt8) else d.toUInt8).toNat < 256 := UInt8.toNat_lt_size _
  have f1 := btl fv; have f2 := btl ev; have f3 := btl lv; have f4 := btl lp
  have hb : h.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by omega)
  have t0 : (h.toUInt32.toUInt64).toNat = h.toNat % 2 ^ 32 := by simp
  have t1 : ((if d > 255 then (255 : UInt8) else d.toUInt8).toUInt64.shiftLeft 32).toNat
      = (if d > 255 then (255 : UInt8) else d.toUInt8).toNat * 2 ^ 32 :=
    shl64 (by simp) (by simp) (by omega)
  have s1 := add64 t0 t1 (by omega)
  have t2 : (fv.toUInt64.shiftLeft 40).toNat = fv.toUInt64.toNat * 2 ^ 40 :=
    shl64 rfl (by simp) (by omega)
  have s2 := add64 s1 t2 (by omega)
  have t3 : (ev.toUInt64.shiftLeft 41).toNat = ev.toUInt64.toNat * 2 ^ 41 :=
    shl64 rfl (by simp) (by omega)
  have s3 := add64 s2 t3 (by omega)
  have t4 : (lv.toUInt64.shiftLeft 42).toNat = lv.toUInt64.toNat * 2 ^ 42 :=
    shl64 rfl (by simp) (by omega)
  have s4 := add64 s3 t4 (by omega)
  have t5 : (lp.toUInt64.shiftLeft 43).toNat = lp.toUInt64.toNat * 2 ^ 43 :=
    shl64 rfl (by simp) (by omega)
  have s5 := add64 s4 t5 (by omega)
  have t6 : (br.toUInt64.shiftLeft 44).toNat = br * 2 ^ 44 :=
    shl64 (by simp; omega) (by simp) (by omega)
  exact ⟨_, by omega, add64 s5 t6 (by omega)⟩

/-- Replaces `Lean.Expr.mkData_looseBVarRange` of `Verify/Expr.lean`. -/
theorem mkData'_looseBVarRange {h : UInt64} {br : Nat} {d : UInt32} {fv ev lv lp : Bool}
    (H : br ≤ 2 ^ 20 - 1) : (mkData' h br d fv ev lv lp).looseBVarRange.toNat = br := by
  obtain ⟨lo, hlo, hc⟩ := mkData'_pack (h := h) (d := d) (fv := fv) (ev := ev) (lv := lv)
    (lp := lp) H
  exact field44 hlo (by omega) hc

set_option maxHeartbeats 800000 in
/-- Replaces `Lean.Expr.mkAppData_looseBVarRange` of `Verify/Expr.lean`.

Note the `assert!` of `mkAppData'` is discharged, not assumed: its argument is a
`max` of two 20-bit field reads, so the `panic!` branch is unreachable and the
unconditional `mkAppData_eq` costs nothing. -/
theorem mkAppData'_looseBVarRange (f a : Expr.Data) :
    (mkAppData' f a).looseBVarRange.toNat
      = max f.looseBVarRange.toNat a.looseBVarRange.toNat := by
  have hf := looseBVarRange_lt f; have ha := looseBVarRange_lt a
  have hass : max f.looseBVarRange a.looseBVarRange ≤ (Nat.pow 2 20 - 1).toUInt32 := by
    rw [UInt32.le_iff_toNat_le, u32_max]; simp; omega
  have h8 : (if max f.approxDepth.toUInt16 a.approxDepth.toUInt16 + 1 > 255 then (255 : UInt8)
      else (max f.approxDepth.toUInt16 a.approxDepth.toUInt16 + 1).toUInt8).toNat < 256 :=
    UInt8.toNat_lt_size _
  rw [mkAppData', if_pos hass]
  refine or44 ?_ ?_ ?_ ?_ (by omega)
  · have h15 : ((15 : UInt64) <<< (40 : UInt64)).toNat = 16492674416640 := by simp
    rw [UInt64.toNat_and, h15]
    have := Nat.and_le_right (n := (f ||| a).toNat) (m := 16492674416640)
    omega
  · rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    have : (mixHash f a).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by omega)
    omega
  · rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
    simp only [UInt64.toNat_ofNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    omega
  · rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, u32_max]
    simp only [UInt64.toNat_ofNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    omega

/-! ## §E1. The same facts for the real `mkData` / `mkAppData`, via the axioms -/

theorem mkData_looseBVarRange {h : UInt64} {br : Nat} {d : UInt32} {fv ev lv lp : Bool}
    (H : br ≤ 2 ^ 20 - 1) : (mkData h br d fv ev lv lp).looseBVarRange.toNat = br := by
  rw [mkData_eq H]; exact mkData'_looseBVarRange H

theorem mkAppData_looseBVarRange (f a : Expr.Data) :
    (mkAppData f a).looseBVarRange.toNat
      = max f.looseBVarRange.toNat a.looseBVarRange.toNat := by
  rw [mkAppData_eq]; exact mkAppData'_looseBVarRange f a

/-! ## §E2. `looseBVarRange_eq` is a **theorem**, not an axiom

The only clause of `BVarBounded` that does any work is `bvar`: every other
`mkData` call in the `Expr.data` computed field (`Lean/Expr.lean:471-513`)
passes an argument built from `looseBVarRange` *field reads*, which
`looseBVarRange_lt` already bounds unconditionally.  `BVarBounded`'s recursion
exists only to reach every `bvar` leaf. -/

private theorem le_of_field (c : Expr.Data) : c.looseBVarRange.toNat ≤ 2 ^ 20 - 1 := by
  have := looseBVarRange_lt c; omega

set_option maxHeartbeats 1000000 in
theorem data_looseBVarRange : ∀ (e : Expr), e.BVarBounded →
    (Expr.data e).looseBVarRange.toNat = e.looseBVarRange' := by
  intro e
  induction e with
  | bvar i => intro h; exact mkData_looseBVarRange h
  | fvar _ => intro _; exact mkData_looseBVarRange (by omega)
  | mvar _ => intro _; exact mkData_looseBVarRange (by omega)
  | sort _ => intro _; exact mkData_looseBVarRange (by omega)
  | const _n _us => intro _; exact mkData_looseBVarRange (by omega)
  | lit _ => intro _; exact mkData_looseBVarRange (by omega)
  | mdata _ b ih =>
    intro h; exact (mkData_looseBVarRange (le_of_field b.data)).trans (ih h)
  | proj _ _ b ih =>
    intro h; exact (mkData_looseBVarRange (le_of_field b.data)).trans (ih h)
  | app f a ihf iha =>
    intro h
    exact (mkAppData_looseBVarRange f.data a.data).trans (by rw [ihf h.1, iha h.2]; rfl)
  | lam _ t b _ iht ihb =>
    intro h
    have hb : max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1) ≤ 2 ^ 20 - 1 := by
      have := looseBVarRange_lt t.data; have := looseBVarRange_lt b.data; omega
    exact (mkData_looseBVarRange hb).trans (by rw [iht h.1, ihb h.2]; rfl)
  | forallE _ t b _ iht ihb =>
    intro h
    have hb : max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1) ≤ 2 ^ 20 - 1 := by
      have := looseBVarRange_lt t.data; have := looseBVarRange_lt b.data; omega
    exact (mkData_looseBVarRange hb).trans (by rw [iht h.1, ihb h.2]; rfl)
  | letE _ t v b _ iht ihv ihb =>
    intro h
    have hb : max (max t.data.looseBVarRange.toNat v.data.looseBVarRange.toNat)
        (b.data.looseBVarRange.toNat - 1) ≤ 2 ^ 20 - 1 := by
      have := looseBVarRange_lt t.data; have := looseBVarRange_lt v.data
      have := looseBVarRange_lt b.data; omega
    exact (mkData_looseBVarRange hb).trans (by rw [iht h.1, ihv h.2.1, ihb h.2.2]; rfl)

/-- **Axiom `Lean.Expr.looseBVarRange_eq` as a theorem**, from
`Expr.mkData_eq` and `Expr.mkAppData_eq` only. -/
theorem looseBVarRange_eq_proved (e : Expr) (h : e.BVarBounded) :
    e.looseBVarRange = e.looseBVarRange' :=
  data_looseBVarRange e h

/-! ## §E3. The side condition is load-bearing

Not a model separation but an outright refutation, with no axiom at all: the
cached field is 20 bits wide and `looseBVarRange'` is unbounded, so the
*unconditional* form is false in every interpretation of `mkData`.  This is the
mechanism of the original `False`-proof of `docs/axiom-audit.md` §3.1, restated
as a negation so that it proves the necessity of `BVarBounded` without
introducing an inconsistency. -/

theorem looseBVarRange'_bvar_big : (Expr.bvar (2 ^ 20 - 1)).looseBVarRange' = 2 ^ 20 := by
  show 2 ^ 20 - 1 + 1 = 2 ^ 20
  omega

theorem not_looseBVarRange_eq_unconditional :
    ¬ ∀ e : Expr, e.looseBVarRange = e.looseBVarRange' := by
  intro H
  have h1 := H (.bvar (2 ^ 20 - 1))
  rw [looseBVarRange'_bvar_big] at h1
  have h2 : (Expr.bvar (2 ^ 20 - 1)).looseBVarRange < 2 ^ 20 :=
    looseBVarRange_lt (Expr.data _)
  omega

/-- The witness is not `BVarBounded`, so §E2 and §E3 do not collide. -/
theorem bvar_big_not_bvarBounded : ¬ (Expr.bvar (2 ^ 20 - 1)).BVarBounded := by
  show ¬ (2 ^ 20 - 1 + 1 ≤ 2 ^ 20 - 1)
  omega

/-! ## §E4. A model of `Expr.mkData_eq` + `Expr.mkAppData_eq`

Clamp the range into the field instead of panicking, exactly as `mkDataM` does
for `Level`.  Together with §E2 — which derives `looseBVarRange_eq` from these
two — this settles **joint consistency of the whole trio**. -/

/-- Candidate interpretation of the opaque `Lean.Expr.mkData`. -/
def mkDataC (h : UInt64) (br : Nat) (d : UInt32) (fv ev lv lp : Bool) : Expr.Data :=
  mkData' h (min br (2 ^ 20 - 1)) d fv ev lv lp

/-- Candidate interpretation of the opaque `Lean.Expr.mkAppData`: `mkAppData'`
itself, which is total (its `assert!` is unreachable, see
`mkAppData'_looseBVarRange`). -/
def mkAppDataC (f a : Expr.Data) : Expr.Data := mkAppData' f a

/-- The model validates `Lean.Expr.mkData_eq`. -/
theorem mkDataC_validates_mkData_eq {h br d fv ev lv lp} (H : br ≤ 2 ^ 20 - 1) :
    mkDataC h br d fv ev lv lp = mkData' h br d fv ev lv lp := by
  rw [mkDataC, Nat.min_eq_left H]

/-- The model validates `Lean.Expr.mkAppData_eq`, unconditionally. -/
theorem mkAppDataC_validates_mkAppData_eq : @mkAppDataC = @mkAppData' := rfl

/-- The clamped interpretation keeps the field exact at *every* argument, which
is what lets it validate the trio simultaneously. -/
theorem mkDataC_looseBVarRange {h br d fv ev lv lp} :
    (mkDataC h br d fv ev lv lp).looseBVarRange.toNat = min br (2 ^ 20 - 1) :=
  mkData'_looseBVarRange (by omega)

/-! ## Axiom hygiene.  §E0, §E3, §E4 must show no repo axiom at all; §E1 and §E2
must show exactly `Lean.Expr.mkData_eq` and `Lean.Expr.mkAppData_eq`.
Any `_native.*` entry, or any appearance of `Lean.Expr.looseBVarRange_eq`
itself, is a regression. -/

#print axioms looseBVarRange_lt
#print axioms mkData'_looseBVarRange
#print axioms mkAppData'_looseBVarRange
#print axioms looseBVarRange_eq_proved
#print axioms not_looseBVarRange_eq_unconditional
#print axioms mkDataC_validates_mkData_eq
#print axioms mkAppDataC_validates_mkAppData_eq

end Lean4Lean.Tests.AxiomConsistencyExpr
