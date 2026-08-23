import Lean4Lean.Verify.Axioms
import Std.Tactic.BVDecide

/-!
# Consistency analysis of `Lean4Lean/Verify/Axioms.lean`

This file is **analysis only**; nothing here is used by the kernel proofs.

The question it answers is about axioms 12/13/14 of `docs/axiom-audit.md`:

* 12 `Lean.Level.mkData_eq` (now carrying `H : d < 2 ^ 24`)
* 13 `Lean.Level.hasParam_eq`
* 14 `Lean.Level.hasMVar_eq`

`Lean.Level.mkData` is an `opaque` constant (`@[extern "lean_level_mk_data"]`),
so it is a *free* symbol of the theory: a set of assumptions about it is
consistent exactly when some definable function satisfies them all.
`Lean.Level.data` is an ordinary structural recursion whose only appeal to the
outside world is `mkData` (`Lean/Level.lean:98-106`), and `Level.hasParam`,
`Level.hasMVar`, `Level.depth`, `Level.hash` are field reads of `Level.data`.
So reinterpreting `mkData` as `f` reinterprets `Level.data` as `dataOf f` and
the three axioms as statements about `dataOf f`.

Two interpretations are given below, and then the free win.

* `mkDataM` (§1) satisfies **all three** axioms ⇒ 12+13+14 are **jointly
  consistent**; the argued contradiction of `docs/axiom-audit.md` §4 is dead.
* `mkDataZ` (§2) satisfies 12 but **refutes** 13 and 14 ⇒ 13/14 are
  **independent** of 12; they cannot be proved "using `mkData_eq` and friends"
  as their docstrings claim.
* §3 shows that under the side condition `dep l < 2 ^ 24` — the `Level`
  analogue of `Expr.BVarBounded`, and cheaper: one top-level bound, no
  per-subterm recursion — both **become theorems**, proved from axiom 12 alone.
  So axioms 13 and 14 can be retired from the guard's whitelist.

See `docs/axiom-audit.md` §12.
-/

namespace Lean4Lean.Tests.AxiomConsistency
open Lean Lean.Level

set_option allowUnsafeReducibility true
attribute [local reducible] Lean.Level.Data

/-! ## 0. Bit facts about `Level.mkData'`

These are the `Verify/Level.lean` proofs of `mkData_depth` / `mkData_hasParam` /
`mkData_hasMVar` with the `mkData_eq` rewrite removed, i.e. stated about the
model function `mkData'` directly, so that they assume no repo axiom. -/

theorem mkData'_depth (H : d < 2 ^ 24) : (mkData' h d hmv hp).depth.toNat = d := by
  rw [mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H)), Data.depth]
  have : d.toUInt64.toUInt32.toNat = d := by simp; omega
  refine .trans ?_ this; congr 2
  rw [← UInt64.toBitVec_inj]
  have : d.toUInt64.toNat = d := by simp; omega
  have : d.toUInt64.toBitVec ≤ 0xffffff#64 := (this ▸ Nat.le_sub_one_of_lt H :)
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  change (
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 40#64 = d.toUInt64.toBitVec
  bv_decide

theorem mkData'_hasParam (H : d < 2 ^ 24) : (mkData' h d hmv hp).hasParam = hp := by
  rw [mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H))]
  simp [Data.hasParam, (· == ·), ← UInt64.toBitVec_inj]
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  let L := ((
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 33#64) &&& 1#64
  change decide (L = 1#64) = hp
  rw [show L = hp.toUInt64.toBitVec by bv_decide]
  cases hp <;> decide

theorem mkData'_hasMVar (H : d < 2 ^ 24) : (mkData' h d hmv hp).hasMVar = hmv := by
  rw [mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H))]
  simp [Data.hasMVar, (· == ·), ← UInt64.toBitVec_inj]
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  let L := ((
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 32#64) &&& 1#64
  change decide (L = 1#64) = hmv
  rw [show L = hmv.toUInt64.toBitVec by bv_decide]
  cases hmv <;> decide

/-- The same three facts for the real `mkData`, via axiom 12.  (These duplicate
`Lean.Level.mkData_depth` / `mkData_hasParam` / `mkData_hasMVar` of
`Verify/Level.lean`; restated here so this file needs only `Verify/Axioms`.) -/
theorem mkData_depth (H : d < 2 ^ 24) : (mkData h d hmv hp).depth.toNat = d := by
  rw [mkData_eq H]; exact mkData'_depth H

theorem mkData_hasParam (H : d < 2 ^ 24) : (mkData h d hmv hp).hasParam = hp := by
  rw [mkData_eq H]; exact mkData'_hasParam H

theorem mkData_hasMVar (H : d < 2 ^ 24) : (mkData h d hmv hp).hasMVar = hmv := by
  rw [mkData_eq H]; exact mkData'_hasMVar H

/-! ## The generic reinterpretation of `Level.data`

`dataOf f` is `Lean.Level.data` (`Lean/Level.lean:98-106`) with the opaque
`mkData` replaced by `f`, clause for clause. -/

abbrev MkData := UInt64 → Nat → Bool → Bool → Level.Data

def dataOf (f : MkData) : Level → Level.Data
  | .zero => f 2221 0 false false
  | .mvar mvarId => f (mixHash 2237 <| hash mvarId) 0 true false
  | .param name => f (mixHash 2239 <| hash name) 0 false true
  | .succ u =>
    f (mixHash 2243 <| Data.hash (dataOf f u)) ((Data.depth (dataOf f u)).toNat + 1)
      (Data.hasMVar (dataOf f u)) (Data.hasParam (dataOf f u))
  | .max u v =>
    f (mixHash 2251 <| mixHash (Data.hash (dataOf f u)) (Data.hash (dataOf f v)))
      (Nat.max (Data.depth (dataOf f u)).toNat (Data.depth (dataOf f v)).toNat + 1)
      (Data.hasMVar (dataOf f u) || Data.hasMVar (dataOf f v))
      (Data.hasParam (dataOf f u) || Data.hasParam (dataOf f v))
  | .imax u v =>
    f (mixHash 2267 <| mixHash (Data.hash (dataOf f u)) (Data.hash (dataOf f v)))
      (Nat.max (Data.depth (dataOf f u)).toNat (Data.depth (dataOf f v)).toNat + 1)
      (Data.hasMVar (dataOf f u) || Data.hasMVar (dataOf f v))
      (Data.hasParam (dataOf f u) || Data.hasParam (dataOf f v))

/-! `dataOf` really is the upstream clause set: instantiated at the actual
`mkData` it gives back the actual `Level.data`, clause by clause, by `rfl`. -/

example : dataOf (fun h d mv hp => mkData h d mv hp) .zero = Level.data .zero := rfl
example (n : Name) :
    dataOf (fun h d mv hp => mkData h d mv hp) (.param n) = Level.data (.param n) := rfl
example (n : LMVarId) :
    dataOf (fun h d mv hp => mkData h d mv hp) (.mvar n) = Level.data (.mvar n) := rfl
example (u : Level) (h : dataOf (fun h d mv hp => mkData h d mv hp) u = Level.data u) :
    dataOf (fun h d mv hp => mkData h d mv hp) (.succ u) = Level.data (.succ u) := by
  rw [dataOf, h]; rfl
example (u v : Level)
    (hu : dataOf (fun h d mv hp => mkData h d mv hp) u = Level.data u)
    (hv : dataOf (fun h d mv hp => mkData h d mv hp) v = Level.data v) :
    dataOf (fun h d mv hp => mkData h d mv hp) (.max u v) = Level.data (.max u v) := by
  rw [dataOf, hu, hv]; rfl
example (u v : Level)
    (hu : dataOf (fun h d mv hp => mkData h d mv hp) u = Level.data u)
    (hv : dataOf (fun h d mv hp => mkData h d mv hp) v = Level.data v) :
    dataOf (fun h d mv hp => mkData h d mv hp) (.imax u v) = Level.data (.imax u v) := by
  rw [dataOf, hu, hv]; rfl

/-! ## 1. A model of `mkData_eq` + `hasParam_eq` + `hasMVar_eq`

Clamp the depth into range instead of panicking.  This agrees with `mkData'`
below `2 ^ 24`, so it validates `mkData_eq`, and it stores `hasMVar`/`hasParam`
faithfully at *every* depth, so it validates `hasParam_eq`/`hasMVar_eq`. -/

/-- Candidate interpretation of the opaque `Lean.Level.mkData`. -/
def mkDataM (h : UInt64) (d : Nat) (mv hp : Bool) : Level.Data :=
  mkData' h (min d (2 ^ 24 - 1)) mv hp

theorem mkDataM_lt : min d (2 ^ 24 - 1) < 2 ^ 24 := by omega

/-- The model validates axiom 12, `Level.mkData_eq`. -/
theorem mkDataM_validates_mkData_eq (H : d < 2 ^ 24) :
    mkDataM h d mv hp = mkData' h d mv hp := by
  rw [mkDataM, Nat.min_eq_left (by omega)]

theorem mkDataM_hasParam : (mkDataM h d mv hp).hasParam = hp :=
  mkData'_hasParam mkDataM_lt

theorem mkDataM_hasMVar : (mkDataM h d mv hp).hasMVar = mv :=
  mkData'_hasMVar mkDataM_lt

/-- The model validates axiom 13, `Level.hasParam_eq`. -/
theorem mkDataM_validates_hasParam_eq (l : Level) :
    (dataOf mkDataM l).hasParam = l.hasParam' := by
  induction l <;> simp [dataOf, hasParam', mkDataM_hasParam, *]

/-- The model validates axiom 14, `Level.hasMVar_eq`. -/
theorem mkDataM_validates_hasMVar_eq (l : Level) :
    (dataOf mkDataM l).hasMVar = l.hasMVar' := by
  induction l <;> simp [dataOf, hasMVar', mkDataM_hasMVar, *]

/-! ## 2. A model of `mkData_eq` that refutes `hasParam_eq` / `hasMVar_eq`

Return `0` out of range (this is exactly what the *old*, unconditional
`mkData_eq` forced, since `panic! _ : Level.Data` reduces to `default = 0`).
It still validates the *current* `mkData_eq`, which only speaks below `2 ^ 24`. -/

def mkDataZ (h : UInt64) (d : Nat) (mv hp : Bool) : Level.Data :=
  if d < 2 ^ 24 then mkData' h d mv hp else 0

/-- The second model also validates axiom 12, `Level.mkData_eq`. -/
theorem mkDataZ_validates_mkData_eq (H : d < 2 ^ 24) :
    mkDataZ h d mv hp = mkData' h d mv hp := if_pos H

/-- `succ^[n] (.param `x)`. -/
def L : Nat → Level
  | 0 => .param `x
  | n + 1 => .succ (L n)

/-- `succ^[n] (.mvar `x)`. -/
def M : Nat → Level
  | 0 => .mvar ⟨`x⟩
  | n + 1 => .succ (M n)

theorem L_hasParam' (n : Nat) : (L n).hasParam' = true := by
  induction n <;> simp [L, hasParam', *]

theorem M_hasMVar' (n : Nat) : (M n).hasMVar' = true := by
  induction n <;> simp [M, hasMVar', *]

theorem dataZ_L_depth (n : Nat) (h : n < 2 ^ 24) :
    (dataOf mkDataZ (L n)).depth.toNat = n := by
  induction n with
  | zero => rw [L, dataOf, mkDataZ, if_pos (by omega)]; exact mkData'_depth (by omega)
  | succ n ih => rw [L, dataOf, ih (by omega), mkDataZ, if_pos h]; exact mkData'_depth h

theorem dataZ_M_depth (n : Nat) (h : n < 2 ^ 24) :
    (dataOf mkDataZ (M n)).depth.toNat = n := by
  induction n with
  | zero => rw [M, dataOf, mkDataZ, if_pos (by omega)]; exact mkData'_depth (by omega)
  | succ n ih => rw [M, dataOf, ih (by omega), mkDataZ, if_pos h]; exact mkData'_depth h

/-- Once the cached depth has reached `2 ^ 24 - 1`, one more `succ` asks the
model for depth `2 ^ 24`, out of range, and it answers `0` — every cached bit,
`hasParam` and `hasMVar` included, is wiped. -/
theorem dataZ_succ_of_depth (l : Level) (h : (dataOf mkDataZ l).depth.toNat = 2 ^ 24 - 1) :
    dataOf mkDataZ (.succ l) = 0 := by
  rw [dataOf, h, mkDataZ, if_neg (by omega)]

/-- `Level.succ (L (2 ^ 24 - 1))` is `succ^[2 ^ 24] (.param `x)`: the cached
`hasParam` bit is `false` while `hasParam'` is `true`, so `hasParam_eq` fails in
this model. -/
theorem mkDataZ_refutes_hasParam_eq :
    (dataOf mkDataZ (.succ (L (2 ^ 24 - 1)))).hasParam
      ≠ (Level.succ (L (2 ^ 24 - 1))).hasParam' := by
  rw [dataZ_succ_of_depth _ (dataZ_L_depth _ (by omega)), hasParam', L_hasParam']
  decide

/-- Same for `hasMVar_eq`, on `succ^[2 ^ 24] (.mvar `x)`. -/
theorem mkDataZ_refutes_hasMVar_eq :
    (dataOf mkDataZ (.succ (M (2 ^ 24 - 1)))).hasMVar
      ≠ (Level.succ (M (2 ^ 24 - 1))).hasMVar' := by
  rw [dataZ_succ_of_depth _ (dataZ_M_depth _ (by omega)), hasMVar', M_hasMVar']
  decide

/-! ## 3. Both axioms become **theorems** under a depth side condition

§2 shows `hasParam_eq`/`hasMVar_eq` cannot be proved outright.  But the failure
is confined to levels whose *structural* depth reaches `2 ^ 24`, exactly the
levels the C runtime refuses to build.  Adding that side condition — the `Level`
analogue of `Expr.BVarBounded` — makes both **provable from `mkData_eq` alone**,
so axioms 13 and 14 can be retired from the whitelist.

Unlike `BVarBounded`, no per-subterm recursion is needed: `dep` is strictly
increasing on subterms, so the single top-level bound `dep l < 2 ^ 24` implies
it for every subterm. -/

/-- The structural (model) depth of a level: what `Level.depth` caches. -/
def dep : Level → Nat
  | .zero | .param _ | .mvar _ => 0
  | .succ u => dep u + 1
  | .max u v | .imax u v => Nat.max (dep u) (dep v) + 1

theorem data_zero : Level.data .zero = mkData 2221 0 false false := rfl
theorem data_param (n : Name) :
    Level.data (.param n) = mkData (mixHash 2239 <| hash n) 0 false true := rfl
theorem data_mvar (n : LMVarId) :
    Level.data (.mvar n) = mkData (mixHash 2237 <| hash n) 0 true false := rfl
theorem data_succ (u : Level) :
    Level.data (.succ u) = mkData (mixHash 2243 <| Data.hash (Level.data u))
      ((Data.depth (Level.data u)).toNat + 1)
      (Data.hasMVar (Level.data u)) (Data.hasParam (Level.data u)) := rfl
theorem data_max (u v : Level) :
    Level.data (.max u v) =
      mkData (mixHash 2251 <| mixHash (Data.hash (Level.data u)) (Data.hash (Level.data v)))
        (Nat.max (Data.depth (Level.data u)).toNat (Data.depth (Level.data v)).toNat + 1)
        (Data.hasMVar (Level.data u) || Data.hasMVar (Level.data v))
        (Data.hasParam (Level.data u) || Data.hasParam (Level.data v)) := rfl
theorem data_imax (u v : Level) :
    Level.data (.imax u v) =
      mkData (mixHash 2267 <| mixHash (Data.hash (Level.data u)) (Data.hash (Level.data v)))
        (Nat.max (Data.depth (Level.data u)).toNat (Data.depth (Level.data v)).toNat + 1)
        (Data.hasMVar (Level.data u) || Data.hasMVar (Level.data v))
        (Data.hasParam (Level.data u) || Data.hasParam (Level.data v)) := rfl

/-- The three cached fields are exact below depth `2 ^ 24`.  Uses axiom 12
(`Level.mkData_eq`) and nothing else. -/
theorem data_exact : ∀ (l : Level), dep l < 2 ^ 24 →
    (Level.data l).depth.toNat = dep l ∧
    (Level.data l).hasParam = l.hasParam' ∧
    (Level.data l).hasMVar = l.hasMVar' := by
  intro l
  induction l with
  | zero =>
    intro _
    rw [data_zero]
    exact ⟨mkData_depth (by omega), mkData_hasParam (by omega), mkData_hasMVar (by omega)⟩
  | param n =>
    intro _
    rw [data_param]
    exact ⟨mkData_depth (by omega), mkData_hasParam (by omega), mkData_hasMVar (by omega)⟩
  | mvar n =>
    intro _
    rw [data_mvar]
    exact ⟨mkData_depth (by omega), mkData_hasParam (by omega), mkData_hasMVar (by omega)⟩
  | succ u ih =>
    intro h
    rw [dep] at h
    obtain ⟨d1, p1, m1⟩ := ih (by omega)
    rw [data_succ, d1, p1, m1]
    refine ⟨?_, ?_, ?_⟩
    · rw [mkData_depth h]; rfl
    · rw [mkData_hasParam h]; rfl
    · rw [mkData_hasMVar h]; rfl
  | max u v ihu ihv =>
    intro h
    rw [dep] at h
    have hu : dep u ≤ Nat.max (dep u) (dep v) := Nat.le_max_left _ _
    have hv : dep v ≤ Nat.max (dep u) (dep v) := Nat.le_max_right _ _
    obtain ⟨d1, p1, m1⟩ := ihu (by omega)
    obtain ⟨d2, p2, m2⟩ := ihv (by omega)
    rw [data_max, d1, d2, p1, p2, m1, m2]
    refine ⟨?_, ?_, ?_⟩
    · rw [mkData_depth h]; rfl
    · rw [mkData_hasParam h]; rfl
    · rw [mkData_hasMVar h]; rfl
  | imax u v ihu ihv =>
    intro h
    rw [dep] at h
    have hu : dep u ≤ Nat.max (dep u) (dep v) := Nat.le_max_left _ _
    have hv : dep v ≤ Nat.max (dep u) (dep v) := Nat.le_max_right _ _
    obtain ⟨d1, p1, m1⟩ := ihu (by omega)
    obtain ⟨d2, p2, m2⟩ := ihv (by omega)
    rw [data_imax, d1, d2, p1, p2, m1, m2]
    refine ⟨?_, ?_, ?_⟩
    · rw [mkData_depth h]; rfl
    · rw [mkData_hasParam h]; rfl
    · rw [mkData_hasMVar h]; rfl

/-- **Axiom 13 as a theorem.** -/
theorem hasParam_eq_of_dep (l : Level) (h : dep l < 2 ^ 24) : l.hasParam = l.hasParam' :=
  (data_exact l h).2.1

/-- **Axiom 14 as a theorem.** -/
theorem hasMVar_eq_of_dep (l : Level) (h : dep l < 2 ^ 24) : l.hasMVar = l.hasMVar' :=
  (data_exact l h).2.2

/-- Bonus: `Level.depth` is exact under the same hypothesis. -/
theorem depth_eq_of_dep (l : Level) (h : dep l < 2 ^ 24) : l.depth = dep l :=
  (data_exact l h).1

#print axioms hasParam_eq_of_dep
#print axioms hasMVar_eq_of_dep

/-! ## Axiom hygiene: none of §0-§2 uses any repo axiom.
(`_native.bv_decide.ax_*` are the LRAT certificates of `bv_decide`, the same
ones `Verify/Level.lean` already emits for the identical bit lemmas.) -/

#print axioms mkDataM_validates_mkData_eq
#print axioms mkDataM_validates_hasParam_eq
#print axioms mkDataM_validates_hasMVar_eq
#print axioms mkDataZ_validates_mkData_eq
#print axioms mkDataZ_refutes_hasParam_eq
#print axioms mkDataZ_refutes_hasMVar_eq

end Lean4Lean.Tests.AxiomConsistency
