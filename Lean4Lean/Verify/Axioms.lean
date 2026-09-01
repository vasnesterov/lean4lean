import Batteries.Tactic.OpenPrivate
import Lean4Lean.Std.Basic
import Lean4Lean.Std.NodupKeys
import Lean4Lean.Std.TreeMap
import Lean4Lean.PtrEq

namespace Std.TreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap α β cmp}

/-- Was an axiom (https://github.com/leanprover/lean4/issues/12798); upstream has since
added `Std.DTreeMap.Internal.Impl.all_eq_all_toListModel`, which proves it.
See `docs/axiom-audit.md` §8. -/
theorem all_eq_all_toList {p : α → β → Bool} :
    t.all p = t.toList.all fun a => p a.1 a.2 := by
  simp [TreeMap.all, TreeMap.toList, DTreeMap.all, DTreeMap.Const.toList,
    Std.DTreeMap.Internal.Impl.all_eq_all_toListModel,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map, Function.comp_def]

/-- Was an axiom (https://github.com/leanprover/lean4/issues/12798); upstream proved only
the `all` form, so this uses the mirror lemma `Impl.any_eq_any_toListModel` in
`Lean4Lean/Std/TreeMap.lean`. See `docs/axiom-audit.md` §8. -/
theorem any_eq_any_toList {p : α → β → Bool} :
    t.any p = t.toList.any fun a => p a.1 a.2 := by
  simp [TreeMap.any, TreeMap.toList, DTreeMap.any, DTreeMap.Const.toList,
    Std.DTreeMap.Internal.Impl.any_eq_any_toListModel,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map, Function.comp_def]

end Std.TreeMap

open scoped _root_.List
namespace Lean

noncomputable def PersistentArrayNode.toList' : PersistentArrayNode α → List α :=
  PersistentArrayNode.rec
    (motive_1 := fun _ => List α) (motive_2 := fun _ => List α) (motive_3 := fun _ => List α)
    (node := fun _ => id) (leaf := (·.toList)) (fun _ => id) [] (fun _ _ a b => a ++ b)

namespace PersistentArray

inductive WF : PersistentArray α → Prop where
  | empty : WF .empty
  | push : WF arr → WF (arr.push x)

noncomputable def toList' (arr : PersistentArray α) : List α :=
  arr.root.toList' ++ arr.tail.toList

@[simp] theorem toList'_empty : (.empty : PersistentArray α).toList' = [] := rfl

@[simp] theorem size_empty : (.empty : PersistentArray α).size = 0 := rfl

@[simp] theorem size_push {α} (arr : PersistentArray α) (x : α) :
    (arr.push x).size = arr.size + 1 := by
  simp [push]; split <;> [rfl; (simp [mkNewTail]; split <;> rfl)]

end PersistentArray

namespace PersistentHashMap

noncomputable def Node.toList' : Node α β → List (α × β) :=
  Node.rec
    (motive_1 := fun _ => List (α × β)) (motive_2 := fun _ => List (α × β))
    (motive_3 := fun _ => List (α × β)) (motive_4 := fun _ => List (α × β))
    (entries := fun _ => id) (collision := fun ks xs _ => ks.toList.zip xs.toList)
    (mk := fun _ => id)
    (nil := []) (cons := fun _ _ l1 l2 => l1 ++ l2)
    (entry := fun a b => [(a, b)]) (ref := fun _ => id) (null := [])

noncomputable def toList' [BEq α] [Hashable α] (m : PersistentHashMap α β) :
    List (α × β) := m.root.toList'

inductive WF [BEq α] [Hashable α] : PersistentHashMap α β → Prop where
  | empty : WF .empty
  | insert : WF m → WF (m.insert a b)

end PersistentHashMap

namespace Syntax

def structEq' : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node _ k args, .node _ k' args' => k == k' &&
    (args.size == args'.size &&
      (args.toList.attach.zip args'.toList.attach).all fun (a, b) =>
        have := Array.mem_toList_iff.1 a.2; structEq' a b)
  | .atom _ val, .atom _ val' => val == val'
  | .ident _ rawVal val preresolved, Syntax.ident _ rawVal' val' preresolved' =>
    rawVal == rawVal' && val == val' && preresolved == preresolved'
  | _, _ => false
termination_by x _ => x

theorem structEq'_node :
    structEq' (.node _x k args) (.node _y k' args') = (k == k' && args.isEqv args' structEq') := by
  unfold structEq'; simp; congr 1
  by_cases h : args.size = args'.size <;> [simp [h]; simp [Array.isEqv, h]]
  let ⟨args⟩ := args; let ⟨args'⟩ := args'; simp at h ⊢
  have' : ((args.attach.map (·.1)).zip (args'.attach.map (·.1))).all
      (fun x => x.1.structEq' x.2) = _ := by
    simp only [List.zip_map_left, List.zip_map_right]; simp [Function.comp_def]; rfl
  rw [← this]; simp; clear this
  induction args generalizing args' <;> cases args' <;> simp at h <;> simp [List.isEqv, *]

/-- This is a `partial` because it is not obviously terminating. The `structEq'_node` theorem
shows that a definition with the same clauses can be defined manually. -/
@[simp] axiom structEq_eq : structEq a b = structEq' a b
end Syntax

namespace Level

/-!
### A total copy of `Lean.Level.normalize`

`Lean.Level.normalize` and four of its helpers are `partial def`s, so they are opaque and nothing
can be proved about them. The `Total` namespace below is a clause-by-clause copy of
[Lean's `Lean/Level.lean`](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Level.lean#L319-L404),
under the same names, with the termination proofs supplied. That makes `normalize_eq` below a
purely syntactic trust assumption, checkable by reading the two definitions side by side;
`Lean4Lean.Tests.LevelStd` also checks it on a finite corpus of levels.
-/
namespace Total

/-- The structural size of a level, used as the termination measure for `normalize`. -/
def size : Level → Nat
  | .zero | .param _ | .mvar _ => 1
  | .succ l => size l + 1
  | .max l₁ l₂ => size l₁ + size l₂ + 1
  | .imax l₁ l₂ => size l₁ + size l₂ + 2

/-- Secondary termination measure for `normalize`: in the `imax` branch it recurses on
`mkLevelMax l₁ l₂`, which has the same `size` as `imax l₁ l₂` but a smaller `tag`. -/
private def tag (l : Level) : Nat :=
  match l.getLevelOffset with
  | .imax .. => 1
  | _ => 0

private theorem tag_le (l : Level) : tag l ≤ 1 := by unfold tag; split <;> omega

theorem one_le_size (l : Level) : 1 ≤ size l := by cases l <;> simp [size]

private theorem getOffsetAux_eq (l : Level) (k) : getOffsetAux l k = getOffsetAux l 0 + k := by
  induction l generalizing k with
  | succ l ih => rw [getOffsetAux, ih (k+1), getOffsetAux, ih 1]; omega
  | _ => simp [getOffsetAux]

theorem size_getLevelOffset (l : Level) :
    size l.getLevelOffset + l.getOffset = size l := by
  simp only [getOffset]
  induction l with | succ l ih => ?_ | _ => rfl
  show size l.getLevelOffset + getOffsetAux l 1 = size l + 1
  rw [getOffsetAux_eq l 1]; omega

end Total
open private accMax mkIMaxAux mkMaxAux skipExplicit isExplicitSubsumedAux
  isExplicitSubsumed from Lean.Level

def Total.mkMaxAux (lvls : Array Level) (extraK : Nat) (i : Nat)
    (prev : Level) (prevK : Nat) (result : Level) : Level :=
  if h : i < lvls.size then
    let lvl   := lvls[i]
    let curr  := lvl.getLevelOffset
    let currK := lvl.getOffset
    if curr == prev then mkMaxAux lvls extraK (i+1) curr currK result
    else mkMaxAux lvls extraK (i+1) curr currK (accMax result prev (extraK + prevK))
  else accMax result prev (extraK + prevK)

/-- Patch for `partial def Lean.Level.mkMaxAux`. -/
@[simp] axiom mkMaxAux_eq : mkMaxAux = Total.mkMaxAux

def Total.skipExplicit (lvls : Array Level) (i : Nat) : Nat :=
  if h : i < lvls.size then
    if lvls[i].getLevelOffset.isZero then skipExplicit lvls (i+1) else i
  else i

/-- Patch for `partial def Lean.Level.skipExplicit`. -/
@[simp] axiom skipExplicit_eq : skipExplicit = Total.skipExplicit

def Total.isExplicitSubsumedAux (lvls : Array Level) (maxExplicit : Nat) (i : Nat) : Bool :=
  if h : i < lvls.size then
    if lvls[i].getOffset ≥ maxExplicit then true
    else isExplicitSubsumedAux lvls maxExplicit (i+1)
  else false

/-- Patch for `partial def Lean.Level.isExplicitSubsumedAux`. -/
@[simp] axiom isExplicitSubsumedAux_eq : isExplicitSubsumedAux = Total.isExplicitSubsumedAux

mutual

/-- A total copy of `partial def Lean.Level.normalize`. -/
def Total.normalize (l : Level) : Level :=
  if isAlreadyNormalizedCheap l then l else
  let k := l.getOffset
  match h : l.getLevelOffset with
  | .max l₁ l₂ =>
    let lvls  := getMaxArgsAux l₁ false #[]
    let lvls  := getMaxArgsAux l₂ false lvls
    let lvls  := lvls.qsort normLt
    let firstNonExplicit := skipExplicit lvls 0
    let i := if isExplicitSubsumed lvls firstNonExplicit then firstNonExplicit
              else firstNonExplicit - 1
    let lvl₁  := lvls[i]!
    let prev  := lvl₁.getLevelOffset
    let prevK := lvl₁.getOffset
    mkMaxAux lvls k (i+1) prev prevK Level.zero
  | .imax l₁ l₂ =>
    if l₂.isNeverZero then addOffset (normalize (mkLevelMax l₁ l₂)) k
    else addOffset (mkIMaxAux (normalize l₁) (normalize l₂)) k
  | _ => unreachable!
termination_by (1, 3 * size l + tag l)
decreasing_by all_goals
  refine .right _ ?_
  have hsz := size_getLevelOffset l
  rw [h] at hsz
  simp only [size] at hsz
  have := one_le_size l₁
  have := one_le_size l₂
  have := tag_le l₁
  have := tag_le l₂
  first
  | omega
  | have ht : tag l = 1 := by simp [tag, h]
    have e1 : size (mkLevelMax l₁ l₂) = size l₁ + size l₂ + 1 := rfl
    have e2 : tag (mkLevelMax l₁ l₂) = 0 := rfl
    omega

def Total.getMaxArgsAux : Level → Bool → Array Level → Array Level
  | .max l₁ l₂, norm, lvls => getMaxArgsAux l₂ norm (getMaxArgsAux l₁ norm lvls)
  | l, false, lvls => getMaxArgsAux (normalize l) true lvls
  | l, true, lvls => lvls.push l
termination_by l b => (if b then 0 else 1, 3 * size l + tag l + 1)
decreasing_by
  any_goals cases norm
  any_goals first | refine .right _ ?_ | exact .left _ _ (by decide)
  all_goals first
  | omega
  | have e1 : size (Level.max l₁ l₂) = size l₁ + size l₂ + 1 := rfl
    have e2 : tag (Level.max l₁ l₂) = 0 := rfl
    have := one_le_size l₁
    have := one_le_size l₂
    have := tag_le l₁
    have := tag_le l₂
    omega

end

/-- `Lean.Level.normalize` is a `partial def`, so it is opaque;
`Total.normalize` above is a total copy of it. -/
axiom normalize_eq : normalize = Total.normalize

def mkData' (h : UInt64) (depth : Nat := 0) (hasMVar hasParam : Bool := false) : Level.Data :=
  if depth > Nat.pow 2 24 - 1 then panic! "universe level depth is too big"
  else
    h.toUInt32.toUInt64 +
    hasMVar.toUInt64.shiftLeft 32 +
    hasParam.toUInt64.shiftLeft 33 +
    depth.toUInt64.shiftLeft 40

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead.

The hypothesis `H : d < 2 ^ 24` is essential. The previous unconditional form
`@mkData = @mkData'` was **false, and jointly inconsistent with `hasParam_eq` /
`hasMVar_eq`**: for `d ≥ 2 ^ 24` the C function `lean_level_mk_data` calls
`lean_internal_panic` and *aborts the process*, whereas the Lean-side
`panic! ... : Level.Data` reduces to `default = 0`. Asserting the equation on
that branch therefore claims a return value the implementation never produces,
and makes e.g. `(Level.succ^[2 ^ 24] (.param `x)).hasParam` provably `false`
while `hasParam'` is `true`. See `docs/axiom-audit.md` §4 (and §5.4). -/
axiom mkData_eq {h : UInt64} {d : Nat} {mv hp : Bool} (H : d < 2 ^ 24) :
    mkData h d mv hp = mkData' h d mv hp

def hasParam' : Level → Bool
  | .param .. => true
  | .zero | .mvar .. => false
  | .succ l => l.hasParam'
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.hasParam' || l₂.hasParam'

/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
@[simp] axiom hasParam_eq (l : Level) : l.hasParam = l.hasParam'

def hasMVar' : Level → Bool
  | .mvar .. => true
  | .zero | .param .. => false
  | .succ l => l.hasMVar'
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.hasMVar' || l₂.hasMVar'

/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
@[simp] axiom hasMVar_eq (l : Level) : l.hasMVar = l.hasMVar'

/-- This is because the `BEq` instance is implemented in C++ -/
@[instance] axiom instLawfulBEqLevel : LawfulBEq Level

@[inline] private def mkIMaxCore (u v : Level) (elseK : Unit → Level) : Level :=
  if v.isNeverZero then mkLevelMax' u v
  else if v.isZero then v
  else if u.isZero then v
  else if u == v then u
  else elseK ()

open private mkLevelIMaxCore from Lean.Level in
/-- `mkIMaxCore` is a verbatim copy of the private `Lean.Level.mkLevelIMaxCore`,
so this holds by `rfl` and need not be assumed.

It was previously an axiom, and a *false* one: the model carried an extra
`|| u matches .succ .zero` disjunct in the third branch which upstream has in
neither `v4.33.0-rc2` nor master. Since `mkLevelIMaxCore` is a plain
`private def` rather than an `opaque`, the equation is decidable, and the axiom
proved `False` on its own -- see `docs/axiom-audit.md`. -/
@[simp] theorem mkLevelIMaxCore_eq : mkLevelIMaxCore = mkIMaxCore := rfl

end Level

namespace Expr

def mkData'
    (h : UInt64) (looseBVarRange : Nat := 0) (approxDepth : UInt32 := 0)
    (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool := false)
    : Expr.Data :=
  let approxDepth : UInt8 := if approxDepth > 255 then 255 else approxDepth.toUInt8
  assert! (looseBVarRange ≤ Nat.pow 2 20 - 1)
  h.toUInt32.toUInt64 +
  approxDepth.toUInt64.shiftLeft 32 +
  hasFVar.toUInt64.shiftLeft 40 +
  hasExprMVar.toUInt64.shiftLeft 41 +
  hasLevelMVar.toUInt64.shiftLeft 42 +
  hasLevelParam.toUInt64.shiftLeft 43 +
  looseBVarRange.toUInt64.shiftLeft 44

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead.

The hypothesis `H : br ≤ 2 ^ 20 - 1` is essential. The previous unconditional
form `@mkData = @mkData'` was **false**: for `looseBVarRange > 2 ^ 20 - 1` the C
function `lean_expr_mk_data` calls `lean_internal_panic` and *aborts the
process*, whereas the `assert!` in `mkData'` elaborates to
`if _ then _ else panic! _` and `panic! ... : Expr.Data` reduces to
`default = 0`. Asserting the equation on that branch claims a return value the
implementation never produces. See `docs/axiom-audit.md` §4 (and §5.4). -/
axiom mkData_eq {h : UInt64} {br : Nat} {d : UInt32} {fv ev lv lp : Bool}
    (H : br ≤ 2 ^ 20 - 1) :
    mkData h br d fv ev lv lp = mkData' h br d fv ev lv lp

@[inline] def mkAppData' (fData : Data) (aData : Data) : Data :=
  let depth          := max fData.approxDepth.toUInt16 aData.approxDepth.toUInt16 + 1
  let approxDepth    := if depth > 255 then 255 else depth.toUInt8
  let looseBVarRange := max fData.looseBVarRange aData.looseBVarRange
  let hash           := mixHash fData aData
  let fData : UInt64 := fData
  let aData : UInt64 := aData
  assert! looseBVarRange ≤ (Nat.pow 2 20 - 1).toUInt32
  (fData ||| aData) &&& (15 : UInt64) <<< (40 : UInt64) |||
  hash.toUInt32.toUInt64 |||
  approxDepth.toUInt64 <<< (32 : UInt64) |||
  looseBVarRange.toUInt64 <<< (44 : UInt64)

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead -/
axiom mkAppData_eq : @mkAppData = @mkAppData'

def looseBVarRange' : Expr → Nat
  | .bvar i => i + 1
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => 0
  | .mdata _ e
  | .proj _ _ e => e.looseBVarRange'
  | .app e1 e2 => max e1.looseBVarRange' e2.looseBVarRange'
  | .lam _ e1 e2 _
  | .forallE _ e1 e2 _ => max e1.looseBVarRange' (e2.looseBVarRange' - 1)
  | .letE _ e1 e2 e3 _ => max (max e1.looseBVarRange' e2.looseBVarRange') (e3.looseBVarRange' - 1)

/-- Every `bvar` index occurring in `e` fits the 20-bit `looseBVarRange` field,
so the cached range is exact for `e` and for every subterm of `e`.

`.lam`/`.forallE`/`.letE` need only their children checked: the parent's own
`mkData` argument is a `max` of quantities bounded by the children's ranges. -/
def BVarBounded : Expr → Prop
  | .bvar i => i + 1 ≤ 2^20 - 1
  | .mdata _ b
  | .proj _ _ b => b.BVarBounded
  | .app f a => f.BVarBounded ∧ a.BVarBounded
  | .lam _ t b _
  | .forallE _ t b _ => t.BVarBounded ∧ b.BVarBounded
  | .letE _ t v b _ => t.BVarBounded ∧ v.BVarBounded ∧ b.BVarBounded
  | _ => True

/-! ### `looseBVarRange_eq` is proved, not assumed

This was an axiom until `docs/axiom-audit.md` §13. It is **derivable** from
`mkData_eq` and `mkAppData_eq` under the side condition it already carried, so
it is now a theorem with an unchanged statement -- no consumer had to change.

The `BVarBounded` side condition is **required**, absolutely and not just
relative to some interpretation of the packing function: `Expr.looseBVarRange`
is a read of a 20-bit field (`Expr.Data.looseBVarRange c = (c >>> 44).toUInt32`)
so it is `< 2^20` whatever `mkData` returns, whereas `looseBVarRange'` is
unbounded -- `(Expr.bvar 1048575).looseBVarRange' = 2^20`. Without the
hypothesis the statement proved `False` on its own (§3.1); the refutation is
preserved as a live theorem, `not_looseBVarRange_eq_unconditional` in
`Lean4Lean/Tests/AxiomConsistencyExpr.lean`, so it cannot be re-broken silently.
Upstream refuses to construct such a term at all (`lean_expr_mk_data` panics
with "too many bound variables" when the range exceeds `1048575`), which is also
why the RHS must *not* be patched to return `0` out of range: the C function
aborts, it does not keep going with `0`.

A bound on the top-level range does not suffice -- the field is computed
bottom-up, so every subterm's `mkData` call must be in range; hence the
per-subterm `BVarBounded`. Of its clauses only `bvar` does any work: every other
`mkData` call in the `Expr.data` computed field passes an argument built from
`looseBVarRange` *field reads*, which `dataLooseBVarRange_lt` below bounds
unconditionally. The recursion exists only to reach the `bvar` leaves.

The proofs deliberately avoid `bv_decide`, which discharges its LRAT certificate
by compiling and running the checker and then minting a fresh
`..._native.bv_decide.ax_N` axiom from the runtime result -- the kernel never
sees a proof (§12.5). `simp` + `omega` over `Nat` suffices. These are private
duplicates of facts `Verify/Expr.lean` also proves, rather than a shared home,
because a shared file would have to import this frozen one. -/

section LooseBVarRangeEq
set_option allowUnsafeReducibility true
attribute [local reducible] Data

private theorem shr (a b : UInt64) : a.shiftRight b = a >>> b := rfl
private theorem shl (a b : UInt64) : a.shiftLeft b = a <<< b := rfl

private theorem add64 {x y : UInt64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b)
    (hab : a + b < 2 ^ 64) : (x + y).toNat = a + b := by
  rw [UInt64.toNat_add, hx, hy]; omega

private theorem shl64 {x n : UInt64} {a k : Nat} (hx : x.toNat = a) (hn : n.toNat % 64 = k)
    (hb : a * 2 ^ k < 2 ^ 64) : (x.shiftLeft n).toNat = a * 2 ^ k := by
  rw [shl, UInt64.toNat_shiftLeft, hx, hn, Nat.shiftLeft_eq]; omega

private theorem btl (b : Bool) : b.toUInt64.toNat < 2 := by cases b <;> simp [Bool.toUInt64]

/-- The cached `looseBVarRange` is a read of a 20-bit field, so it is `< 2 ^ 20`
whatever `mkData` returns. Axiom-free: this is the provable property that makes
the unconditional form refutable, and that makes `mkAppData'`'s `assert!`
unreachable. -/
private theorem dataLooseBVarRange_lt (c : Data) : c.looseBVarRange.toNat < 2 ^ 20 := by
  have h : (c : UInt64).toNat < 2 ^ 64 := UInt64.toNat_lt_size c
  simp only [Data.looseBVarRange, shr, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  omega

private theorem u32max_toNat (x y : UInt32) : (max x y).toNat = max x.toNat y.toNat := by
  simp only [Max.max]
  split <;> rename_i h <;> rw [UInt32.le_iff_toNat_le] at h <;> split <;> omega

/-- Field read of a value packed as `lo + br * 2 ^ 44` with `lo` below the field. -/
private theorem field44 {c : UInt64} {lo br : Nat} (hlo : lo < 2 ^ 44) (hbr : br < 2 ^ 20)
    (hc : c.toNat = lo + br * 2 ^ 44) : (Data.looseBVarRange c).toNat = br := by
  simp only [Data.looseBVarRange, shr, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.shiftRight_eq_div_pow, hc]
  omega

/-- Field read of a value assembled by `|||`. `>>>` distributes over `|||`, so
the three sub-44 pieces vanish and the field survives. -/
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

private theorem mkData'_lbr {h : UInt64} {br : Nat} {d : UInt32} {fv ev lv lp : Bool}
    (H : br ≤ 2 ^ 20 - 1) : (mkData' h br d fv ev lv lp).looseBVarRange.toNat = br := by
  obtain ⟨lo, hlo, hc⟩ := mkData'_pack (h := h) (d := d) (fv := fv) (ev := ev) (lv := lv)
    (lp := lp) H
  exact field44 hlo (by omega) hc

set_option maxHeartbeats 800000 in
private theorem mkAppData'_lbr (f a : Data) :
    (mkAppData' f a).looseBVarRange.toNat
      = max f.looseBVarRange.toNat a.looseBVarRange.toNat := by
  have hf := dataLooseBVarRange_lt f; have ha := dataLooseBVarRange_lt a
  have hass : max f.looseBVarRange a.looseBVarRange ≤ (Nat.pow 2 20 - 1).toUInt32 := by
    rw [UInt32.le_iff_toNat_le, u32max_toNat]; simp; omega
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
  · rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, u32max_toNat]
    simp only [UInt64.toNat_ofNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    omega

private theorem mkData_lbr {h : UInt64} {br : Nat} {d : UInt32} {fv ev lv lp : Bool}
    (H : br ≤ 2 ^ 20 - 1) : (mkData h br d fv ev lv lp).looseBVarRange.toNat = br := by
  rw [mkData_eq H]; exact mkData'_lbr H

private theorem mkAppData_lbr (f a : Data) :
    (mkAppData f a).looseBVarRange.toNat
      = max f.looseBVarRange.toNat a.looseBVarRange.toNat := by
  rw [mkAppData_eq]; exact mkAppData'_lbr f a

private theorem le_of_field (c : Data) : c.looseBVarRange.toNat ≤ 2 ^ 20 - 1 := by
  have := dataLooseBVarRange_lt c; omega

set_option maxHeartbeats 1000000 in
private theorem data_lbr : ∀ (e : Expr), e.BVarBounded →
    e.data.looseBVarRange.toNat = e.looseBVarRange' := by
  intro e
  induction e with
  | bvar i => intro h; exact mkData_lbr h
  | fvar _ => intro _; exact mkData_lbr (by omega)
  | mvar _ => intro _; exact mkData_lbr (by omega)
  | sort _ => intro _; exact mkData_lbr (by omega)
  | const _n _us => intro _; exact mkData_lbr (by omega)
  | lit _ => intro _; exact mkData_lbr (by omega)
  | mdata _ b ih => intro h; exact (mkData_lbr (le_of_field b.data)).trans (ih h)
  | proj _ _ b ih => intro h; exact (mkData_lbr (le_of_field b.data)).trans (ih h)
  | app f a ihf iha =>
    intro h; exact (mkAppData_lbr f.data a.data).trans (by rw [ihf h.1, iha h.2]; rfl)
  | lam _ t b _ iht ihb =>
    intro h
    have hb : max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1) ≤ 2 ^ 20 - 1 := by
      have := dataLooseBVarRange_lt t.data; have := dataLooseBVarRange_lt b.data; omega
    exact (mkData_lbr hb).trans (by rw [iht h.1, ihb h.2]; rfl)
  | forallE _ t b _ iht ihb =>
    intro h
    have hb : max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1) ≤ 2 ^ 20 - 1 := by
      have := dataLooseBVarRange_lt t.data; have := dataLooseBVarRange_lt b.data; omega
    exact (mkData_lbr hb).trans (by rw [iht h.1, ihb h.2]; rfl)
  | letE _ t v b _ iht ihv ihb =>
    intro h
    have hb : max (max t.data.looseBVarRange.toNat v.data.looseBVarRange.toNat)
        (b.data.looseBVarRange.toNat - 1) ≤ 2 ^ 20 - 1 := by
      have := dataLooseBVarRange_lt t.data; have := dataLooseBVarRange_lt v.data
      have := dataLooseBVarRange_lt b.data; omega
    exact (mkData_lbr hb).trans (by rw [iht h.1, ihv h.2.1, ihb h.2.2]; rfl)

/-- The cached `looseBVarRange` is exact on every `BVarBounded` term.

Formerly an axiom; see `docs/axiom-audit.md` §13. Proved from `mkData_eq` and
`mkAppData_eq`, which are the only assumptions in its cone. -/
@[simp] theorem looseBVarRange_eq (e : Expr) (h : e.BVarBounded) :
    e.looseBVarRange = e.looseBVarRange' := data_lbr e h

end LooseBVarRangeEq

/-- The side condition on `looseBVarRange_eq` is strong enough to block the
refutation in `docs/axiom-audit.md` §3.1: under `BVarBounded` the model range
obeys the same `≤ 2^20 - 1` bound that `Expr.looseBVarRange_le` proves for the
packed field, so the two sides are no longer forced apart. -/
theorem BVarBounded.looseBVarRange'_le :
    ∀ {e : Expr}, e.BVarBounded → e.looseBVarRange' ≤ 2^20 - 1 := by
  intro e; induction e with
  | bvar i => exact fun h => h
  | mdata _ _ ih => exact ih
  | proj _ _ _ ih => exact ih
  | app _ _ ih1 ih2 =>
    intro h; have h1 := ih1 h.1; have h2 := ih2 h.2
    simp only [looseBVarRange']; omega
  | lam _ _ _ _ ih1 ih2 =>
    intro h; have h1 := ih1 h.1; have h2 := ih2 h.2
    simp only [looseBVarRange']; omega
  | forallE _ _ _ _ ih1 ih2 =>
    intro h; have h1 := ih1 h.1; have h2 := ih2 h.2
    simp only [looseBVarRange']; omega
  | letE _ _ _ _ _ ih1 ih2 ih3 =>
    intro h; have h1 := ih1 h.1; have h2 := ih2 h.2.1; have h3 := ih3 h.2.2
    simp only [looseBVarRange']; omega
  | _ => exact fun _ => Nat.zero_le _

def liftLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  match e with
  | .bvar i => .bvar (if i < s then i else i + d)
  | .mdata m e => .mdata m (liftLooseBVars' e s d)
  | .proj n i e => .proj n i (liftLooseBVars' e s d)
  | .app f a => .app (liftLooseBVars' f s d) (liftLooseBVars' a s d)
  | .lam n t b bi => .lam n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (liftLooseBVars' t s d) (liftLooseBVars' v s d) (liftLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

/-!
`liftLooseBVars_eq : e.liftLooseBVars s d = e.liftLooseBVars' s d` used to sit here.
It was **deleted**, not weakened, because it was **false** and had **no consumers**.

*False.* `lean_expr_lift_loose_bvars` (`kernel/expr.cpp`) begins

```c
if (!lean_is_scalar(s) || !lean_is_scalar(d)) { lean_inc(e); return e; }
```

a bignum guard that fires at `2^63` (`LEAN_MAX_SMALL_NAT = SIZE_MAX >> 1`) and
returns `e` *unchanged* — it does not panic. At `e := .bvar 0, s := 0, d := 2^63`
the compiled function returns `.bvar 0` (checked by `#eval`) while the model
gives `.bvar (2^63)` (checked by kernel reduction). The call completes and the
input is an ordinary literal; only the model's *output* is not runtime
constructible, which is why the two halves need different instruments.

*No consumers.* An axiom-cone scan over every non-internal `Lean4Lean.*`
declaration found **0** dependents — the checker never calls
`Expr.liftLooseBVars` at all. A grep could not have established this: the axiom
was `@[simp]`, so it had no explicit call sites either way.

The model `liftLooseBVars'` above **stays**: a constant-dependency scan gives it
29 direct users, including `instantiate1'`, the model behind `instantiate1_eq`.
It is the axiom that was false, not the model.

See `docs/axiom-audit.md` §11.2.
-/

def lowerLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  if s < d then e else
  match e with
  | .bvar i => .bvar (if i < s then i else i - d)
  | .mdata m e => .mdata m (lowerLooseBVars' e s d)
  | .proj n i e => .proj n i (lowerLooseBVars' e s d)
  | .app f a => .app (lowerLooseBVars' f s d) (lowerLooseBVars' a s d)
  | .lam n t b bi => .lam n (lowerLooseBVars' t s d) (lowerLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (lowerLooseBVars' t s d) (lowerLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (lowerLooseBVars' t s d) (lowerLooseBVars' v s d) (lowerLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

/-- This could be an `@[implemented_by]` -/
@[simp] axiom lowerLooseBVars_eq (e : Expr) (s d) : e.lowerLooseBVars s d = e.lowerLooseBVars' s d

def instantiate1' (e : Expr) (subst : Expr) (d := 0) : Expr :=
  match e with
  | .bvar i => if i < d then e else if i = d then subst.liftLooseBVars' 0 d else .bvar (i - 1)
  | .mdata m e => .mdata m (instantiate1' e subst d)
  | .proj s i e => .proj s i (instantiate1' e subst d)
  | .app f a => .app (instantiate1' f subst d) (instantiate1' a subst d)
  | .lam n t b bi => .lam n (instantiate1' t subst d) (instantiate1' b subst (d+1)) bi
  | .forallE n t b bi => .forallE n (instantiate1' t subst d) (instantiate1' b subst (d+1)) bi
  | .letE n t v b bi =>
    .letE n (instantiate1' t subst d) (instantiate1' v subst d) (instantiate1' b subst (d+1)) bi
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => e

/-- This could be an `@[implemented_by]` -/
@[simp] axiom instantiate1_eq (e : Expr) (subst) : e.instantiate1 subst = e.instantiate1' subst

@[simp] def instantiateList : Expr → List Expr → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => instantiateList (instantiate1' e a k) as k

/--
This could be an `@[implemented_by]`, but only under the closedness hypothesis `h`.

The previous statement of this axiom (without `h`) was **false**: the real
`Expr.instantiate` is *simultaneous* — a loose `bvar i` at binding depth `d` is
replaced by `liftLooseBVars (subst[i-d]) 0 d` and the loose bvars *inside* the
substituted term are neither re-substituted nor renumbered — whereas
`instantiateList` is *sequential*, re-entering the result of each step.

Counterexample: for `e = .bvar 0` and `subst = #[.bvar 0, .sort .zero]`,
`e.instantiate subst = .bvar 0` but `e.instantiateList subst.toList = .sort .zero`.

Requiring every substituend to be closed makes the two agree.
See `docs/axiom-audit.md` §5.1.
-/
@[simp] axiom instantiate_eq (e : Expr) (subst : Array Expr)
    (h : ∀ a ∈ subst, a.looseBVarRange' = 0) :
    e.instantiate subst = e.instantiateList subst.toList

/-- This could be an `@[implemented_by]` -/
@[simp] axiom instantiateRev_eq (e : Expr) (subst) :
    e.instantiateRev subst = e.instantiate subst.reverse

/-- This could be an `@[implemented_by]`.

The hypotheses `h₁ : start ≤ stop` and `h₂ : stop ≤ subst.size` are essential.
The previous unconditional form was **false**: `lean_expr_instantiate_range`
(`kernel/instantiate.cpp:82`) starts with
`if (b > e || e > sz) lean_internal_panic(...)` and so *aborts the process*
outside the range, whereas `Array.extract` clamps and the right-hand side
returns a value. Inside the range the two sides agree exactly.
See `docs/axiom-audit.md` §6. -/
@[simp] axiom instantiateRange_eq (e : Expr) (subst)
    (h₁ : start ≤ stop) (h₂ : stop ≤ subst.size) :
    e.instantiateRange start stop subst = e.instantiate (subst.extract start stop)

/-- This could be an `@[implemented_by]`.

The hypotheses `h₁ : start ≤ stop` and `h₂ : stop ≤ subst.size` are essential;
see `instantiateRange_eq` above and `docs/axiom-audit.md` §6. Out of range the
C wrapper calls `lean_internal_panic` and aborts, while `Array.extract` clamps. -/
@[simp] axiom instantiateRevRange_eq (e : Expr) (subst)
    (h₁ : start ≤ stop) (h₂ : stop ≤ subst.size) :
    e.instantiateRevRange start stop subst = e.instantiateRev (subst.extract start stop)

def abstract1 (v : FVarId) : Expr → (k :_:= 0) → Expr
  | .bvar i, d => .bvar (if i < d then i else i + 1)
  | e@(.fvar v'), d => if v == v' then .bvar d else e
  | .mdata m e, d => .mdata m (abstract1 v e d)
  | .proj s i e, d => .proj s i (abstract1 v e d)
  | .app f a, d => .app (abstract1 v f d) (abstract1 v a d)
  | .lam n t b bi, d => .lam n (abstract1 v t d) (abstract1 v b (d+1)) bi
  | .forallE n t b bi, d => .forallE n (abstract1 v t d) (abstract1 v b (d+1)) bi
  | .letE n t val b bi, d =>
    .letE n (abstract1 v t d) (abstract1 v val d) (abstract1 v b (d+1)) bi
  | e@(.const ..), _
  | e@(.sort _), _
  | e@(.mvar _), _
  | e@(.lit _), _ => e

@[simp] def abstractList : Expr → List FVarId → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => abstractList (abstract1 a e k) as k

/--
This could be an `@[implemented_by]`, but only under the hypotheses `he` and `hx`.

The previous statement of this axiom (without `he`, `hx`) was **false**, for two
independent reasons:

* The C `abstract` (`kernel/abstract.cpp`) rewrites only `fvar`/`mvar` nodes and
  leaves `bvar`s untouched, so it *captures* loose bvars, while `abstract1`
  shifts them.  Counterexample: for `e = .app (.fvar x) (.bvar 0)`, `xs = [x]`,
  `e.abstract #[.fvar x] = .app (.bvar 0) (.bvar 0)` but
  `e.abstractList xs = .app (.bvar 0) (.bvar 1)`.
* On duplicates, `abstract` scans `i = n-1 … 0` and takes the **last** match,
  while the sequential `abstractList` gives the first-abstracted variable the
  *highest* index.  Counterexample: for `e = .fvar x`, `xs = [x, x]`,
  `e.abstract #[.fvar x, .fvar x] = .bvar 0` but `e.abstractList xs = .bvar 1`.

Requiring `e` to be loose-bvar-free and `xs` to be duplicate-free makes the two
agree.  See `docs/axiom-audit.md` §5.2.
-/
@[simp] axiom abstract_eq (e : Expr) (xs : List FVarId)
    (he : e.looseBVarRange' = 0) (hx : xs.Nodup) :
    e.abstract ⟨xs.map .fvar⟩ = e.abstractList xs

/-- This could be an `@[implemented_by]` -/
@[simp] axiom abstractRange_eq (e : Expr) (n : Nat) (xs : Array Expr) :
    e.abstractRange n xs = e.abstract (xs.extract 0 n)

def hasLooseBVar' : (e : @& Expr) → (bvarIdx : @& Nat) → Bool
  | .bvar i, d => i = d
  | .mdata _ e, d
  | .proj _ _ e, d => hasLooseBVar' e d
  | .app f a, d => hasLooseBVar' f d || hasLooseBVar' a d
  | .lam _ t b _, d
  | .forallE _ t b _, d => hasLooseBVar' t d || hasLooseBVar' b (d+1)
  | .letE _ t v b _, d => hasLooseBVar' t d || hasLooseBVar' v d || hasLooseBVar' b (d+1)
  | .const .., _
  | .sort _, _
  | .fvar _, _
  | .mvar _, _
  | .lit _, _ => false

/-- This could be an `@[implemented_by]` -/
@[simp] axiom hasLooseBVar_eq (e : Expr) (n : Nat) : e.hasLooseBVar n = e.hasLooseBVar' n

def eqv' : (e1 e2 : Expr) → (strict : Bool := false) → Bool
  | .bvar i, .bvar i', _
  | .lit i, .lit i', _
  | .mvar i, .mvar i', _
  | .fvar i, .fvar i', _
  | .sort i, .sort i', _ => i == i'
  | .mdata d e, .mdata d' e', st => e.eqv' e' st && d.entries == d'.entries
  | .proj s i e, .proj s' i' e', st => e.eqv' e' st && s == s' && i == i'
  | .const n ls, .const n' ls', _ => n == n' && ls == ls'
  | .app f a, .app f' a', st => f.eqv' f' st && a.eqv' a' st
  | .lam n t b bi, .lam n' t' b' bi', st
  | .forallE n t b bi, .forallE n' t' b' bi', st =>
    t.eqv' t' st && b.eqv' b' st && (!st || (n == n' && bi == bi'))
  | .letE n t v b nd, .letE n' t' v' b' nd', st =>
    t.eqv' t' st && v.eqv' v' st && b.eqv' b' st && nd == nd' && (!st || n == n')
  | _, _, _ => false

/-- This could be an `@[implemented_by]` -/
@[simp] axiom eqv_eq (e1 e2 : Expr) : e1.eqv e2 = e1.eqv' e2

/-- This could be an `@[implemented_by]` -/
@[simp] axiom equal_eq (e1 e2 : Expr) : e1.equal e2 = e1.eqv' e2 (strict := true)

end Expr
end Lean

/-! ## Pointer equality

`Lean4Lean/PtrEq.lean` declares the two `opaque` functions `ptrEqExpr` and
`ptrEqConstantInfo`, whose runtime implementation compares addresses. The two
axioms below are the *only* thing the proofs are allowed to assume about them,
and they are declared here rather than beside the opaques so that every frozen
axiom of this project lives in one file — `Verify/Guard.lean`'s check 1
enumerates axioms by defining module, so an axiom declared elsewhere is
invisible to it.

**Shape.** Each is an *implication constraining only the `true` branch*, not an
equation. That makes them structurally immune to the defect that produced both
historical `False`-proofs (§4, §11.2 of `docs/axiom-audit.md`): that defect needs
an axiom to *specify a return value* on a branch where the implementation does
something else, and these specify nothing on the `false` branch. The unsound
direction — equal values ⇒ equal addresses, false under copying — is not
asserted.

**Consistent, with an exhibited model.** `fun _ _ => false` satisfies both, so
neither can be inconsistent alone; and nothing else in the tree constrains these
opaques, so neither can join a contradiction. See `docs/axiom-audit.md` §14.

`withPtrEq` is not usable here — see `PtrEq.lean`'s docstring: the kernel really
does behave differently under pointer identity rather than treating it as an
optimisation before a true equality test. -/

namespace Lean4Lean
open Lean

axiom ptrEqExpr_eq : ptrEqExpr a b → a = b

axiom ptrEqConstantInfo_eq : ptrEqConstantInfo a b → a = b

end Lean4Lean
