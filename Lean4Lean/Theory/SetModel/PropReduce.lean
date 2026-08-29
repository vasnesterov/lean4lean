import Lean4Lean.Theory.SetModel.PropSplitAudit
import Lean4Lean.Theory.Typing.Lemmas

/-!
# `PropUniq` and `PropTypeAgree` reduce to zero universe parameters

**RZ-2 of `docs/backward-analysis.md` §9.**  The model, as `kernel_sound` needs
it, runs at `nv = 0`: `hfalse` gives `HasType 0 [] e falseProp`, so `sound_nil`
is instantiated at `nv := 0`.  The question this file answers is whether the two
statements `PropSplit` is built from are then only needed at `nv = 0`.

**They are.**  `PropUniq env 0 → PropUniq env nv` and
`PropTypeAgree env 0 → PropTypeAgree env nv`, for every `nv`, with no hypothesis
on `env` at all.  The reduction is `IsDefEq.instL` (`Theory/Typing/Lemmas.lean`)
against a list of **closed** levels, plus `VLevel.eval_inst`.

## Why it works, and what makes it slightly more than bookkeeping

Both conclusions are about `u.eval ls` at a **single** valuation `ls`, and a
valuation of `ℕ`s is realised by closed `VLevel`s: `ls.getD i 0` is the value of
the numeral `succ^(ls.getD i 0) zero`, which is `WF 0`.  So instantiating the
whole derivation at those numerals moves it to `nv = 0` while *preserving the
one number the conclusion is about*.  `VLevel.eval_inst` is the transport:
`(u.inst us).eval ns = u.eval (us.map (·.eval ns))`.

The one place care is needed is that `instL` substitutes at **every** parameter
index, while `u.WF nv` only bounds the ones `u` mentions; `eval_eq_of_wf` is the
lemma that says `eval` cannot see the difference.

## What this does *not* say

It does not make either statement any easier to *prove*: `PropUniq env 0` and
`PropTypeAgree env 0` are the same open problems, now stated over an environment
with no universe parameters in scope.  What it buys is that
`docs/backward-analysis.md` §6.2's derivation — which discharges `PropUniq` at
zero universe parameters from `hfalse` — is not restricted to closed levels, and
that RZ-1 (whether the model's outer induction can be run at `nv = 0`) does not
have to be answered.

`RZ-2 subsumes RZ-1`, in the document's phrase, because the reduction is on the
*syntactic* statements and not on the interpretation.
-/

namespace Lean4Lean

namespace VLevel

/-- The closed level `succ^k zero`. -/
def ofNat : ℕ → VLevel
  | 0 => .zero
  | k + 1 => .succ (ofNat k)

@[simp] theorem ofNat_wf {k n : ℕ} : (ofNat k).WF n := by
  induction k with
  | zero => trivial
  | succ _ ih => exact ih

@[simp] theorem ofNat_eval {k : ℕ} {ns : List ℕ} : (ofNat k).eval ns = k := by
  induction k with
  | zero => rfl
  | succ _ ih => simp [ofNat, eval, ih]

/-- **`eval` only looks at the parameters `WF` bounds.**  Two valuations that
agree below `n` give the same value to every `n`-well-formed level. -/
theorem eval_eq_of_wf : ∀ {l : VLevel} {n : ℕ}, l.WF n →
    ∀ {ls ls' : List ℕ}, (∀ i, i < n → ls.getD i 0 = ls'.getD i 0) →
    l.eval ls = l.eval ls'
  | .zero, _, _, _, _, _ => rfl
  | .succ l, _, h, _, _, H => by simp [eval, eval_eq_of_wf (l := l) h H]
  | .max l₁ l₂, _, h, _, _, H => by
    simp [eval, eval_eq_of_wf (l := l₁) h.1 H, eval_eq_of_wf (l := l₂) h.2 H]
  | .imax l₁ l₂, _, h, _, _, H => by
    simp [eval, eval_eq_of_wf (l := l₁) h.1 H, eval_eq_of_wf (l := l₂) h.2 H]
  | .param i, _, h, _, _, H => H i h

/-- **The closed realisation of a valuation.**  `numerals nv ls` is the list of
`nv` closed levels whose values are `ls`'s first `nv` entries. -/
def numerals (nv : ℕ) (ls : List ℕ) : List VLevel :=
  (List.range nv).map fun i ↦ ofNat (ls.getD i 0)

@[simp] theorem numerals_length {nv : ℕ} {ls : List ℕ} : (numerals nv ls).length = nv := by
  simp [numerals]

theorem numerals_wf {nv : ℕ} {ls : List ℕ} {n : ℕ} :
    ∀ l ∈ numerals nv ls, l.WF n := by
  simp [numerals]

theorem numerals_getD {nv : ℕ} {ls : List ℕ} {ns : List ℕ} {i : ℕ} (hi : i < nv) :
    ((numerals nv ls).map (eval ns)).getD i 0 = ls.getD i 0 := by
  have hlen : ((numerals nv ls).map (eval ns)).length = nv := by simp
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp [numerals, List.getElem_map]

/-- **The reduction, at the level of `VLevel`.**  For an `nv`-well-formed `u`
and any valuation `ls`, instantiating at `numerals nv ls` and evaluating at the
empty valuation returns `u.eval ls` — and the instantiated level is closed. -/
theorem eval_inst_numerals {u : VLevel} {nv : ℕ} (hu : u.WF nv) {ls ns : List ℕ} :
    (u.inst (numerals nv ls)).eval ns = u.eval ls := by
  rw [eval_inst]
  exact eval_eq_of_wf hu fun i hi ↦ numerals_getD hi

end VLevel

namespace VEnv

variable {env : VEnv}

/-- **RZ-2: `PropUniq` is a statement about zero universe parameters.**

Every instance at `nv` is the `nv = 0` instance of the derivation instantiated
at closed levels.  No hypothesis on `env`; in particular no `Ordered`, no
context well-formedness — `IsDefEq.instL` needs none. -/
theorem PropUniq.of_zero (h : env.PropUniq 0) (nv : ℕ) : env.PropUniq nv := by
  intro Γ A u v ls hu hv hA hA'
  have hw : ∀ l ∈ VLevel.numerals nv ls, l.WF 0 := VLevel.numerals_wf
  have h1 : env.HasType 0 (Γ.map (VExpr.instL (VLevel.numerals nv ls)))
      (A.instL (VLevel.numerals nv ls)) (.sort (u.inst (VLevel.numerals nv ls))) :=
    HasType.instL hw hA
  have h2 : env.HasType 0 (Γ.map (VExpr.instL (VLevel.numerals nv ls)))
      (A.instL (VLevel.numerals nv ls)) (.sort (v.inst (VLevel.numerals nv ls))) :=
    HasType.instL hw hA'
  have := h (ls := []) (VLevel.WF.inst hw) (VLevel.WF.inst hw) h1 h2
  rwa [VLevel.eval_inst_numerals hu, VLevel.eval_inst_numerals hv] at this

/-- **The same reduction for `PropTypeAgree`.**  Identical in shape: the term
and both its types are instantiated at the same closed levels, so the four
premises transport together. -/
theorem PropTypeAgree.of_zero (h : env.PropTypeAgree 0) (nv : ℕ) :
    env.PropTypeAgree nv := by
  intro Γ e A A' u u' ls hu hu' he he' hA hA'
  have hw : ∀ l ∈ VLevel.numerals nv ls, l.WF 0 := VLevel.numerals_wf
  have := h (ls := []) (VLevel.WF.inst hw) (VLevel.WF.inst hw)
    (HasType.instL hw he) (HasType.instL hw he')
    (HasType.instL hw hA) (HasType.instL hw hA')
  rwa [VLevel.eval_inst_numerals hu, VLevel.eval_inst_numerals hu'] at this

end VEnv

end Lean4Lean
