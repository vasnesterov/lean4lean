import Lean4Lean.Theory.Typing.KKetaRow

/-!
# `NormalEq.descend`'s restatement, bounded both ways, and the grading route closed

`Theory/Typing/DescendRefute.lean` refutes `ChurchRosser.lean`'s `NormalEq.descend`
(`DescendStatement`) and `Theory/Typing/KDescend.lean` restates it (`NormalEq.descendV`, the
same statement plus `q.NoApp`).  What was missing between the two is the *bounding*: nothing
in the tree stated the restatement as a predicate on the `Params` instance, related it to the
original in either direction, or checked that the weakening is not a vacuity.  This file does
those three things and then closes one route.

## §1-§2: the two bounds

* **(a) implied by the original.**  `descendStatementV_of_descendStatement` -- adding a
  hypothesis, so free, and `sorryAx`-free.
* **(b) still has content.**  The three counterexamples are excluded *by construction*
  (`refQ_not_noApp`, `refQ2_not_noApp`: all three use an `.app`-headed pattern, and `NoApp` is
  literally `False` there), and the exclusion is not a blanket one:
  `refQv := .var (.const `C)` **is** `NoApp` and **does** match witness A's right endpoint
  `refG'`, and at that pattern the descent's obligation is **satisfied**
  (`refDescentOutV`).  So the restatement asks a real question at the very witness that
  refutes the original, rather than declining to ask one.

`descendV_dodges_witnessA` puts the two halves side by side at one `Γ`, `g`, `g'`: the
`.app` pattern's `DescentOut` is unsatisfiable, the `.var` pattern's is satisfied.  It is
`sorryAx`-free.

## §3: the `ParRedKn` grading does **not** close this

Grading `ParRedK` by redex-nesting height is what rescued the `keta` row
(`docs/vacuity-ledger.md` row 47).  It does nothing here, and the reason is that witness A's
*left* term is normal in every relation in play: `refEnv` registers no rules, so `KStep` never
fires (`VEnv.refParams_no_kstep`), hence `EtaK` never fires (`refNoEtaK`), hence `refG` is `ParRedK`-normal
(`refParRedK_G`) and therefore `ParRedKn n`-normal at **every** grade `n`, `n = 0` included
(`refParRedKn_G`).  A graded descent asks for a reduction of bounded grade, i.e. *strictly
less* than the ungraded one asks; so the witness survives grading a fortiori.  The route is
closed, not merely untried.

## Measured cones (this file's own instrument, `Guard` + `KSite7Rows` + `ParRedKGraded` closure)

| seed | cone | `descend` in cone | holes |
|---|---|---|---|
| `NormalEq.descend` | 3837 | -- | `forallE_inv_stratified`, `rigidShapeUniqNS` |
| `NormalEq.descendV` | 3839 | no | the same two |
| `NormalEq.appDF_extra_of_descend` | 3942 | **yes** | the two **+ `descend`** |
| `NormalEq.appDF_extra_of_descendVK` | 3989 | no | the same two |
| `parRedKStatement_of_rows` | 4261 | no | the two **+ `IsDefEqU.weakN_iff`** |
| `parRedKStatementN_zero` | 683 | no | **none** |
| `descendStatementV_of_descendStatement` | 682 | no | **none** |
| `refDescentOutV` | 6537 | no | **none** |
| `descendV_dodges_witnessA` | 6574 | no | **none** |
| `refParRedKn_G` | 6556 | no | **none** |

**Consumer bound (b), the count.**  `descend` has **224** transitive users in 41 modules (`scripts/users.lean`, 2026-09-03; the **193** here was measured at `f4b32ea` over a smaller closure and undercounts by 31) /
**206 users, 196 sole** (`hole-rank`, Guard+ConeJoin closure), and exactly **one** direct
user: `ChurchRosser.lean`'s `NormalEq.appDF_extra_of_descend` (`:2271`), which feeds
`NormalEq.parRed` (`:2332`).  So all 193 pass through one chokepoint, and the restatement
serves **all** of them or none.  It serves all of them: `KSite7App.lean`'s
`NormalEq.appDF_extra_of_descendVK` is that chokepoint's *unconditional* replacement (`hK`
discharged by `ParRedK.hK`) and `descend` is out of its cone.  The price is visible in the
table: the rewiring is descend-free but `parRedKStatement_of_rows` acquires
`IsDefEqU.weakN_iff` (through `parRedKStatementN_succ`, whose `appDF` x `beta` row is the sole
entry -- see `ParRedKGraded.lean`'s table).  That is a trade of a **refuted** lemma for a
**merely open** one, which is the right direction even though the hole count only drops by one.

## Sequel

`Theory/Typing/ParRedMissing.lean` takes the next step: it names the two constructors `ParRed`
lacks (`ParRedP`), repairs all three witnesses in the extension unconditionally, and shows the
extension is **cyclic** -- which is why the rewiring onto the `V`/`VK` route cannot be
completed today.  It also records the trap that a missing reduction step stated as a
*hypothesis about `ParRed`* is false at `refParams` (`not_parRedProofRepl`), so its consequences
are vacuous at the only witness instance available.

## What this file does not claim

`descendStatementV_holds` (the anti-strawman check, `descendV` at the predicate) carries
`sorryAx` -- through `Params.sortUniq` and `IsDefEq.uniq`, i.e. the two ambient injectivity
holes, exactly as `descendV` itself does.  `KDescend.lean`'s "`NormalEq.descendV` ... is
`sorry`-free" is a claim about a *local* `sorry`, not about an axiom set; `#print axioms
NormalEq.descendV` gives `[propext, sorryAx, Classical.choice, Quot.sound]`.  Everything in
§1-§3 that is stated at `refParams` avoids it.
-/

namespace Lean4Lean
open VExpr

/-! ## §1 The restatement as a predicate on the instance, and bound (a) -/

/-- **`NormalEq.descendV`'s statement**, as a predicate on the `Params` instance -- the same
shape `DescendStatement` gives `NormalEq.descend`, so the two are comparable.
It is `DescendStatement` plus the single hypothesis `q.NoApp`. -/
def DescendStatementV (I : VEnv.Params) : Prop :=
  ∀ (N : Nat) {g : VExpr}, sizeOf g ≤ N →
    ∀ {Γ : List VExpr} {q : Pattern} {g' : VExpr}
      {n1 : q.LPath → List VLevel} {n2 : q.Path → VExpr},
      q.NoApp → OnCtx Γ (VEnv.IsType I.env I.univs) → @VEnv.NormalEq I Γ g g' →
      q.Matches g' n1 n2 → @VEnv.DescentOut I Γ q g g' n1 n2

/-- **Bound (a): the restatement is implied by the original.**  Weakening is by *adding* a
hypothesis and nothing else, so this direction is free -- and `sorryAx`-free, which the
converse anti-strawman check is not.  Together with `descendStatementV_holds` this pins
`DescendStatementV` between the original and `descendV`: it is not a different statement
dressed up. -/
theorem descendStatementV_of_descendStatement {I : VEnv.Params}
    (H : DescendStatement I) : DescendStatementV I := by
  intro N g hsz Γ q g' n1 n2 _ hΓ hne hm
  exact H N hsz hΓ hne hm

/-- **Anti-strawman check**: `DescendStatementV` is literally `NormalEq.descendV`'s type.
`sorryAx`-tainted, inherited from `descendV`'s use of `Params.sortUniq` / `IsDefEq.uniq` --
see this file's header; that is why nothing below depends on it. -/
theorem descendStatementV_holds {I : VEnv.Params} : DescendStatementV I :=
  @VEnv.NormalEq.descendV I

/-! ## §2 Bound (b): the weakening excludes the counterexamples and nothing that matters

All three witnesses use an `.app`-headed pattern, so `Pattern.NoApp` is `False` at each:
`KDescend.lean`'s `VEnv.refQ_not_noApp` and `VEnv.refQ2_not_noApp` already record that half,
and this section supplies the half that was missing -- that the exclusion is *narrow*. -/

/-- **The exclusion is not a blanket one.**  Replace witness A's top `.app` node by `.var` --
the function side's pattern with the argument position left free.  This is `NoApp`, and it
still matches witness A's right endpoint.  So `q.NoApp` does *not* say "no pattern matching an
application", which is the vacuity this bound exists to rule out. -/
abbrev refQv : Pattern := .var (.const `C)

theorem refQv_noApp : refQv.NoApp := trivial

theorem refQv_matches : ∃ n1 n2, refQv.Matches refG' n1 n2 := ⟨_, _, .var .const⟩

/-- …and `refG` matches it too, which is the whole point: no reduction is needed. -/
theorem refQv_matches_left : ∃ n1 n2, refQv.Matches refG n1 n2 := ⟨_, _, .var .const⟩

/-- **Bound (b), sharp form: at the refuting witness the restatement's obligation is
*satisfied*.**  Same context, same `g`, same `g'` as `not_descendStatement`; only the pattern's
top node is `.var` instead of `.app`, which is what `q.NoApp` permits.  The descent answers at
eta-depth `0` with no reduction at all: `refG` already matches, and the one argument the
pattern exposes is related by `NormalEq.proofIrrel` -- the very constructor that makes the
original false.  `sorryAx`-free. -/
theorem refDescentOutV {n1 n2} (hm : refQv.Matches refG' n1 n2) :
    @VEnv.DescentOut refParams refCtx refQv refG refG' n1 n2 := by
  letI := refParams
  cases hm with
  | var hf =>
    cases hf
    refine .inl ⟨0, refG, _, _, .rfl, .var .const, fun _ => .nil, ?_, ?_, ?_⟩
    · intro _ _ h; exact absurd h (by simp)
    · intro _ _ h; exact absurd h (by simp)
    · rintro (_|x)
      · exact .proofIrrel refEnv_hasP refEnv_hasBvar refEnv_hasD
      · exact nomatch x

/-- **The fully degenerate instance**: nil var-telescope (`q = .const _`), empty context, no
reduction.  Checked because a statement can be green at `.var`-patterns and vacuous at the
base of the pattern induction, which is where the descent's own recursion bottoms out. -/
theorem refDescentOutV_const {n1 n2}
    (hm : (Pattern.const `D).Matches (.const `D []) n1 n2) :
    @VEnv.DescentOut refParams [] (.const `D) (.const `D []) (.const `D []) n1 n2 := by
  letI := refParams
  cases hm
  exact .inl ⟨0, _, _, _, .rfl, .const, fun _ => .nil,
    (fun _ _ h => absurd h (by simp)), (fun _ _ h => absurd h (by simp)), nofun⟩

/-- **The two bounds at one instance.**  At witness A's `Γ`, `g`, `g'`: the original's
`.app`-pattern obligation is unsatisfiable, and the restatement's `.var`-pattern obligation is
satisfied.  So `DescendStatementV` is weaker than `DescendStatement` *exactly* at the
`.app` node and is not vacuous there.  `sorryAx`-free (the two hypotheses are
`not_descendStatement`'s own, unchanged). -/
theorem descendV_dodges_witnessA (hsu : refEnv.SortUniq 0) (huq : refEnv.UniqTyping 0) :
    (∀ n1 n2, ¬ @VEnv.DescentOut refParams refCtx refQ refG refG' n1 n2) ∧
    (∀ {n1 n2}, refQv.Matches refG' n1 n2 →
      @VEnv.DescentOut refParams refCtx refQv refG refG' n1 n2) :=
  ⟨fun _ _ => refNoDescentOut hsu huq, fun hm => refDescentOutV hm⟩


/-! ## §3 The `ParRedKn` grading closes nothing here

`refEnv` registers no rules, so the K-rule never fires; hence `refG` is normal for `ParRedK`
and for `ParRedKn n` at every grade, `0` included. -/

/-- `KStep` never fires at `refParams` -- `KDescend.lean`'s `VEnv.refParams_no_kstep`, reused
rather than restated. -/
theorem refNoEtaK {Γ e e'} (H : @VEnv.EtaK refParams Γ e e') : False := by
  letI := refParams
  induction H with
  | here h => exact VEnv.refParams_no_kstep h
  | under _ _ ih => exact ih

theorem refParRedK_const {Γ c ls e} (H : @VEnv.ParRedK refParams Γ (.const c ls) e) :
    e = .const c ls := by
  cases H with
  | const => rfl
  | extra h => exact absurd h refNoPat
  | keta h _ => exact (refNoEtaK h).elim

theorem refParRedK_bvar {Γ i e} (H : @VEnv.ParRedK refParams Γ (.bvar i) e) : e = .bvar i := by
  cases H with
  | bvar => rfl
  | extra h => exact absurd h refNoPat
  | keta h _ => exact (refNoEtaK h).elim

/-- **Witness A's left term is `ParRedK`-normal.**  `ParRedK` is `ParRed` plus `keta`, and
`keta` needs an `EtaK` step, which needs a registered `.app` pattern.  There is none. -/
theorem refParRedK_G {e} (H : @VEnv.ParRedK refParams refCtx refG e) : e = refG := by
  cases H with
  | app hf ha => rw [refParRedK_const hf, refParRedK_bvar ha]
  | extra h => exact absurd h refNoPat
  | keta h _ => exact (refNoEtaK h).elim

/-- **…hence normal at every grade, `0` included.**  So grading `ParRedK` by redex-nesting
height does not make witness A ill-formed: the grade of the reduction the descent would have
to produce is `0`, and no reduction of grade `0` -- or of any grade -- moves `refG`.  A graded
descent asks for *less* than the ungraded one, so the refutation transfers a fortiori and the
`ParRedKn` route is closed for `descend`.  Contrast `docs/vacuity-ledger.md` row 47, where
grading works because there the obstruction is that a `keta` premise fails to *descend*, not
that a term fails to *move*. -/
theorem refParRedKn_G {n e} (H : @VEnv.ParRedKn refParams n refCtx refG e) : e = refG := by
  letI := refParams
  exact refParRedK_G H.toParRedK

/-- The degenerate instance of the grading, checked separately because a graded statement that
is only ever used at `n+1` can be green for the wrong reason. -/
theorem refParRedKn_G_zero {e} (H : @VEnv.ParRedKn refParams 0 refCtx refG e) : e = refG :=
  refParRedKn_G (n := 0) H

end Lean4Lean
