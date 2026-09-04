import Lean4Lean.Theory.Typing.StructEtaPrice
import Lean4Lean.Theory.Typing.PatternRules

/-!
# Pricing round of 2026-09-04: does the closed-`VDefEq` route avoid the confluence re-erection?

`Theory/Typing/StructEtaPrice.lean` §7 prices two routes for putting Lean's structure eta into
the abstract relation, and its table records, for the closed-`VDefEq` route,

| | closed `VDefEq` (§7) |
|---|---|
| induction cases added | **0** |
| `church_rosser` | `extra` case, already written |

**The first row is right and the second row is wrong**, and this file is the machine-checked
reason.  Nothing here edits an existing file; it is pricing, not repair.

## The distinction the §7 table misses

`VEnv.ParRed`'s and `VEnv.CParRed`'s `extra` constructors (`ChurchRosser.lean:761`, `:795`) are
indeed *generic*: they fire at any `Params.Pat`-registered pattern, so a new rule adds no
constructor and no induction case to either relation.  That much of §7 is correct.

But `ChurchRosser.lean`'s entire development — `NormalEq`, `ParRed`, `CParRed`, `ParRed.triangle`,
`NormalEq.parRed`, `IsDefEq.church_rosser` — is stated under `[VEnv.Params]`, and `Params` is not
a bare "there is a set of rules" hypothesis.  It is a **ten-field interface** that pins the rule
set to exactly two shapes and asserts they do not overlap:

* `pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern`, and `SimplePattern` has
  exactly two constructors — `.defn c` (a bare `const` head, a δ-rule) and
  `.iota r m c n` (`rec`-spine applied to a `ctor`-spine, an ι-rule);
* `pat_uniq`, `pat_app_l_uniq`, `pat_app_uniq` — the non-overlap conditions the diamond needs;
* `extra_pat` — **every** `env.defeqs df` is a `Pat`-registered pattern under leading lambdas.

So a new `VDefEq` does not reach `ParRed` as a *case*.  It reaches `Params` as an *obligation*,
and the three theorems below show it cannot be discharged in either orientation.  The cost of the
`VDefEq` route is therefore not "0 induction cases against 136"; it is a rebuild of the `Params`
interface, `PatternRules.lean`'s `Pat`/`RuleShape` classification, and `ParamsBuild.lean`'s
`paramsOfWF` — under which `ChurchRosser.lean` is then re-checked in full.

## What is proved here

* §1 `Pattern.not_matches_bvar`, `Pattern.not_matches_lam` — `Pattern.Matches` walks `const`/`app`
  spines only.  Two lines each, but they are what makes §2 route-independent: no *extension* of
  `Pat` can help, because the failure is in `Matches`.
* §2 `VEnv.Params.not_defeqs_etaDfZ` — **orientation 1 refuted.**  `StructEtaPrice.etaDfZ`, the
  exact rule §7 machine-checks `structEta_of_extra` against, cannot be in `Params.env.defeqs`:
  `extra_pat` λ-peels it to either a `lam` or a `bvar`, and neither is matchable.  This is the
  zero-field case, i.e. `isDefEqUnitLike`'s hole — the very instance §7 chose as its evidence.
* §3 `VEnv.Params.not_pat_ctorSpine` — **orientation 2 refuted.**  Flip the rule so its left-hand
  side is the constructor spine `S.mk ps (proj₀ ps x) …` and the peeled head *is* a `const`.  Then
  its pattern is `(Pattern.const C.name).varN (D.np + C.fields.length)`, which is **the ι-rule's own
  constructor block**, verbatim (`VInductDecl'.iotaPat`).  `pat_uniq` forbids exactly that.
* §4 `SimplePattern.eq_defn_of_toPattern_varN` — and at positive arity the orientation-2 pattern is
  not even *expressible*: `pat_simple` rejects it before `pat_uniq` gets to.  So the two obstacles
  are not the same obstacle counted twice; they bite at complementary arities.

Together: **the closed-`VDefEq` route does not make structure eta invisible to the confluence
layer.**  It makes `Params` uninhabitable at any environment carrying the rule.  Since
`church_rosser` is a theorem *about* `Params.env`, that is strictly worse than a new case: a new
case is work, an uninhabitable interface is vacuity.
-/

namespace Lean4Lean

open VExpr

/-! ## §1 `Pattern.Matches` walks `const`/`app` spines only -/

/-- No pattern matches a de Bruijn variable. -/
theorem Pattern.not_matches_bvar {p : Pattern} {i : Nat} {m1 m2} :
    ¬ p.Matches (.bvar i) m1 m2 := nofun

/-- No pattern matches a λ. -/
theorem Pattern.not_matches_lam {p : Pattern} {A b : VExpr} {m1 m2} :
    ¬ p.Matches (.lam A b) m1 m2 := nofun

/-- `mkLams Δ L` is a `bvar` only when the telescope is empty. -/
theorem mkLams_eq_bvar : ∀ {Δ : List VExpr} {L : VExpr} {i : Nat},
    VExpr.mkLams Δ L = .bvar i → Δ = [] ∧ L = .bvar i
  | [], _, _, h => ⟨rfl, h⟩
  | _::_, _, _, h => nomatch h

/-! ## §2 Orientation 1: the rule §7 machine-checks cannot be a `Params` rule -/

/-- **The closed-`VDefEq` structure-eta rule is not admissible in a `Params` environment.**

`StructEtaPrice.etaDfZ S mk` is `(fun x : S => x) ≡ (fun x : S => mk)`, the rule
`structEta_of_extra` fires.  `Params.extra_pat` demands it λ-peel to a *matchable* body sharing a
telescope with the right-hand side.  There are exactly two peels — `Δ = []`, body a `lam`; and
`Δ = [S]`, body `.bvar 0` — and §1 kills both.

The refutation is **route-independent within the pattern language**: it does not mention `Pat`, so
adding constructors to `Pat` (or to `SimplePattern`, or to `VEnv.RuleShape`) does not repair it.
Only changing `Pattern.Matches` — the matching relation `ParRed.extra`, `CParRed.extra`,
`Pattern.matches_inter` and the whole diamond argument are written against — would. -/
theorem VEnv.Params.not_defeqs_etaDfZ [VEnv.Params] {S mk : Lean.Name}
    (h : VEnv.Params.env.defeqs (etaDfZ S mk)) : False := by
  obtain ⟨Δ, L, R, p, r, m1, m2, hL, -, -, hm, -, -⟩ :=
    VEnv.Params.extra_pat (Γ := []) (ls := []) trivial h nofun rfl
  simp only [etaDfZ, VExpr.instL] at hL
  match Δ, hL with
  | [], hL =>
    simp only [VExpr.mkLams] at hL
    obtain rfl := hL
    exact Pattern.not_matches_lam hm
  | _::Δ', hL =>
    simp only [VExpr.mkLams, VExpr.lam.injEq] at hL
    obtain ⟨rfl, hL⟩ := hL
    obtain ⟨rfl, rfl⟩ := mkLams_eq_bvar hL.symm
    exact Pattern.not_matches_bvar hm

/-! ## §3 Orientation 2: the constructor-spine pattern is the ι-rule's own -/

theorem Pattern.app_ne_const_varN {f a : Pattern} {c : Lean.Name} :
    ∀ {n : Nat}, Pattern.app f a ≠ (Pattern.const c).varN n
  | 0 => nofun
  | _+1 => nofun

/-- **A rule whose pattern is a constructor spine collides with that constructor's ι-rule.**

Orient structure eta the other way — left-hand side `S.mk ps (proj₀ ps x) … (projₙ₋₁ ps x)`, right-hand
side `x` — and the λ-peeled body *is* `const`-headed, so §2's obstacle is gone.  The term has
exactly `D.np + C.fields.length` arguments, so any pattern matching it has that arity, and the
`SimplePattern` for it is `(Pattern.const C.name).varN (D.np + C.fields.length)`.

That is, letter for letter, the right half of `VInductDecl'.iotaPat` — the block the ι-rule's own
pattern already registers as its major-premise position.  `Params.pat_uniq` says two registered
patterns whose intersection with a subpattern of one of them is non-empty must be *the same
pattern*; here the intersection is `Pattern.inter_self`, and the two patterns differ in their head
constructor.  So the two rules cannot coexist.

Nothing in the statement is eta-specific: it prices *any* rewrite rule whose left-hand side is a
saturated constructor application, which is what surjective pairing is. -/
theorem VEnv.Params.not_pat_ctorSpine [VEnv.Params] {D : VInductDecl'} {T : VIndType}
    {C : VIndCtor} {r r'}
    (h₁ : VEnv.Params.Pat (D.iotaPat T C) r)
    (h₂ : VEnv.Params.Pat ((Pattern.const C.name).varN (D.np + C.fields.length)) r') :
    False := by
  have hsub : Subpattern ((Pattern.const C.name).varN (D.np + C.fields.length))
      (D.iotaPat T C) := .appR .refl
  obtain ⟨heq, -, -⟩ := VEnv.Params.pat_uniq h₁ h₂ hsub (Pattern.inter_self _)
  exact Pattern.app_ne_const_varN heq

/-! ## §4 And at positive arity `pat_simple` rejects it first -/

/-- **The pattern language has no constructor-spine shape at positive arity.**

`SimplePattern` is δ-rules and ι-rules and nothing else, so `(const c).varN n` is a `SimplePattern`
only at `n = 0`.  §3's collision therefore fires only in the zero-parameter zero-field case; at
every *other* structure, `Params.pat_simple` rejects the orientation-2 rule outright, without
needing `pat_uniq`.  The two obstacles cover complementary arities, so between §2, §3 and §4 the
closed-`VDefEq` route has no surviving orientation at any structure. -/
theorem SimplePattern.eq_defn_of_toPattern_varN {sp : SimplePattern} {c : Lean.Name} :
    ∀ {n : Nat}, sp.toPattern = (Pattern.const c).varN n → n = 0 ∧ sp = .defn c := by
  intro n h
  match sp, n, h with
  | .defn _, 0, h =>
    simp only [SimplePattern.toPattern, Pattern.varN, Pattern.const.injEq] at h
    exact ⟨rfl, by rw [h]⟩
  | .defn _, _+1, h => simp [SimplePattern.toPattern, Pattern.varN] at h
  | .iota .., 0, h => simp [SimplePattern.toPattern, Pattern.varN] at h
  | .iota .., _+1, h => simp [SimplePattern.toPattern, Pattern.varN] at h

/-- `(const a).varN m` determines both `a` and `m`. -/
theorem Pattern.const_varN_inj : ∀ {a b : Lean.Name} {m n : Nat},
    (Pattern.const a).varN m = (Pattern.const b).varN n → a = b ∧ m = n
  | _, _, 0, 0, h => ⟨by simpa [Pattern.varN] using h, rfl⟩
  | _, _, 0, _+1, h => by simp [Pattern.varN] at h
  | _, _, _+1, 0, h => by simp [Pattern.varN] at h
  | _, _, _+1, _+1, h => by
    simp only [Pattern.varN, Pattern.var.injEq] at h
    obtain ⟨rfl, rfl⟩ := Pattern.const_varN_inj h
    exact ⟨rfl, rfl⟩

/-! ## §5 The one encoding §4 does not cover — and it collides too

§4 rules out the *bare* constructor spine.  It does not rule out a sneakier encoding, and this
section closes that gap, because without it the §2–§4 verdict would have a hole.

`SimplePattern.iota r m c n` is `r` applied to `m` variables, applied to (`c` applied to `n`
variables).  At **positive fields** the eta rule's left-hand side
`S.mk ps (proj₀ ps x) … (projₖ₋₁ ps x)` has that shape with the roles *swapped*: take
`r := C.name`, `m := D.np + k - 1`, `c :=` the head of the last projection term (a recursor), `n :=`
its arity.  So the orientation-2 pattern **is** expressible as a `SimplePattern` after all, and §4
alone does not close the route.

It still collides, for the same reason and by the same field.  The ι-rule's own constructor block
`(const C.name).varN (D.np + C.fields.length)` is `Pattern.var` of `(const C.name).varN (D.np + k - 1)`
— which is precisely the *left* half of the sneaky pattern — so `Pattern.inter` succeeds through
`inter (.app f a) (.var f')`, and `pat_uniq` again demands the two patterns be equal.

The one residue is that equality of the two `.app` patterns forces the recursor leaf's name to be
the constructor's.  That is impossible in any environment built by declarations — it is exactly
what `Lean4Lean.rec_ne_ctor` (`PatternRules.lean:362`; note the module's own docstrings misname it `Pat.rec_ne_ctor`, which is NOT FOUND) establishes, from the two
`env.constants … = some …` fields `Pat.iota` carries, and the global name-distinctness discussion
in `PatternRules.lean` is about nothing else.  It is taken as a hypothesis here rather than
re-derived, because deriving it needs `Pat.iota`'s environment data and this is a pricing file. -/

/-- **The `mk`-headed-`iota` encoding of the eta rule collides with the real ι-rule.**

Together with §2 (orientation 1, any structure), §3 (orientation 2 bare spine, arity 0) and §4
(orientation 2 bare spine, positive arity), this leaves the closed-`VDefEq` route no surviving
encoding at any structure. -/
theorem VEnv.Params.not_pat_ctorHeadedIota [VEnv.Params] {D : VInductDecl'} {T : VIndType}
    {C : VIndCtor} {rn : Lean.Name} {n k : Nat} {r r'}
    (hne : Lean.mkRecName T.name ≠ C.name)
    (hk : D.np + C.fields.length = k + 1)
    (h₁ : VEnv.Params.Pat (D.iotaPat T C) r)
    (h₂ : VEnv.Params.Pat (SimplePattern.iota C.name k rn n).toPattern r') :
    False := by
  have hsub : Subpattern ((Pattern.const C.name).varN (k + 1)) (D.iotaPat T C) := by
    rw [VInductDecl'.iotaPat, SimplePattern.toPattern, hk]; exact .appR .refl
  have hint : (SimplePattern.iota C.name k rn n).toPattern.inter
      ((Pattern.const C.name).varN (k + 1)) = some (SimplePattern.iota C.name k rn n).toPattern := by
    simp [SimplePattern.toPattern, Pattern.varN, Pattern.inter, Pattern.inter_self]
  obtain ⟨heq, -, -⟩ := VEnv.Params.pat_uniq h₁ h₂ hsub hint
  rw [VInductDecl'.iotaPat, SimplePattern.toPattern, SimplePattern.toPattern,
    Pattern.app.injEq] at heq
  obtain ⟨hl, -⟩ := heq
  exact hne (Pattern.const_varN_inj hl).1

/-- **Corollary, stated the way the price wants it.**  At a structure with at least one parameter
or field, no `Params` instance registers the orientation-2 eta pattern — no `pat_uniq` needed. -/
theorem VEnv.Params.not_pat_ctorSpine_of_pos [VEnv.Params] {D : VInductDecl'} {C : VIndCtor}
    {r'} (hpos : 0 < D.np + C.fields.length)
    (h : VEnv.Params.Pat ((Pattern.const C.name).varN (D.np + C.fields.length)) r') :
    False := by
  obtain ⟨sp, hsp⟩ := VEnv.Params.pat_simple h
  obtain ⟨h0, -⟩ := SimplePattern.eq_defn_of_toPattern_varN hsp.symm
  omega

end Lean4Lean

/-! ## Axiom bar -/

#print axioms Lean4Lean.Pattern.not_matches_bvar
#print axioms Lean4Lean.Pattern.not_matches_lam
#print axioms Lean4Lean.VEnv.Params.not_defeqs_etaDfZ
#print axioms Lean4Lean.VEnv.Params.not_pat_ctorSpine
#print axioms Lean4Lean.SimplePattern.eq_defn_of_toPattern_varN
#print axioms Lean4Lean.VEnv.Params.not_pat_ctorSpine_of_pos
#print axioms Lean4Lean.VEnv.Params.not_pat_ctorHeadedIota
