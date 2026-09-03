import Lean4Lean.Theory.Inductive.RecTyped
import Lean4Lean.Theory.Typing.SpineInv

/-!
# `HargsShared`: the one datum behind obligations (A), (B) and (C), named once

Three streams reduced the three general parameterful obligations of `VEnv.addInductR_ordered'`
and each reported that its residual "bottoms out in §8.7's `hargs`".  Those were three
*docstring* identifications, at four syntactically different judgements.  This file makes the
identification a theorem, and measures what is genuinely shared and what is not.

## What is claimed

* §2: at a companion member, §8.7's pair `hsplit` + `hargs` and "the presented head applied to
  the presented spine is well typed" are **equivalent** (given `e.WF`, the lookup, and
  `hsplit`).  So §8.7's residual is **one** datum, not two.  `hsplit` is a shape fact and stays
  a hypothesis; §5 records why it cannot be dropped.
* §3/§4: that one datum, stated once at the block's parameter context and at `D.uvars`,
  transports by **existing** lemmas to all four consumption sites — §8.8's `hbody` (obligation
  (A)), `MotiveHargs`' and `RecBodyHargs`' type-head `hbody` and `MinorCtorHargs`'
  constructor-head `hbody` (obligation (B), and (C) through the same two bundles).  The two
  transports are `VInductDecl'.atRec_hasType` and `VEnv.IsDefEq.weakR`; neither is new.
* §6: the datum is **two** data, not one — the type head's and the constructor head's — and
  their telescopes are related only definitionally (F3).  Collapsing them needs
  `VEnv.HasArgs.congr_tele`, which is another stream's.
* §7: the datum is **jointly inhabited at a real parameterised nested block**, with the
  transports firing, in an **arity-0** theorem.

## What is NOT claimed

Nothing here produces the datum in general.  `VIndRestore.instAt_indep_of_tyArgs`
(`Theory/Inductive/NestedRules.lean`) shows no restoration-independent argument can, and §8
records the measurement that `AddInductStagesR` does not supply it either.  **This is a
reduction of four residuals to one, not a discharge**, and the remaining datum is named in §8.
-/

namespace Lean4Lean

open Lean (Name)
open VExpr (mkPi mkLams mkApp bvars instAll splitPis)

namespace VIndRestore

variable {R : VIndRestore} {D : VInductDecl'} {e : VEnv} {n : Name} {j : Nat} {B : VExpr}

/-! ## §1 The datum

`VIndRestore.tyBody` and `VIndRestore.ctorBody` are the same expression shape at two different
head constants — the presented head `n.{R.tyLvls j}` applied to the presented spine
`R.tyArgs j`.  Naming that shape once is what lets §3/§4 be stated once. -/

/-- The presented head applied to the presented spine.  `tyBody` and `ctorBody` are its two
instances (`tyBody_eq_headApp`, `ctorBody_eq_headApp`, both `rfl`). -/
def HeadApp (R : VIndRestore) (n : Name) (j : Nat) : VExpr :=
  (VExpr.const n (R.tyLvls j)).mkApp (R.tyArgs j)

theorem tyBody_eq_headApp (R : VIndRestore) (D : VInductDecl') (j : Nat) :
    R.tyBody D j = R.HeadApp (R.tyName j) j := rfl

theorem ctorBody_eq_headApp (R : VIndRestore) (D : VInductDecl') (j : Nat) (C : VIndCtor) :
    R.ctorBody D j C = R.HeadApp (R.ctorName C.name) j := rfl

/-- **THE DATUM.**  The presented head applied to the presented spine is well typed, in the
block's parameter telescope, at the block's own universe count, over the environment the step
produces (`e`, *not* the pre-block one: the spine mentions the constants the step declares —
`ntreeRestore.tyArgs 1` is `List (NTree #0)` and `NTree` is declared by the block).

The resulting type `B` is explicit rather than existential because every consumer's `hpi`
mentions it. -/
def SpineTypedAt (R : VIndRestore) (D : VInductDecl') (e : VEnv) (n : Name) (j : Nat)
    (B : VExpr) : Prop :=
  e.HasType D.uvars D.params.reverse (R.HeadApp n j) B

/-- The datum with the type existentially quantified — the form §2's equivalence is stated at. -/
def SpineTyped (R : VIndRestore) (D : VInductDecl') (e : VEnv) (n : Name) (j : Nat) : Prop :=
  ∃ B, R.SpineTypedAt D e n j B

/-! ## §2 §8.7's residual is the datum — and its `hsplit` half is FREE

**Correction, measured.**  `VIndRestore.tyVal_hasType_of_faithful`'s docstring says of its two
hypotheses "the two hypotheses are the whole gap", and `docs/vacuity-ledger.md` row 74b records
an asymmetry — `hsplit` "derivable for one head, data for the other", by
`VIndCtor.splitPis_type_instL` for the constructor head and *not* for the type head (F1).

`hsplit` is **free for both heads, with no hypotheses at all**: `VExpr.mkPi_splitPis`
(`Theory/Inductive/NestedBuild.lean`) says `mkPi (splitPis n e).1 (splitPis n e).2 = e` at
**every** `n` and every `e`, because `splitPis` returns the empty telescope when the subject is
not `forallE`-headed.  `hsplit_free` below is that, reversed.  So row 74b's asymmetry is not
about `hsplit`; `ParamRedex.lean`'s `mp_hsplit` was not needed; and §8.7 has **one** residual,
not two.

**Stated precisely, because the negative in the tree is about a different proposition.**
`NestedTele.lean` §T12's prose says of the type head "that cannot be proved: F1 makes `T.type`
only *definitionally* the canonical pi-telescope".  That is right about the sentence *"the
presented head's type has `npJ j` leading pis syntactically"* — i.e. about
`(splitPis (npJ j) X).1.length = npJ j`, which really is not derivable.  But that sentence is
**not** what `hsplit` says: `splitPis` truncates silently when the subject runs out of pis, and
`hsplit` compares the subject with the re-assembly of whatever `splitPis` produced, so it holds
either way.  And the truncated case is not smuggled past anything: `hargs` is stated against the
*same* truncated telescope, so it then forces the presented spine to be correspondingly short,
and `Faithful.ty_agree`'s `instAt` uses the same `splitPis`.  So the strong sentence is not
needed anywhere in §8.7, and `hsplit` is dead weight.

`VIndRestore.tyVal_hasType_of_faithful` (`Theory/Inductive/NestedRules.lean` §8.7) reduces the
`val` clause of `(R.csubst D K).WF` at a companion member to two hypotheses.  Both directions
below are one application of an existing lemma; the point is that they are *both* available, so
"§8.7's residual is `hsplit` plus `hargs`" over-counts: given `hsplit` (a shape fact about the
presented head's declared type, independent of the spine) the residual is exactly `SpineTyped`.

The backward direction needs `e.WF`, because `VEnv.HasArgs.of_mkApp`
(`Theory/Typing/SpineInv.lean`) does — it inverts an application, which needs uniqueness of
types. -/

section
variable {ci : VConstant} {np : Nat}

/-- Abbreviation for the presented head's declared telescope after `np` splits. -/
abbrev declTele (R : VIndRestore) (ci : VConstant) (np j : Nat) : List VExpr :=
  (splitPis np (ci.type.instL (R.tyLvls j))).1

abbrev declBody (R : VIndRestore) (ci : VConstant) (np j : Nat) : VExpr :=
  (splitPis np (ci.type.instL (R.tyLvls j))).2

/-- **§8.7's `hsplit`, unconditionally.**  `VExpr.mkPi_splitPis` reversed. -/
theorem hsplit_free (R : VIndRestore) (ci : VConstant) (np j : Nat) :
    ci.type.instL (R.tyLvls j) = mkPi (R.declTele ci np j) (R.declBody ci np j) :=
  (VExpr.mkPi_splitPis np _).symm

/-- **`hargs` ⟹ the datum.**  Exactly the two steps `tyVal_hasType_of_faithful` performs
internally, with the `mkLams` peeled off. -/
theorem spineTypedAt_of_hargs
    (hci : e.constants n = some ci) (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (huv : (R.tyLvls j).length = ci.uvars)
    (hargs : e.HasArgs D.uvars D.params.reverse (R.declTele ci np j) (R.tyArgs j)) :
    R.SpineTypedAt D e n j (instAll (R.declBody ci np j) (R.tyArgs j)) := by
  have hconst := VEnv.HasType.const (Γ := D.params.reverse) (U := D.uvars) hci hlvl huv
  rw [hsplit_free R ci np j] at hconst
  exact VEnv.HasType.mkApp' hargs hconst

/-- **…and the datum ⟹ `hargs`.**  So the two are equivalent and §8.7 has one residual. -/
theorem hargs_of_spineTyped (henv : e.WF)
    (hΓ : OnCtx D.params.reverse (e.IsType D.uvars))
    (hci : e.constants n = some ci) (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (huv : (R.tyLvls j).length = ci.uvars)
    (hlen : (R.tyArgs j).length = (R.declTele ci np j).length)
    (h : R.SpineTyped D e n j) :
    e.HasArgs D.uvars D.params.reverse (R.declTele ci np j) (R.tyArgs j) := by
  obtain ⟨B, hB⟩ := h
  have hconst := VEnv.HasType.const (Γ := D.params.reverse) (U := D.uvars) hci hlvl huv
  rw [hsplit_free R ci np j] at hconst
  exact VEnv.HasArgs.of_mkApp henv hΓ _ hlen hconst hB

end

/-! ## §3 Transport 1: to the recursor's numbering — obligations (B) and (C)

`MotiveHargs`, `MinorCtorHargs` and `RecBodyHargs` (`Theory/Inductive/RecTyped.lean` §4) all
take their head typing at `D.recUvars` over `(D.atRecTele D.params).reverse`.  That is the datum
under `VInductDecl'.atRec` — the level renumbering `D.selfLvls`, whose typing transport
`VInductDecl'.atRec_hasType` (`Theory/Inductive/Lemmas.lean`) already exists.  **No new
content**; this section exists to say that the four sites need one datum. -/

theorem spineTypedAt_atRec (h : R.SpineTypedAt D e n j B) :
    e.HasType D.recUvars ((D.atRecTele D.params).reverse) (D.atRec (R.HeadApp n j))
      (D.atRec B) := by
  have h' := D.atRec_hasType h
  rwa [VInductDecl'.atRecCtx, List.map_reverse] at h'

/-! ## §4 Transport 2: under an ambient context — obligation (A)

§8.8's `substC_tyApp_defeq_tyAppR_comp` takes its `hbody` at `D.params.reverse ++ Γ`, `Γ` being
the field context obligation (A)'s per-field defeq lives in.  The parameters are closed and the
subject is typed under them, so this is `VEnv.IsDefEq.weakR` — again an existing lemma. -/

theorem spineTypedAt_append (he : e.Ordered)
    (hΓ : OnCtx D.params.reverse (e.IsType D.uvars))
    (h : R.SpineTypedAt D e n j B) (Γ : List VExpr) :
    e.HasType D.uvars (D.params.reverse ++ Γ) (R.HeadApp n j) B :=
  VEnv.IsDefEq.weakR he (VEnv.CtxWF.closed he hΓ) h Γ

end VIndRestore

/-! ## §5 The decomposition of (B)'s bundles: datum ∧ shape residual

`VIndRestore.MotiveHargs` and `VIndRestore.MinorCtorHargs` (`Theory/Inductive/RecTyped.lean`
§4) are each a four-way conjunction under an existential.  The two theorems below split each
into **exactly** the datum of §1 (transported by §3) and a residual that mentions no typing of
the presented head at all — an `Iff`, so nothing is smuggled either way.

That is the measurement "how much of (B)'s bundle is the shared datum": one conjunct of four in
each, and the *same* conjunct in both, up to which constant heads the spine.  The residual is
what §T10/§T12.1 and row 74b are about (`hpi`/`hAs`/`hsort` for the type head, plus `hfun` for
the constructor head) and is not touched here. -/

namespace VIndRestore

section
variable (R : VIndRestore) (D : VInductDecl') (σ : CSubst) (e : VEnv)

/-- `MotiveHargs`' residual at a fixed head type `B`: `hpi` + `hAs` + `hsort`, no typing of the
presented head. -/
def MotiveShape (t : Nat) (T : VIndType) (B : VExpr) : Prop :=
  ∃ (As : List VExpr) (B' : VExpr) (w : VLevel),
    VExpr.instAll B (bvars (T.indices.length + t) D.np) = mkPi As B' ∧
    e.HasArgs D.recUvars
      ((VExpr.liftTele t ((D.atRecTele T.indices).map (VExpr.substC · σ)) 0).reverse
        ++ (((D.motives.map (VExpr.substC · σ)).take t).reverse
            ++ (D.atRecTele D.params).reverse))
      As (bvars 0 T.indices.length) ∧
    VExpr.instAll B' (bvars 0 T.indices.length) = .sort w

/-- `MinorCtorHargs`' residual at a fixed head type `B`: `hpi` + `hfun`.

**Two conjuncts, no existentials**, since `RecTyped.lean` §4 pins `As` and `B'` in the bundle and
`hAs` is a theorem there (`minorCtor_hAs`).  `R` is now an argument, because the pinned `As`/`B'`
mention the restoration data. -/
def MinorCtorShape (q t : Nat) (C : VIndCtor) (B : VExpr) : Prop :=
    VExpr.instAll B
      (bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
        = mkPi
          (VExpr.instAllTele (D.atRecTele (C.fieldTypesR D R))
            (bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np) 0)
          (instAll (D.tyAppR' R t C.fields.length (D.atRecTele C.args))
            (bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
            (C.fieldTypesR D R).length) ∧
    e.HasType D.recUvars
      ((VExpr.liftTele (D.nm + q)
          ((D.atRecTele (C.fields.map (·.type))).map (VExpr.substC · σ))
          ++ (D.ihTypes q C).map (VExpr.substC · σ)).reverse
        ++ (((D.minors.map (VExpr.substC · σ)).take q).reverse
            ++ ((D.motives.map (VExpr.substC · σ)).reverse
                ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length
            C.fields.length (D.atRec a)).map (VExpr.substC · σ)))
      (.forallE (VExpr.instAll
          (instAll (D.tyAppR' R t C.fields.length (D.atRecTele C.args))
            (bvars ((D.ihTypes q C).length + C.fields.length + (D.nm + q)) D.np)
            (C.fieldTypesR D R).length)
          (bvars (D.ihTypes q C).length C.fields.length))
        (.sort D.elimLvl))

end

variable {R : VIndRestore} {D : VInductDecl'} {e : VEnv} {B : VExpr}

/-- **`MotiveHargs` = the datum ∧ the shape residual.** -/
theorem motiveHargs_iff {σ : CSubst} {t : Nat} {T : VIndType} :
    R.MotiveHargs D σ e t T ↔
      ∃ B₀, e.HasType D.recUvars ((D.atRecTele D.params).reverse)
        (D.atRec (R.tyBody D t)) B₀ ∧ MotiveShape D σ e t T B₀ := by
  constructor
  · rintro ⟨As, B₀, B', w, hbody, hpi, hAs, hsort⟩
    exact ⟨B₀, hbody, As, B', w, hpi, hAs, hsort⟩
  · rintro ⟨B₀, hbody, As, B', w, hpi, hAs, hsort⟩
    exact ⟨As, B₀, B', w, hbody, hpi, hAs, hsort⟩

/-- **…and the same for `MinorCtorHargs`.** -/
theorem minorCtorHargs_iff {σ : CSubst} {q t : Nat} {C : VIndCtor} :
    R.MinorCtorHargs D σ e q t C ↔
      ∃ B₀, e.HasType D.recUvars ((D.atRecTele D.params).reverse)
        (D.atRec (R.ctorBody D t C)) B₀ ∧ R.MinorCtorShape D σ e q t C B₀ :=
  ⟨fun ⟨B₀, hbody, hpi, hfun⟩ => ⟨B₀, hbody, hpi, hfun⟩,
   fun ⟨B₀, hbody, hpi, hfun⟩ => ⟨B₀, hbody, hpi, hfun⟩⟩

/-- **OBLIGATION (B)'s MOTIVE BUNDLE FROM THE DATUM.**  `MotiveHargs` from `SpineTypedAt` at
the **type** head plus the shape residual — the datum entering once, at `D.uvars` and at the
parameter context, with §3 doing the transport. -/
theorem motiveHargs_of_spineTypedAt {σ : CSubst} {t : Nat} {T : VIndType}
    (h : R.SpineTypedAt D e (R.tyName t) t B)
    (hsh : MotiveShape D σ e t T (D.atRec B)) : R.MotiveHargs D σ e t T :=
  motiveHargs_iff.2 ⟨_, spineTypedAt_atRec h, hsh⟩

/-- **OBLIGATION (B)'s MINOR BUNDLE FROM THE DATUM**, at the **constructor** head — the same
datum at a different head constant, and the same transport. -/
theorem minorCtorHargs_of_spineTypedAt {σ : CSubst} {q t : Nat} {C : VIndCtor}
    (h : R.SpineTypedAt D e (R.ctorName C.name) t B)
    (hsh : R.MinorCtorShape D σ e q t C (D.atRec B)) : R.MinorCtorHargs D σ e q t C :=
  minorCtorHargs_iff.2 ⟨_, spineTypedAt_atRec h, hsh⟩

end VIndRestore

/-! ## §6 The two other consumption sites, from the same datum

§5 covers obligations (B) and (C) (both go through `MotiveHargs`/`MinorCtorHargs`; (C)
additionally through `iotaCtx_teleDefEq`'s `hmot`/`hmin`, which are those two bundles verbatim
per `NestedTele.lean` §T16's docstring — *read off*, not re-derived here).  This section covers
the other two: obligation (A)'s β-gap head defeq (§8.8) and the `val` clause of
`(R.csubst D K).WF` (§8.7).

Both are one application; that is the claim.  The datum enters at `D.uvars` over
`D.params.reverse` in both, exactly as in §5. -/

namespace VIndRestore
variable {R : VIndRestore} {D : VInductDecl'} {K : List Name} {e : VEnv} {B : VExpr}

/-- **OBLIGATION (A)'s β-GAP HEAD DEFEQ FROM THE DATUM.**  `NestedRules.lean` §8.8's
`substC_tyApp_defeq_tyAppR_comp` with its `hbody` replaced by §1's datum: §4's `weakR` supplies
the ambient context.  `hpar` is `VInductDecl'.WF.params` transported to `e`, which
`NestedTele.lean` §T15's item 2 already names as the one telescope-typing side condition. -/
theorem substC_tyApp_defeq_tyAppR_of_spineTypedAt (hnd : D.blockNames.Nodup)
    (hlw : ∀ i, (R.tyVal D i).LevelWF D.uvars)
    (hcl : ∀ i, ∀ a ∈ R.tyArgs i, a.ClosedN D.np) (henv : e.Ordered)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {k : Nat} {args Γ As : List VExpr} {B' : VExpr}
    (hargs : ∀ a ∈ args, a.NoCSubst (R.csubstTy D K))
    (hpar : OnCtx D.params.reverse (e.IsType D.uvars))
    (hOn : OnCtx (D.params.reverse ++ Γ) (e.IsType D.uvars))
    (hbv : e.HasArgs D.uvars Γ D.params (bvars k D.np))
    (h : R.SpineTypedAt D e (R.tyName j) j B)
    (hpi : VExpr.instAll B (bvars k D.np) = mkPi As B')
    (hAs : e.HasArgs D.uvars Γ As args) :
    e.IsDefEq D.uvars Γ ((D.tyApp j k args).substC (R.csubstTy D K))
      (D.tyAppR R j k args) (VExpr.instAll B' args) :=
  substC_tyApp_defeq_tyAppR_comp hnd hlw hcl henv hT hK hargs hOn hbv
    (spineTypedAt_append henv hpar h Γ) hpi hAs

/-- **§8.7's `val` CLAUSE FROM THE DATUM IN `HasArgs` FORM — HOLE-FREE.**
`tyVal_hasType_of_faithful` with `hsplit` discharged by §2's `hsplit_free`, so the residual is
`hargs` **alone**.  Prefer this over `tyVal_hasType_of_spineTyped` below, which takes the applied
form and pays the Π-inversion hole to get back to `HasArgs`. -/
theorem tyVal_hasType_of_hargs {env e₂ : VEnv} {npJ : Nat → Nat}
    (hfa : R.Faithful D env K npJ) (hle : env ≤ e₂)
    (hparams : OnCtx D.params.reverse (e₂.IsType D.uvars))
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (hargs : ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
      e₂.HasArgs D.uvars D.params.reverse (R.declTele ci (npJ j) j) (R.tyArgs j)) :
    e₂.HasType D.uvars [] (R.tyVal D j) T.type :=
  tyVal_hasType_of_faithful hfa hle hparams hT hK hlvl
    (fun ci _ => hsplit_free R ci (npJ j) j) hargs

/-- **§8.7's `val` CLAUSE FROM THE DATUM.**  `tyVal_hasType_of_faithful` with `hargs` replaced
by §1's datum, via §2's backward direction, and with `hsplit` **discharged** by §2's `hsplit_free`.
The extra `hlen` is the length side condition
`VEnv.HasArgs.of_mkApp` needs and cannot derive (a spine may under- or over-apply); `he₂ : e₂.WF`
is what the inversion costs. -/
theorem tyVal_hasType_of_spineTyped {env e₂ : VEnv} {npJ : Nat → Nat}
    (hfa : R.Faithful D env K npJ) (hle : env ≤ e₂) (he₂ : e₂.WF)
    (hparams : OnCtx D.params.reverse (e₂.IsType D.uvars))
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    (hlvl : ∀ l ∈ R.tyLvls j, l.WF D.uvars)
    (hlen : ∀ ci : VConstant, env.constants (R.tyName j) = some ci →
      (R.tyArgs j).length = (R.declTele ci (npJ j) j).length)
    (h : R.SpineTyped D e₂ (R.tyName j) j) :
    e₂.HasType D.uvars [] (R.tyVal D j) T.type := by
  obtain ⟨ci₀, hci₀, huv₀, -⟩ := hfa.ty_agree j T hT hK
  refine tyVal_hasType_of_faithful hfa hle hparams hT hK hlvl
    (fun ci _ => hsplit_free R ci (npJ j) j) fun ci hci => ?_
  have huv : (R.tyLvls j).length = ci.uvars := by
    cases Option.some.inj (hci₀.symm.trans hci); exact huv₀.symm
  exact hargs_of_spineTyped he₂ hparams (hle.constants hci) hlvl huv
    (hlen ci hci) h

end VIndRestore

/-! ## §7 Inhabitation, stated separately from hole-freeness

`docs/vacuity-ledger.md` §0 and rows 195/199b/205: a clean axiom line is compatible with proving
nothing, and the check that has caught this three times is *instantiate at a real witness*.

The witness is `ntreeAux` — `NTree α` with a `List (NTree α)` field, `D.np = 1`, the block Lean's
own kernel runs the nested elimination on.  Its companion member is presented as
`List.{u} (NTree.{u} #0)`, so the datum here is a **non-empty** spine at a **non-empty**
parameter telescope: the `ni = 0` degeneracy `docs/handoff-iotahargs.md` §5b discloses for
`hidx` does not apply to it (the datum is about the parameter block, not the index block). -/

namespace InductiveDeclExamples

section
variable {env₁ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

include h hF₁ hF₂ in
/-- **THE DATUM AT THE TYPE HEAD OF A PARAMETERISED NESTED BLOCK.** -/
theorem ntree_spineTypedAt_ty :
    ntreeRestore.SpineTypedAt ntreeAux F₂ ``List 1 (.sort (.succ (.param 0))) := by
  have hL : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.const ``List [.param 0])
      (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
    .const (ntreeF₂_list h hF₁ hF₂) (by decide) rfl
  have hN : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.const ``NTree [.param 0])
      (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
    .const (ntreeF₂_ntree hF₁ hF₂) (by decide) rfl
  have hb : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.bvar 0)
      (.sort (.succ (.param 0))) := .bvar .zero
  exact hL.app (hN.app hb)

end

/-- …and with the staging equations **supplied** rather than assumed: the datum holds at a real
parameterised nested block with nothing hypothesised.  This is the form row 11a asks for. -/
theorem ntree_spineTypedAt_ty_inhabited :
    ∃ env₁ F₁ F₂ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁ ∧
      F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂ ∧
      ntreeRestore.SpineTypedAt ntreeAux F₂ ``List 1 (.sort (.succ (.param 0))) := by
  obtain ⟨env₁, E₁, E₂, F₁, F₂, h, -, -, hF₁, hF₂⟩ := ntree_stage₂_exists
  exact ⟨env₁, F₁, F₂, h, hF₁, hF₂, ntree_spineTypedAt_ty h hF₁ hF₂⟩

/-! ### §7b The constructor heads, the transports firing, and the boundary -/

section
variable {env₁ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

include h hF₁ hF₂ in
/-- **The datum at the companion's `nil` constructor head.** -/
theorem ntree_spineTyped_nil : ntreeRestore.SpineTyped ntreeAux F₂ ``List.nil 1 := by
  have hN : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.const ``NTree [.param 0])
      (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
    .const (ntreeF₂_ntree hF₁ hF₂) (by decide) rfl
  have hb : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.bvar 0)
      (.sort (.succ (.param 0))) := .bvar .zero
  have hnil : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.const ``List.nil [.param 0])
      (.forallE (.sort (.succ (.param 0))) (.app (.const ``List [.param 0]) (.bvar 0))) :=
    .const (ntreeF₂_nil h hF₁ hF₂) (by decide) rfl
  exact ⟨_, hnil.app (hN.app hb)⟩

include h hF₁ hF₂ in
/-- **…and at the `cons` constructor head**, whose declared type genuinely uses the parameter
in two field positions. -/
theorem ntree_spineTyped_cons : ntreeRestore.SpineTyped ntreeAux F₂ ``List.cons 1 := by
  have hN : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.const ``NTree [.param 0])
      (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
    .const (ntreeF₂_ntree hF₁ hF₂) (by decide) rfl
  have hb : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.bvar 0)
      (.sort (.succ (.param 0))) := .bvar .zero
  have hcons : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.const ``List.cons [.param 0])
      (.forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const ``List [.param 0]) (.bvar 1))
            (.app (.const ``List [.param 0]) (.bvar 2))))) :=
    .const (ntreeF₂_cons h hF₁ hF₂) (by decide) rfl
  exact ⟨_, hcons.app (hN.app hb)⟩

include h hF₁ hF₂ in
/-- **§3's transport, firing at the witness.**  The datum, stated once at `ntreeAux.uvars = 1`
over the parameter telescope, arrives at `ntreeAux.recUvars = 2` over
`(ntreeAux.atRecTele ntreeAux.params).reverse` — the context `MotiveHargs` and
`MinorCtorHargs` bind their head typing in.  So the transport is not merely stated. -/
theorem ntree_headTyped_atRec :
    F₂.HasType ntreeAux.recUvars ((ntreeAux.atRecTele ntreeAux.params).reverse)
      (ntreeAux.atRec (ntreeRestore.tyBody ntreeAux 1))
      (ntreeAux.atRec (.sort (.succ (.param 0)))) :=
  VIndRestore.spineTypedAt_atRec (ntree_spineTypedAt_ty h hF₁ hF₂)

end

/-! #### The boundary: the datum is FALSE at the pre-block environment

This is why §8.7 states `hargs` at `e₂` and not at `env`, and it is a hard constraint on where
the datum can come from: the presented spine `List.{u} (NTree.{u} #0)` mentions `NTree`, a
constant the step **declares**.  Any account of the datum that reads it off the pre-block
environment alone is therefore refuted, at a real parameterised nested block. -/

theorem ntree_not_spineTyped_pre {env₁ : VEnv}
    (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ¬ ntreeRestore.SpineTyped ntreeAux env₁ ``List 1 := by
  rintro ⟨B, hB⟩
  have hfresh : env₁.constants ``NTree = none := by
    rw [VEnv.addInduct'_constants_of_not_mem h (by decide)]; rfl
  have hctx : CtxConstsIn env₁.contains ntreeAux.params.reverse := ⟨⟨⟩, trivial⟩
  have := (hB.constsIn (listEnv_ordered h).constsIn hctx).1
  obtain ⟨-, hNT⟩ := this
  obtain ⟨ci, hci⟩ := hNT.1
  exact absurd (hfresh.symm.trans hci) (by simp)

end InductiveDeclExamples

/-! ## §8 Where the datum comes from: a clause on the *occurrence*, not on the step

The datum is data — `VIndRestore.instAt_indep_of_tyArgs` (`Theory/Inductive/NestedRules.lean`
§8.7) shows `Faithful` cannot produce it, and §7's `ntree_not_spineTyped_pre` shows it is not a
fact about the pre-block environment at all.  The question the brief poses is *where it is
supplied from*.

`VInductDecl'.Built` (`Theory/Inductive/NestedBuild.lean`) is the only structure in `Theory/`
that pins `R.tyArgs` to anything: `Built.tyArgs` says `R.tyArgs j = (occ j).args`, the argument
spine of the nested occurrence the elimination pass read out of the source.  So the datum's home
is a clause on `VNestedOcc`, alongside `OccursN.args_noNested` — and `OccursN`'s docstring
already records the design rule for such a clause: it must be *satisfiable across the step*, so
it is stated at the environment the step produces.

`ArgsTyped` below is that clause, and §8's two theorems show it is enough: `Built` + `ArgsTyped`
gives the datum at **every** presented head, type and constructor alike.  Nothing here proves
`ArgsTyped`; that is the `Verify/`-side hand-off named in `docs/handoff-hargsshared.md` §4. -/

/-- **The clause `VNestedOcc.OccursN` does not have.**  The occurrence's spine, applied to the
foreign block's member and to each of its constructors, is well typed over the new block's
parameters — in the environment the step produces (see §7's boundary theorem for why it cannot
be the pre-block one).

This is `HasArgs`-free on purpose: §2 shows the `HasArgs` form and the applied form are
equivalent, and the applied form needs no `hsplit`, no length side condition and no `e.WF`. -/
structure VNestedOcc.ArgsTyped (N : VNestedOcc) (D : VInductDecl') (e : VEnv) : Prop where
  /-- The presented type head, applied. -/
  ty : ∃ B, e.HasType D.uvars D.params.reverse
    ((VExpr.const N.tyName N.lvls).mkApp N.args) B
  /-- Each presented constructor head, applied. -/
  ctor : ∀ C ∈ N.src.ctors, ∃ B, e.HasType D.uvars D.params.reverse
    ((VExpr.const C.name N.lvls).mkApp N.args) B

namespace VInductDecl'

variable {D : VInductDecl'} {R : VIndRestore} {K : List Name} {env e : VEnv}
  {occ : Nat → VNestedOcc}

/-- **THE DATUM AT THE TYPE HEAD, FROM `Built` AND THE OCCURRENCE CLAUSE.** -/
theorem Built.spineTyped_ty (hB : D.Built R K env occ)
    (hAT : ∀ j T, D.types[j]? = some T → T.name ∈ K → (occ j).ArgsTyped D e)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K) :
    R.SpineTyped D e (R.tyName j) j := by
  obtain ⟨B, hBt⟩ := (hAT j T hT hK).ty
  refine ⟨B, ?_⟩
  show e.HasType D.uvars D.params.reverse
    ((VExpr.const (R.tyName j) (R.tyLvls j)).mkApp (R.tyArgs j)) B
  rw [hB.tyName j T hT hK, hB.tyLvls j T hT hK, hB.tyArgs j T hT hK]
  exact hBt

/-- **…AND AT EVERY CONSTRUCTOR HEAD.**  The bridge is `Built.member` (the companion member's
constructor list *is* `J`'s, mapped) composed with `Built.ctorName_inv` (the naming residue), so
the conclusion is stated at `R.ctorName C.name` — the form `MinorCtorHargs` consumes. -/
theorem Built.spineTyped_ctor (hB : D.Built R K env occ)
    (hAT : ∀ j T, D.types[j]? = some T → T.name ∈ K → (occ j).ArgsTyped D e)
    {j : Nat} {T : VIndType} (hT : D.types[j]? = some T) (hK : T.name ∈ K)
    {C : VIndCtor} (hC : C ∈ T.ctors) :
    R.SpineTyped D e (R.ctorName C.name) j := by
  have hm := hB.member j T hT hK
  rw [hm] at hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
  obtain ⟨B, hBt⟩ := (hAT j T hT hK).ctor C₀ hC₀
  refine ⟨B, ?_⟩
  show e.HasType D.uvars D.params.reverse
    ((VExpr.const (R.ctorName ((occ j).ctor D.header R C₀).name) (R.tyLvls j)).mkApp
      (R.tyArgs j)) B
  rw [show ((occ j).ctor D.header R C₀).name = (occ j).ctorName C₀.name from rfl,
    hB.ctorName_inv j T hT hK C₀ hC₀, hB.tyLvls j T hT hK, hB.tyArgs j T hT hK]
  exact hBt

end VInductDecl'

/-! ## §8b The `HasArgs` form of the clause, and why it is the one to supply

§10's axiom audit records a taint that matters: `hargs_of_spineTyped` — §2's **backward**
direction — carries `sorryAx`, because `VEnv.HasArgs.of_mkApp` does (`Theory/Typing/SpineInv.lean`
says so in its own docstring: it uses `IsDefEqU.forallE_inv`, i.e. the Π-inversion hole).  §2's
**forward** direction is hole-free.

So the two forms of the datum are *not* interchangeable for the purpose of counting holes:

* supply it in **`HasArgs` form** and every consumer is hole-free — §8.7 takes that form
  directly, and §5/§6's applied form follows by the forward direction;
* supply it in **applied form** and §8.7 costs the Π-inversion hole.

`ArgsTypedH` is therefore the clause to put on the occurrence record, and `toArgsTyped` is the
hole-free descent to §8's form.

**And the taint is worse than a hole count.**  `NestedTele.lean` §T12's "the `PiInv` line" and
§T15/§T16's repeated "nothing here uses `HasArgs.of_mkApp'`, so the cone stays `PiInv`-free" are
a deliberate invariant of the whole nested corner.  `hargs_of_spineTyped` is the first use of
`HasArgs.of_mkApp` in it.  Supplying the datum in applied form would therefore not merely add a
hole — it would put the nested corner behind `VEnv.WF` and `PiInv`, which §T12 says explicitly
it is avoiding.  Supplying it in `HasArgs` form costs nothing. -/

namespace VEnv

/-- The restoration-free core of §2's forward direction: a declared constant applied to a spine
that instantiates the first `np` binders of its declared type is well typed.  `hsplit` does not
appear — §2's `hsplit_free`. -/
theorem headApp_hasType {e : VEnv} {U : Nat} {Γ : List VExpr} {n : Name} {ls : List VLevel}
    {ci : VConstant} {as : List VExpr} {np : Nat}
    (hci : e.constants n = some ci) (hlvl : ∀ l ∈ ls, l.WF U) (huv : ls.length = ci.uvars)
    (hargs : e.HasArgs U Γ (splitPis np (ci.type.instL ls)).1 as) :
    e.HasType U Γ ((VExpr.const n ls).mkApp as)
      (VExpr.instAll (splitPis np (ci.type.instL ls)).2 as) := by
  have hconst := VEnv.HasType.const (Γ := Γ) (U := U) hci hlvl huv
  rw [(VExpr.mkPi_splitPis np (ci.type.instL ls)).symm] at hconst
  exact VEnv.HasType.mkApp' hargs hconst

end VEnv

/-- **The occurrence clause in `HasArgs` form.**  The spine instantiates the foreign block's
parameter telescope, at the member's declared type and at each of its constructors' declared
types.  (Those telescopes are `J.params` and each `C.params` respectively — equal only
definitionally, F3, which is why both clauses are here rather than one.) -/
structure VNestedOcc.ArgsTypedH (N : VNestedOcc) (D : VInductDecl') (e : VEnv) : Prop where
  lvls : ∀ l ∈ N.lvls, l.WF D.uvars
  ty : e.HasArgs D.uvars D.params.reverse
    (splitPis N.decl.np (N.src.type.instL N.lvls)).1 N.args
  ctor : ∀ C ∈ N.src.ctors, e.HasArgs D.uvars D.params.reverse
    (splitPis N.decl.np ((C.type N.decl N.idx).instL N.lvls)).1 N.args

/-- **…and its hole-free descent to §8's form**, using only `Occurs`' two lookups and its
`lvls_len`. -/
theorem VNestedOcc.ArgsTypedH.toArgsTyped {N : VNestedOcc} {D : VInductDecl'} {env e : VEnv}
    (hAT : N.ArgsTypedH D e) (ho : N.Occurs env) (hle : env ≤ e) : N.ArgsTyped D e where
  ty := ⟨_, VEnv.headApp_hasType (hle.constants ho.ty_const) hAT.lvls ho.lvls_len hAT.ty⟩
  ctor := fun C hC =>
    ⟨_, VEnv.headApp_hasType (hle.constants (ho.ctor_const C hC)) hAT.lvls ho.lvls_len
      (hAT.ctor C hC)⟩

/-! ## §9 §8's clause is jointly inhabited with `Built`, at a parameterised nested block

Ledger row 205's lesson: check the hypothesis set is **jointly** inhabited, not each hypothesis
alone.  `ntreeAux_built` (`Theory/Inductive/NestedBuild.lean`) and §7's three typings hold at the
same block, the same `R`, the same `occ` and the same staging; §9's last theorem runs §8's
producer on them and gets the datum out. -/

namespace InductiveDeclExamples

section
variable {env₁ F₁ F₂ : VEnv}
variable (h : VEnv.empty.addInduct' listDecl = some env₁)
variable (hF₁ : env₁.addConstList (ntreeAux.typeConstsC ntreeK) = some F₁)
variable (hF₂ : F₁.addConstList (ntreeAux.ctorConstsCR ntreeRestore ntreeK) = some F₂)

include h hF₁ hF₂ in
/-- **§8's occurrence clause, at the real occurrence `List (NTree α)`.**  All three components —
the type head and both constructor heads — at one environment. -/
theorem ntree_listOcc_argsTyped : listOcc.ArgsTyped ntreeAux F₂ where
  ty := ⟨_, ntree_spineTypedAt_ty h hF₁ hF₂⟩
  ctor := by
    intro C hC
    simp only [show listOcc.src.ctors = [listNil, listCons] from rfl, List.mem_cons,
      List.not_mem_nil, or_false] at hC
    obtain rfl | rfl := hC
    · exact ntree_spineTyped_nil h hF₁ hF₂
    · exact ntree_spineTyped_cons h hF₁ hF₂

include hF₁ hF₂ in
/-- **§8b's clause in `HasArgs` form, at the real occurrence** — the form that keeps every
consumer hole-free.  All three telescopes are `List`'s single parameter binder, so the same
`HasArgs` serves the member and both of its constructors. -/
theorem ntree_listOcc_argsTypedH : listOcc.ArgsTypedH ntreeAux F₂ := by
  have hN : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.const ``NTree [.param 0])
      (.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))) :=
    .const (ntreeF₂_ntree hF₁ hF₂) (by decide) rfl
  have hb : F₂.HasType 1 [VExpr.sort (.succ (.param 0))] (.bvar 0)
      (.sort (.succ (.param 0))) := .bvar .zero
  have harg : F₂.HasArgs 1 ntreeAux.params.reverse [VExpr.sort (.succ (.param 0))]
      listOcc.args := .cons (hN.app hb) .nil
  refine ⟨by decide, harg, fun C hC => ?_⟩
  simp only [show listOcc.src.ctors = [listNil, listCons] from rfl, List.mem_cons,
    List.not_mem_nil, or_false] at hC
  obtain rfl | rfl := hC
  · exact harg
  · exact harg

include h hF₁ hF₂ in
/-- …and §8b's descent, so §8's clause is available **hole-free** at the witness. -/
theorem ntree_listOcc_argsTyped_of_H : listOcc.ArgsTyped ntreeAux F₂ :=
  (ntree_listOcc_argsTypedH hF₁ hF₂).toArgsTyped (listOcc_occurs h).toOccurs
    ((VEnv.addConstList_le hF₁).trans (VEnv.addConstList_le hF₂))

include h hF₁ hF₂ in
/-- **END TO END: `Built` + §8's clause ⟹ the datum, at `ntreeAux`.**  This is the joint
inhabitation check: the two hypothesis families of `Built.spineTyped_ty` hold simultaneously at
one block, and the producer fires. -/
theorem ntree_datum_of_built :
    ntreeRestore.SpineTyped ntreeAux F₂ (ntreeRestore.tyName 1) 1 :=
  (ntreeAux_built h).spineTyped_ty
    (fun _ _ _ _ => ntree_listOcc_argsTyped h hF₁ hF₂)
    (show ntreeAux.types[1]? = some (listOcc.member ntreeAux.header ntreeRestore) from rfl)
    (by decide)

include h hF₁ hF₂ in
/-- …and at the constructor heads, through `Built.member` + `Built.ctorName_inv`. -/
theorem ntree_datum_of_built_ctor (C : VIndCtor)
    (hC : C ∈ (listOcc.member ntreeAux.header ntreeRestore).ctors) :
    ntreeRestore.SpineTyped ntreeAux F₂ (ntreeRestore.ctorName C.name) 1 :=
  (ntreeAux_built h).spineTyped_ctor
    (fun _ _ _ _ => ntree_listOcc_argsTyped h hF₁ hF₂)
    (show ntreeAux.types[1]? = some (listOcc.member ntreeAux.header ntreeRestore) from rfl)
    (by decide) hC

end

/-! ### §9b Non-degeneracy of the witness, `decide`-checked

The datum could be uninteresting for three separate reasons; all three are excluded here. -/

/-- The parameter telescope is **not** empty, so the datum is not the `D.np = 0` statement. -/
theorem ntree_np_pos : 0 < ntreeAux.np := by decide

/-- The presented spine is **not** empty, so the `HasArgs` of §2 is not `.nil`. -/
theorem ntree_tyArgs_ne_nil : ntreeRestore.tyArgs 1 ≠ [] := by decide

/-- The presentation is **not** the identity one: `R.tyArgs 1` is not the parameter run, so this
is not `VInductDecl'.idRestore` in disguise. -/
theorem ntree_tyArgs_ne_bvars :
    ntreeRestore.tyArgs 1 ≠ VExpr.bvars 0 ntreeAux.np := by decide

/-- …and the presented head is a **foreign** constant, not the block's own member name. -/
theorem ntree_tyName_ne_own :
    ntreeRestore.tyName 1 ≠ (ntreeAux.types.getD 1 default).name := by decide

end InductiveDeclExamples

/-! ## §10 Axiom audit -/

#print axioms Lean4Lean.VIndRestore.spineTypedAt_of_hargs
#print axioms Lean4Lean.VIndRestore.hargs_of_spineTyped
#print axioms Lean4Lean.VIndRestore.spineTypedAt_atRec
#print axioms Lean4Lean.VIndRestore.spineTypedAt_append
#print axioms Lean4Lean.VIndRestore.motiveHargs_iff
#print axioms Lean4Lean.VIndRestore.minorCtorHargs_iff
#print axioms Lean4Lean.VIndRestore.motiveHargs_of_spineTypedAt
#print axioms Lean4Lean.VIndRestore.minorCtorHargs_of_spineTypedAt
#print axioms Lean4Lean.VIndRestore.substC_tyApp_defeq_tyAppR_of_spineTypedAt
#print axioms Lean4Lean.VIndRestore.tyVal_hasType_of_spineTyped
#print axioms Lean4Lean.VInductDecl'.Built.spineTyped_ty
#print axioms Lean4Lean.VInductDecl'.Built.spineTyped_ctor
#print axioms Lean4Lean.InductiveDeclExamples.ntree_spineTypedAt_ty
#print axioms Lean4Lean.InductiveDeclExamples.ntree_spineTypedAt_ty_inhabited
#print axioms Lean4Lean.InductiveDeclExamples.ntree_spineTyped_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntree_spineTyped_cons
#print axioms Lean4Lean.InductiveDeclExamples.ntree_headTyped_atRec
#print axioms Lean4Lean.InductiveDeclExamples.ntree_not_spineTyped_pre
#print axioms Lean4Lean.InductiveDeclExamples.ntree_listOcc_argsTyped
#print axioms Lean4Lean.InductiveDeclExamples.ntree_datum_of_built
#print axioms Lean4Lean.InductiveDeclExamples.ntree_datum_of_built_ctor
#print axioms Lean4Lean.VIndRestore.hsplit_free
#print axioms Lean4Lean.VEnv.headApp_hasType
#print axioms Lean4Lean.VNestedOcc.ArgsTypedH.toArgsTyped
#print axioms Lean4Lean.VIndRestore.tyVal_hasType_of_hargs
#print axioms Lean4Lean.InductiveDeclExamples.ntree_listOcc_argsTypedH
#print axioms Lean4Lean.InductiveDeclExamples.ntree_listOcc_argsTyped_of_H
#print axioms Lean4Lean.InductiveDeclExamples.ntree_np_pos
#print axioms Lean4Lean.InductiveDeclExamples.ntree_tyArgs_ne_nil
#print axioms Lean4Lean.InductiveDeclExamples.ntree_tyArgs_ne_bvars
#print axioms Lean4Lean.InductiveDeclExamples.ntree_tyName_ne_own
