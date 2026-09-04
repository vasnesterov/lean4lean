import Lean4Lean.Verify.Inductive.TrExprSGeneral

/-!
# Is `CtorsInFragment` a restriction?  Yes — and here are three declarations that prove it

`Verify/Inductive/TrExprSGeneral.lean` discharges `TrIndDeclN.trCtors` for every block satisfying
`CtorsInFragment`, a *checkable* predicate: every constructor type is built from
`.sort | .bvar | .const | .app | .forallE | .mdata`, every `.const` leaf is in `Γc`, and every
application's function has a **syntactically** `∀` inferred type.  That file's §6 costs the six
omitted `Expr` constructors and asserts, in prose, that

* "`.lam` … the reason it is omitted is that a constructor type never has one", and
* of `.proj`, `.lit`, `.fvar`: "none of them occurs in a constructor type".

## §0 The verdict, up front

**Both prose claims are false, and `CtorsInFragment` is a real restriction with two independent
escape routes.**  §2 exhibits three inductive declarations that Lean's own C++ kernel accepts and
whose stored constructor types contain, respectively, `.lit`, `.lam` and `.letE`:

| declaration | stored constructor type | offending head |
| --- | --- | --- |
| `FragEx.WithLit.mk` | `Fin 3 → FragEx.WithLit` | `.lit (.natVal 3)` |
| `FragEx.WithLam.mk` | `{ n // n = n } → FragEx.WithLam` | `.lam` |
| `FragEx.WithLet.mk` | `(let n := 3; Fin n) → FragEx.WithLet` | `.letE` (elaboration does *not* zeta-reduce it) |

and §5 exhibits a fourth escape that uses **only** the six allowed heads: an application whose
function's stored type is a constant that merely *unfolds* to a `∀`.  That one is the real
boundary, and it is the one that cannot be widened without a conversion check.

Because §1's escape theorem is stated at **every** `Γc`, `Us` and `Γ`, none of these is an
artefact of a badly chosen environment: `¬ CtorsInFragment Γc Us [block]` holds universally.

## §0a What this file then does about it

§3 widens the inferencer to `.lam` and `.lit` — both without any new hypothesis and without any
conversion check — and §4 re-derives the field producer over the widened fragment.  §6 says
exactly where the remaining boundary is and why each remaining exclusion is not bookkeeping.
§7 is the arity-0 witness at `InductiveDeclExamples.ntreeAux`.

Structural exclusions: this file imports only `Verify/Inductive/TrExprSGeneral`, so
`Verify/Inductive/FlipConstruct` (hence `tr_ntreeNodeType`) and `Verify/Inductive/TrTypeProducer`
are **not in the import closure at all**, and §7's witness cannot be using them.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

/-! ## §1 The fragment as a decidable predicate, and the escape theorem

`ctorTr?` returning `none` at one `Γc` proves nothing (the constant might just be missing).  What
is needed to settle (a) is the converse direction: *success forces syntactic membership*, so
failure of membership forces `none` **at every environment**.  That is `inFragment_of_ctorTr?`
below, and it is what makes §2's counterexamples environment-independent. -/

/-- The syntactic half of `ctorTr?`'s domain: the six heads it recurses through, as a `Bool` so
that membership at a concrete constructor type is `rfl`. -/
def inFragment : Expr → Bool
  | .sort _ => true
  | .bvar _ => true
  | .const _ _ => true
  | .app f a => inFragment f && inFragment a
  | .forallE _ d b _ => inFragment d && inFragment b
  | .mdata _ e => inFragment e
  | _ => false

/-- **Success forces syntactic membership.**  Note this is *only* the syntactic half: the
converse fails (§5), so `inFragment` is necessary and not sufficient. -/
theorem inFragment_of_ctorTr? {Γc : Name → Option VConstant} {Us : List Name} :
    ∀ {e : Expr} {Γ : List VExpr} {p : VExpr × VExpr},
      ctorTr? Γc Us e Γ = some p → inFragment e = true := by
  intro e
  induction e with
  | sort | bvar | const => intros; rfl
  | app f a ihf iha =>
    intro Γ p h
    simp only [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, r, hr, _⟩ := h
    simp [inFragment, ihf hq, iha hr]
  | forallE _ d b _ ihd ihb =>
    intro Γ p h
    simp only [ctorTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, _, _, r, hr, _⟩ := h
    simp [inFragment, ihd hq, ihb hr]
  | mdata _ e ih =>
    intro Γ p h
    rw [show ctorTr? Γc Us (.mdata _ e) Γ = ctorTr? Γc Us e Γ from rfl] at h
    simpa [inFragment] using ih h
  | fvar | mvar | lam | letE | lit | proj => intro Γ p h; simp [ctorTr?] at h

/-- …hence the contrapositive, which is the form §2 uses: a constructor type carrying any head
outside the six is outside the fragment at **every** environment, universe context and telescope
depth.  No `Γc` can rescue it. -/
theorem ctorTr?_eq_none_of_not_inFragment {e : Expr} (h : inFragment e = false)
    (Γc : Name → Option VConstant) (Us : List Name) (Γ : List VExpr) :
    ctorTr? Γc Us e Γ = none := by
  cases hc : ctorTr? Γc Us e Γ with
  | none => rfl
  | some p => rw [inFragment_of_ctorTr? hc] at h; exact absurd h Bool.noConfusion

/-- …and lifted to a block: one bad constructor type kills `CtorsInFragment` universally. -/
theorem not_ctorsInFragment_of_ctor {types : List InductiveType} {j q : Nat}
    {t : InductiveType} {c : Constructor}
    (ht : types[j]? = some t) (hc : t.ctors[q]? = some c) (h : inFragment c.type = false)
    (Γc : Name → Option VConstant) (Us : List Name) : ¬ CtorsInFragment Γc Us types := by
  intro H
  obtain ⟨p, hp⟩ := H j t ht q c hc
  rw [ctorTr?_eq_none_of_not_inFragment h] at hp
  exact absurd hp nofun

/-! ## §2 Three well-formed declarations outside the fragment

Each block below is an ordinary `inductive`.  Its presence in the compiled environment *is* the
certificate that Lean's own C++ kernel type-checked it — nothing here is hand-transcribed, because
every constructor type enters through `exprOf%`, which splices the **stored** `Expr`.

This is the part that contradicts `TrExprSGeneral.lean`'s §6 prose.  It is a correction to a
comment, not to a theorem: every theorem in that file is conditional on `hfrag`, so none of them
is wrong.  What was wrong is the belief that `hfrag` is free. -/

namespace FragEx

/-- `.lit` in a constructor type: the `3` of `Fin 3` is a raw `Nat` literal.  The elaborator emits
`@OfNat.ofNat Nat 3 (instOfNatNat 3)` and does **not** reduce `instOfNatNat`, so two `.lit`s
survive into the stored type. -/
inductive WithLit : Type where
  | mk : Fin 3 → WithLit

/-- `.lam` in a constructor type: `Subtype`'s predicate argument is a lambda. -/
inductive WithLam : Type where
  | mk : { n : Nat // n = n } → WithLam

/-- `.letE` in a constructor type: elaboration does not zeta-reduce a `let` in a type. -/
inductive WithLet : Type where
  | mk : (let n := 3; Fin n) → WithLet

/-- None of the three is degenerate: each is inhabited, so each is a type a user could actually
have written and used. -/
example : WithLit := .mk ⟨0, by omega⟩
example : WithLam := .mk ⟨0, rfl⟩
example : WithLet := .mk ⟨0, by omega⟩

/-! ### §2a The three stored constructor types, and their fragment verdicts

`rfl` on `inFragment` — a computation on the spliced literal, so the failure is not asserted. -/

theorem withLit_not_inFragment : inFragment (exprOf% WithLit.mk) = false := rfl
theorem withLam_not_inFragment : inFragment (exprOf% WithLam.mk) = false := rfl
theorem withLet_not_inFragment : inFragment (exprOf% WithLet.mk) = false := rfl

/-- …while the two nested blocks of `TrExprSGeneral.lean` §4b *are* in the syntactic half, so
`inFragment` is not a predicate that fails on everything. -/
theorem ntreeNode_inFragment : inFragment (exprOf% InductiveDeclExamples.NTree.node) = true := rfl
theorem nfnNode_inFragment :
    inFragment (exprOf% InductiveDeclExamples.NFn.node) = true := rfl

/-! ### §2b The blocks, and the universal failure of `CtorsInFragment` -/

def withLitIndType : InductiveType :=
  { name := ``WithLit, type := exprOf% WithLit,
    ctors := [{ name := ``WithLit.mk, type := exprOf% WithLit.mk }] }

def withLamIndType : InductiveType :=
  { name := ``WithLam, type := exprOf% WithLam,
    ctors := [{ name := ``WithLam.mk, type := exprOf% WithLam.mk }] }

def withLetIndType : InductiveType :=
  { name := ``WithLet, type := exprOf% WithLet,
    ctors := [{ name := ``WithLet.mk, type := exprOf% WithLet.mk }] }

/-- **(a), SETTLED NEGATIVELY.**  `CtorsInFragment` fails at this real block for **every**
`Γc` and every `Us`.  So `CtorsInFragment` is a genuine restriction on `TrIndDeclN.trCtors`'s
coverage, not a vacuous side condition, and `trIndDeclN_of_ownId` is a theorem about a proper
subclass of well-formed declarations. -/
theorem withLit_not_ctorsInFragment (Γc : Name → Option VConstant) (Us : List Name) :
    ¬ CtorsInFragment Γc Us [withLitIndType] :=
  not_ctorsInFragment_of_ctor (j := 0) (q := 0) rfl rfl withLit_not_inFragment Γc Us

theorem withLam_not_ctorsInFragment (Γc : Name → Option VConstant) (Us : List Name) :
    ¬ CtorsInFragment Γc Us [withLamIndType] :=
  not_ctorsInFragment_of_ctor (j := 0) (q := 0) rfl rfl withLam_not_inFragment Γc Us

theorem withLet_not_ctorsInFragment (Γc : Name → Option VConstant) (Us : List Name) :
    ¬ CtorsInFragment Γc Us [withLetIndType] :=
  not_ctorsInFragment_of_ctor (j := 0) (q := 0) rfl rfl withLet_not_inFragment Γc Us

end FragEx

/-! ## §3 The widened inferencer: `.lam` and nat literals, still with no conversion check

Two of §2's three escapes close for free, in the strong sense that the widened soundness theorem
takes **exactly** `ConstLookup` — the same hypothesis as `ctorTr?_sound` — and no `VEnv.Ordered`,
no `VEnv.HasPrimitives`, no `IsDefEq` anywhere.

* `.lam`: the body's inferred type is *abstracted* into a `.forallE`, which is `VEnv.HasType.lam`
  read forwards.  `TrExprS.lam`'s `IsType` premise is the domain's `sortOf?`, exactly as
  `.forallE`'s already is.  Nothing new is needed and nothing is assumed.
* `.lit (.natVal n)`: `TrExprS.lit`'s `ContainsLits` premise is `env.contains ``Nat`, which a
  single `Γc` lookup supplies; the translation is the repo's `VExpr.natLit n`, and its typing
  derivation is an induction on `n` from the *stored types* of `Nat.zero` and `Nat.succ`.  The
  repo already has `TrExprS.trLiteral`, which does both literal kinds — but it costs
  `VEnv.Ordered` **and** `VEnv.HasPrimitives` (measured: cone 4938, clean, no watched
  declarations).  Deriving the nat case directly from `ConstLookup` keeps §3's hypothesis
  identical to §2b's, which is the whole point of the inferencer design.

`.lit (.strVal _)` is deliberately left out: it is the *same idea* with five constants
(`Char`, `Char.ofNat`, `List.nil`, `List.cons`, `String.ofList`) instead of two, so it is
bookkeeping rather than a new premise — but it is bookkeeping this round did not pay for, and a
string literal in a *constructor type* is rarer than a numeral.  §6 records that. -/

/-- The lookups a nat literal needs.  `Nat` is what `VEnv.ContainsLits` demands; `Nat.zero` and
`Nat.succ` have their **stored types pinned**, which is what removes the conversion: the `.app`
in `natLit (n+1)` reads its `∀` off `Nat.succ`'s stored type. -/
def natLitOk? (Γc : Name → Option VConstant) : Option Unit :=
  (Γc ``Nat).bind fun _ =>
  (Γc ``Nat.zero).bind fun cz =>
  (Γc ``Nat.succ).bind fun cs =>
  if cz.uvars = 0 ∧ cz.type = .nat ∧ cs.uvars = 0 ∧ cs.type = .forallE .nat .nat
  then some () else none

/-- **The widened inferencer.**  `ctorTr?` plus a `.lam` case and a nat-literal case.  Every other
case is character-for-character the same, so the widening is visibly conservative. -/
def ctorTrW? (Γc : Name → Option VConstant) (Us : List Name) :
    Expr → List VExpr → Option (VExpr × VExpr)
  | .sort u, _ => (VLevel.ofLevel Us u).map fun u' => (.sort u', .sort (.succ u'))
  | .bvar i, Γ => (bvarCtx Γ).find? (.inl i)
  | .const c us, _ =>
    (Γc c).bind fun ci =>
    (us.mapM (VLevel.ofLevel Us)).bind fun us' =>
    if us.length = ci.uvars then some (.const c us', ci.type.instL us') else none
  | .app f a, Γ =>
    (ctorTrW? Γc Us f Γ).bind fun p =>
    (ctorTrW? Γc Us a Γ).bind fun q =>
    (piOf? p.2).bind fun AB =>
    if AB.1 = q.2 then some (.app p.1 q.1, AB.2.inst q.1) else none
  | .forallE _ d b _, Γ =>
    (ctorTrW? Γc Us d Γ).bind fun p =>
    (sortOf? p.2).bind fun u =>
    (ctorTrW? Γc Us b (p.1 :: Γ)).bind fun q =>
    (sortOf? q.2).map fun v => (.forallE p.1 q.1, .sort (.imax u v))
  | .lam _ d b _, Γ =>
    (ctorTrW? Γc Us d Γ).bind fun p =>
    (sortOf? p.2).bind fun _ =>
    (ctorTrW? Γc Us b (p.1 :: Γ)).map fun q => (.lam p.1 q.1, .forallE p.1 q.2)
  | .lit (.natVal n), _ => (natLitOk? Γc).map fun _ => (.natLit n, .nat)
  | .mdata _ e, Γ => ctorTrW? Γc Us e Γ
  | _, _ => none

/-- The widened fragment, syntactically. -/
def inFragmentW : Expr → Bool
  | .sort _ => true
  | .bvar _ => true
  | .const _ _ => true
  | .app f a => inFragmentW f && inFragmentW a
  | .forallE _ d b _ => inFragmentW d && inFragmentW b
  | .lam _ d b _ => inFragmentW d && inFragmentW b
  | .lit (.natVal _) => true
  | .mdata _ e => inFragmentW e
  | _ => false

/-- The widening is a widening: everything the old fragment accepts, the new one does. -/
theorem inFragmentW_of_inFragment : ∀ {e : Expr}, inFragment e = true → inFragmentW e = true
  | .sort _, _ | .bvar _, _ | .const .., _ => rfl
  | .app f a, h => by
    simp only [inFragment, Bool.and_eq_true] at h
    simp [inFragmentW, inFragmentW_of_inFragment h.1, inFragmentW_of_inFragment h.2]
  | .forallE _ d b _, h => by
    simp only [inFragment, Bool.and_eq_true] at h
    simp [inFragmentW, inFragmentW_of_inFragment h.1, inFragmentW_of_inFragment h.2]
  | .mdata _ e, h => inFragmentW_of_inFragment (e := e) h

/-! ### §3a The nat-literal case, from `ConstLookup` alone -/

/-- **`TrExprS` and `HasType` for every nat literal, at every `VLCtx`, from three lookups.**
`TrExprS.trLiteral` proves the same thing for both literal kinds but wants `VEnv.Ordered` and
`VEnv.HasPrimitives`; this wants neither, which is why the widened §3b keeps §2b's hypothesis. -/
theorem trExprS_natLit {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    (hΓc : ConstLookup Γc env) (hok : natLitOk? Γc = some ()) :
    ∀ (Δ : VLCtx) (n : Nat), TrExprS env Us Δ (.lit (.natVal n)) (.natLit n) ∧
      env.HasType Us.length Δ.toCtx (.natLit n) .nat := by
  simp only [natLitOk?, Option.bind_eq_some_iff] at hok
  obtain ⟨cn, hn, ⟨zu, zt⟩, hz, ⟨su, st⟩, hs, hok⟩ := hok
  split at hok
  · next heq =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    have hzc := hΓc _ _ hz
    have hsc := hΓc _ _ hs
    have hlits : ∀ m : Nat, env.ContainsLits (.natVal m) := fun _ => ⟨cn, hΓc _ _ hn⟩
    intro Δ n
    induction n with
    | zero =>
      refine ⟨.lit (hlits 0) ?_, ?_⟩
      · exact .const hzc rfl rfl
      · exact VEnv.HasType.const (ci := ⟨0, .nat⟩) hzc nofun rfl
    | succ n ih =>
      have hsucc : env.HasType Us.length Δ.toCtx .natSucc (.forallE .nat .nat) :=
        VEnv.HasType.const (ci := ⟨0, .forallE .nat .nat⟩) hsc nofun rfl
      refine ⟨.lit (hlits (n+1)) ?_, ?_⟩
      · exact .app hsucc ih.2 (.const hsc rfl rfl) ih.1
      · exact hsucc.app ih.2
  · exact absurd hok nofun

/-! ### §3b Soundness of the widened inferencer, from the same hypothesis

Word for word `ctorTr?_sound`'s statement, with `ctorTrW?` in place of `ctorTr?`.  The hypothesis
is unchanged: `ConstLookup Γc env`, a conjunction of `VEnv.constants` equations. -/

theorem ctorTrW?_sound {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    (hΓc : ConstLookup Γc env) :
    ∀ {e : Expr} {Γ : List VExpr} {e' t' : VExpr}, ctorTrW? Γc Us e Γ = some (e', t') →
      TrExprS env Us (bvarCtx Γ) e e' ∧ env.HasType Us.length Γ e' t' := by
  intro e
  induction e with
  | sort u =>
    intro Γ e' t' h
    simp [ctorTrW?, Option.map_eq_some_iff] at h
    obtain ⟨u', hu, rfl, rfl⟩ := h
    exact ⟨.sort hu, .sort (VLevel.WF.of_ofLevel hu)⟩
  | bvar i =>
    intro Γ e' t' h
    rw [show ctorTrW? Γc Us (.bvar i) Γ = (bvarCtx Γ).find? (.inl i) from rfl] at h
    obtain ⟨rfl, hl⟩ := bvarCtx_find? h
    exact ⟨.bvar h, .bvar hl⟩
  | const c us =>
    intro Γ e' t' h
    simp only [ctorTrW?, Option.bind_eq_some_iff] at h
    obtain ⟨ci, hci, us', hus, h⟩ := h
    split at h
    · next hlen =>
      cases h
      exact ⟨.const (hΓc _ _ hci) hus hlen,
        .const (hΓc _ _ hci) (VLevel.WF.of_mapM_ofLevel hus)
          ((List.Forall₂.length_eq (List.mapM_eq_some.1 hus)).symm.trans hlen)⟩
    · exact absurd h nofun
  | app f a ihf iha =>
    intro Γ e' t' h
    simp only [ctorTrW?, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, q, hq, AB, hAB, h⟩ := h
    split at h
    · next heq =>
      cases h
      obtain ⟨htf, hTf⟩ := ihf hp
      obtain ⟨hta, hTa⟩ := iha hq
      have hpi : p.2 = .forallE AB.1 AB.2 := piOf?_eq_some (by rw [hAB])
      rw [hpi] at hTf
      rw [heq] at hTf
      refine ⟨.app (by rw [bvarCtx_toCtx]; exact hTf) (by rw [bvarCtx_toCtx]; exact hTa)
        htf hta, .app hTf hTa⟩
    · exact absurd h nofun
  | forallE nm d b bi ihd ihb =>
    intro Γ e' t' h
    simp only [ctorTrW?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, u, hu, q, hq, v, hv, h⟩ := h
    cases h
    obtain ⟨htd, hTd⟩ := ihd hp
    obtain ⟨htb, hTb⟩ := ihb hq
    rw [sortOf?_eq_some hu] at hTd
    rw [sortOf?_eq_some hv] at hTb
    refine ⟨.forallE (by rw [bvarCtx_toCtx]; exact ⟨_, hTd⟩)
      (by rw [bvarCtx_toCtx]; exact ⟨_, hTb⟩) htd (by rw [← bvarCtx_cons]; exact htb),
      .forallE hTd hTb⟩
  | lam nm d b bi ihd ihb =>
    intro Γ e' t' h
    simp only [ctorTrW?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, u, hu, q, hq, h⟩ := h
    cases h
    obtain ⟨htd, hTd⟩ := ihd hp
    obtain ⟨htb, hTb⟩ := ihb hq
    rw [sortOf?_eq_some hu] at hTd
    refine ⟨.lam (by rw [bvarCtx_toCtx]; exact ⟨_, hTd⟩) htd
      (by rw [← bvarCtx_cons]; exact htb), .lam hTd hTb⟩
  | lit l =>
    intro Γ e' t' h
    match l with
    | .natVal n =>
      simp only [ctorTrW?, Option.map_eq_some_iff] at h
      obtain ⟨_, hok, h⟩ := h
      cases h
      obtain ⟨ht, hT⟩ := trExprS_natLit (Us := Us) hΓc hok (bvarCtx Γ) n
      exact ⟨ht, by rw [bvarCtx_toCtx] at hT; exact hT⟩
    | .strVal s => simp [ctorTrW?] at h
  | mdata dt e ih =>
    intro Γ e' t' h
    rw [show ctorTrW? Γc Us (.mdata dt e) Γ = ctorTrW? Γc Us e Γ from rfl] at h
    obtain ⟨ht, hT⟩ := ih h
    exact ⟨.mdata ht, hT⟩
  | fvar | mvar | letE | proj =>
    intro Γ e' t' h; simp [ctorTrW?] at h

/-- The `TrExprS` half. -/
theorem trExprS_of_ctorTrW {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    (hΓc : ConstLookup Γc env) {e : Expr} {e' t' : VExpr}
    (h : ctorTrW? Γc Us e [] = some (e', t')) : TrExprS env Us [] e e' :=
  (ctorTrW?_sound hΓc h).1

/-- The typing half — still with `VEnv.Ordered` nowhere in sight, which is the property §3 was
designed to preserve. -/
theorem ctorTrW?_hasType {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    (hΓc : ConstLookup Γc env) {e : Expr} {Γ : List VExpr} {e' t' : VExpr}
    (h : ctorTrW? Γc Us e Γ = some (e', t')) : env.HasType Us.length Γ e' t' :=
  (ctorTrW?_sound hΓc h).2

/-- The widened fragment is still `.proj`-free, so `TrExprS.unique` still applies and §4's `↔`
survives the widening.  (`TrExprS.IsUnique` is `True` at `.lit` and conjunctive at `.lam`.) -/
theorem isUnique_of_ctorTrW {Γc : Name → Option VConstant} {Us : List Name} :
    ∀ {e : Expr} {Γ : List VExpr} {p : VExpr × VExpr}, ctorTrW? Γc Us e Γ = some p →
      TrExprS.IsUnique e := by
  intro e
  induction e with
  | sort | bvar | const | lit => intro _ _ _; trivial
  | app f a ihf iha =>
    intro Γ p h
    simp only [ctorTrW?, Option.bind_eq_some_iff] at h
    obtain ⟨p₁, hp, q, hq, _⟩ := h
    exact ⟨ihf hp, iha hq⟩
  | forallE nm d b bi ihd ihb =>
    intro Γ p h
    simp only [ctorTrW?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p₁, hp, u, hu, q, hq, _⟩ := h
    exact ⟨ihd hp, ihb hq⟩
  | lam nm d b bi ihd ihb =>
    intro Γ p h
    simp only [ctorTrW?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p₁, hp, u, hu, q, hq, _⟩ := h
    exact ⟨ihd hp, ihb hq⟩
  | mdata dt e ih =>
    intro Γ p h
    rw [show ctorTrW? Γc Us (.mdata dt e) Γ = ctorTrW? Γc Us e Γ from rfl] at h
    exact ih h
  | fvar | mvar | letE | proj => intro Γ p h; simp [ctorTrW?] at h

/-- …and the widened inferencer's success still forces syntactic membership, now in the widened
fragment.  This is what keeps §5's boundary argument honest. -/
theorem inFragmentW_of_ctorTrW? {Γc : Name → Option VConstant} {Us : List Name} :
    ∀ {e : Expr} {Γ : List VExpr} {p : VExpr × VExpr},
      ctorTrW? Γc Us e Γ = some p → inFragmentW e = true := by
  intro e
  induction e with
  | sort | bvar | const => intros; rfl
  | app f a ihf iha =>
    intro Γ p h
    simp only [ctorTrW?, Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, r, hr, _⟩ := h
    simp [inFragmentW, ihf hq, iha hr]
  | forallE _ d b _ ihd ihb =>
    intro Γ p h
    simp only [ctorTrW?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, _, _, r, hr, _⟩ := h
    simp [inFragmentW, ihd hq, ihb hr]
  | lam _ d b _ ihd ihb =>
    intro Γ p h
    simp only [ctorTrW?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, _, _, r, hr, _⟩ := h
    simp [inFragmentW, ihd hq, ihb hr]
  | lit l =>
    intro Γ p h
    match l with
    | .natVal _ => rfl
    | .strVal _ => simp [ctorTrW?] at h
  | mdata _ e ih =>
    intro Γ p h
    rw [show ctorTrW? Γc Us (.mdata _ e) Γ = ctorTrW? Γc Us e Γ from rfl] at h
    simpa [inFragmentW] using ih h
  | fvar | mvar | letE | proj => intro Γ p h; simp [ctorTrW?] at h

/-- **The widening is conservative, as a computation**: wherever the old inferencer succeeds the
widened one returns the *same* pair.  So nothing that `TrExprSGeneral.lean` §4 covers is lost, and
`ctorTrW?`'s witnesses at concrete blocks are literally the old ones. -/
theorem ctorTrW?_of_ctorTr? {Γc : Name → Option VConstant} {Us : List Name} :
    ∀ {e : Expr} {Γ : List VExpr} {p : VExpr × VExpr},
      ctorTr? Γc Us e Γ = some p → ctorTrW? Γc Us e Γ = some p := by
  intro e
  induction e with
  | sort u =>
    intro Γ p h
    rw [show ctorTrW? Γc Us (.sort u) Γ = ctorTr? Γc Us (.sort u) Γ from rfl]; exact h
  | bvar i =>
    intro Γ p h
    rw [show ctorTrW? Γc Us (.bvar i) Γ = ctorTr? Γc Us (.bvar i) Γ from rfl]; exact h
  | const c us =>
    intro Γ p h
    rw [show ctorTrW? Γc Us (.const c us) Γ = ctorTr? Γc Us (.const c us) Γ from rfl]; exact h
  | app f a ihf iha =>
    intro Γ p h
    simp only [ctorTr?, Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, r, hr, AB, hAB, h⟩ := h
    simp only [ctorTrW?, Option.bind_eq_some_iff]
    exact ⟨q, ihf hq, r, iha hr, AB, hAB, h⟩
  | forallE nm d b bi ihd ihb =>
    intro Γ p h
    simp only [ctorTr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, u, hu, r, hr, v, hv, h⟩ := h
    simp only [ctorTrW?, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    exact ⟨q, ihd hq, u, hu, r, ihb hr, v, hv, h⟩
  | mdata dt e ih =>
    intro Γ p h
    rw [show ctorTr? Γc Us (.mdata dt e) Γ = ctorTr? Γc Us e Γ from rfl] at h
    rw [show ctorTrW? Γc Us (.mdata dt e) Γ = ctorTrW? Γc Us e Γ from rfl]
    exact ih h
  | fvar | mvar | lam | letE | lit | proj => intro Γ p h; simp [ctorTr?] at h

/-! ## §4 The field, over the widened fragment

`TrExprSGeneral.lean` §3/§4 verbatim, with `ctorTrW?` in place of `ctorTr?`.  The `↔` survives
because §3b's `isUnique_of_ctorTrW` survives. -/

/-- `TrIndCtorR`, discharged for one constructor, over the widened fragment. -/
theorem trIndCtorR_of_ctorTrW {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    {D : VInductDecl'} {R : VIndRestore} {j : Nat} {c : Constructor} {C : VIndCtor}
    (hΓc : ConstLookup Γc env) (hname : c.name = R.ctorName C.name)
    {t' : VExpr} (h : ctorTrW? Γc Us c.type [] = some (C.typeR D R j, t')) :
    TrIndCtorR env Us D R j c C :=
  ⟨hname, trExprS_of_ctorTrW hΓc h⟩

/-- …and the converse on the widened fragment. -/
theorem trIndCtorR_iff_of_ctorTrW {env : VEnv} {Γc : Name → Option VConstant} {Us : List Name}
    {D : VInductDecl'} {R : VIndRestore} {j : Nat} {c : Constructor} {C : VIndCtor}
    (hΓc : ConstLookup Γc env) {ct t' : VExpr}
    (h : ctorTrW? Γc Us c.type [] = some (ct, t')) :
    TrIndCtorR env Us D R j c C ↔ (c.name = R.ctorName C.name ∧ C.typeR D R j = ct) := by
  refine ⟨fun ⟨hn, htr⟩ => ⟨hn, TrExprS.unique (isUnique_of_ctorTrW h) htr
    (trExprS_of_ctorTrW hΓc h)⟩, fun ⟨hn, he⟩ => ⟨hn, ?_⟩⟩
  exact he ▸ trExprS_of_ctorTrW hΓc h

/-- **`TrIndDeclN.trCtors`, discharged over the widened fragment.** -/
theorem trCtorsW_of_ctorTrW {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {Γc : Name → Option VConstant}
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁)
    (h : ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTrW? Γc Us c.type [] = some (C.typeR D R j, t')) :
    ∀ env₁, env.addIndTypesC D K = some env₁ →
    ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      TrIndCtorR env₁ Us D R j c C := by
  intro env₁ hst j t T ht hT q c C hc hC
  obtain ⟨hn, t', htr⟩ := h j t T ht hT q c C hc hC
  exact trIndCtorR_of_ctorTrW (hΓc env₁ hst) hn htr

/-- The widened membership predicate. -/
def CtorsInFragmentW (Γc : Name → Option VConstant) (Us : List Name)
    (types : List InductiveType) : Prop :=
  ∀ (j : Nat) t, types[j]? = some t → ∀ (q : Nat) c, t.ctors[q]? = some c →
    ∃ p, ctorTrW? Γc Us c.type [] = some p

/-- …and the `↔` over it. -/
theorem trCtorsW_iff_of_fragmentW {env : VEnv} {Us : List Name} {types : List InductiveType}
    {D : VInductDecl'} {K : List Name} {R : VIndRestore} {Γc : Name → Option VConstant}
    (hΓc : ∀ env₁, env.addIndTypesC D K = some env₁ → ConstLookup Γc env₁)
    (hfrag : CtorsInFragmentW Γc Us types)
    (hne : ∃ env₁, env.addIndTypesC D K = some env₁) :
    (∀ env₁, env.addIndTypesC D K = some env₁ →
      ∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        TrIndCtorR env₁ Us D R j c C) ↔
    (∀ (j : Nat) t T, types[j]? = some t → D.types[j]? = some T →
      ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
        c.name = R.ctorName C.name ∧
        ∃ t', ctorTrW? Γc Us c.type [] = some (C.typeR D R j, t')) := by
  refine ⟨fun H j t T ht hT q c C hc hC => ?_, trCtorsW_of_ctorTrW hΓc⟩
  obtain ⟨env₁, hst⟩ := hne
  obtain ⟨⟨ct, t'⟩, hp⟩ := hfrag j t ht q c hc
  obtain ⟨hn, he⟩ :=
    (trIndCtorR_iff_of_ctorTrW (hΓc env₁ hst) hp).1 (H env₁ hst j t T ht hT q c C hc hC)
  exact ⟨hn, t', he ▸ hp⟩

/-- The widening is a widening at block level too: nothing that was covered is lost. -/
theorem ctorsInFragmentW_of_ctorsInFragment {Γc : Name → Option VConstant} {Us : List Name}
    {types : List InductiveType} (h : CtorsInFragment Γc Us types) :
    CtorsInFragmentW Γc Us types := by
  intro j t ht q c hc
  obtain ⟨p, hp⟩ := h j t ht q c hc
  exact ⟨p, ctorTrW?_of_ctorTr? hp⟩

/-- §1's block-level escape lemma, for the widened predicate. -/
theorem not_ctorsInFragmentW_of_ctor {Γc : Name → Option VConstant} {Us : List Name}
    {types : List InductiveType} {j q : Nat} {t : InductiveType} {c : Constructor}
    (ht : types[j]? = some t) (hc : t.ctors[q]? = some c)
    (h : ctorTrW? Γc Us c.type [] = none) : ¬ CtorsInFragmentW Γc Us types := by
  intro H
  obtain ⟨p, hp⟩ := H j t ht q c hc
  rw [h] at hp
  exact absurd hp nofun

/-! ## §5 The widening, demonstrated; and the boundary, exhibited at a real declaration

§5a shows the two new cases actually fire — a widening nobody can instantiate is not a widening.
§5b is the finding that matters for (b): **the boundary is not the head enumeration at all.** -/

namespace FragEx

/-- The three-lookup environment for nat literals. -/
def natGc : Name → Option VConstant := fun n =>
  if n = ``Nat then some ⟨0, .sort (.succ .zero)⟩
  else if n = ``Nat.zero then some ⟨0, .nat⟩
  else if n = ``Nat.succ then some ⟨0, .forallE .nat .nat⟩
  else none

/-! ### §5a Both new cases fire, as `rfl` before/after pairs -/

/-- `.lam`: exactly `TrExprSGeneral.lean` §6's `trExprS_lam_outside_fragment` term, now inferred.
The `none` half is the same computation that file records; the `some` half is new. -/
theorem lam_before_after :
    ctorTr? (fun _ => none) [] (.lam `x (.sort (.succ .zero)) (.bvar 0) .default) [] = none ∧
    ctorTrW? (fun _ => none) [] (.lam `x (.sort (.succ .zero)) (.bvar 0) .default) []
      = some (.lam (.sort (.succ .zero)) (.bvar 0),
        .forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := ⟨rfl, rfl⟩

/-- …and the inferred pair really is a `TrExprS` plus its type, at **every** environment (the
`.lam` case consumed no lookups). -/
theorem lam_trExprS {env : VEnv} :
    TrExprS env [] [] (.lam `x (.sort (.succ .zero)) (.bvar 0) .default)
      (.lam (.sort (.succ .zero)) (.bvar 0)) ∧
    env.HasType 0 [] (.lam (.sort (.succ .zero)) (.bvar 0))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  ctorTrW?_sound (Γc := fun _ => none) nofun lam_before_after.2

/-- `.lit`: a nat literal, before and after. -/
theorem lit_before_after :
    ctorTr? natGc [] (.lit (.natVal 3)) [] = none ∧
    ctorTrW? natGc [] (.lit (.natVal 3)) [] = some (.natLit 3, .nat) := ⟨rfl, rfl⟩

/-- …with its `TrExprS` and typing, from the three lookups and nothing else — no `VEnv.Ordered`,
no `VEnv.HasPrimitives`. -/
theorem lit_trExprS {env : VEnv} (hΓc : ConstLookup natGc env) :
    TrExprS env [] [] (.lit (.natVal 3)) (.natLit 3) ∧ env.HasType 0 [] (.natLit 3) .nat :=
  ctorTrW?_sound hΓc lit_before_after.2

/-- **Two of §2's three escapes are closed by the widening**, at the real stored types. -/
theorem withLit_inFragmentW : inFragmentW (exprOf% WithLit.mk) = true := rfl
theorem withLam_inFragmentW : inFragmentW (exprOf% WithLam.mk) = true := rfl

/-- …and the third is not: `.letE` remains outside, so `CtorsInFragmentW` still fails there at
every environment.  §6 says what closing it would cost. -/
theorem withLet_not_inFragmentW : inFragmentW (exprOf% WithLet.mk) = false := rfl

/-! ### §5b The real boundary: a declaration *inside* the fragment that still fails

`Arr` is a `def` whose value is a `∀`; `idf : Arr`, so `idf`'s **stored** type is `.const Arr []`,
which is a `∀` only after delta.  `idf Nat` is a perfectly good field type — Lean's elaborator
whnf's `Arr` to check it, and Lean's kernel accepts the block — but the stored constructor type
records the un-unfolded constant, so `piOf?` fails on it.

Note what this means: the constructor type below uses **only `.app`, `.forallE` and `.const`**, so
it is in the *original* fragment's head set, and `inFragment` says `true`.  The head enumeration of
`TrExprSGeneral.lean` §6 was therefore never a characterisation of the fragment — necessary, not
sufficient — and `ctorTr?_none_of_nonSyntacticPi`'s hand-built `F`/`G` pair is realised by an
ordinary declaration. -/

/-- `Arr : Type 1 := Type → Type` — a constant that unfolds to a `∀`. -/
def Arr : Type 1 := Type → Type
/-- …and an inhabitant of it, whose stored type is the bare constant `Arr`. -/
def idf : Arr := fun α => α

/-- The block.  `Lean` accepts it; its presence here is the certificate. -/
inductive WithConv : Type where
  | mk : idf Nat → WithConv

example : WithConv := .mk Nat.zero

/-- The **faithful** environment: each constant's stored type, transcribed.  `idf`'s is the bare
`.const Arr []`, exactly as `Lean` stores it (checked by `repr` before this was written). -/
def convGc : Name → Option VConstant := fun n =>
  if n = ``Arr then some ⟨0, .sort (.succ (.succ .zero))⟩
  else if n = ``idf then some ⟨0, .const ``Arr []⟩
  else if n = ``Nat then some ⟨0, .sort (.succ .zero)⟩
  else if n = ``WithConv then some ⟨0, .sort (.succ .zero)⟩
  else none

/-- Inside the syntactic fragment — both the old one and the widened one. -/
theorem withConv_inFragment : inFragment (exprOf% WithConv.mk) = true := rfl
theorem withConv_inFragmentW : inFragmentW (exprOf% WithConv.mk) = true := rfl

/-- **…and yet both inferencers return `none`, at the faithful environment.**  So (b)'s boundary
is here and not in the head list. -/
theorem withConv_ctorTr?_none : ctorTr? convGc [] (exprOf% WithConv.mk) [] = none := rfl
theorem withConv_ctorTrW?_none : ctorTrW? convGc [] (exprOf% WithConv.mk) [] = none := rfl

def withConvIndType : InductiveType :=
  { name := ``WithConv, type := exprOf% WithConv,
    ctors := [{ name := ``WithConv.mk, type := exprOf% WithConv.mk }] }

/-- The block-level statement, at the faithful environment. -/
theorem withConv_not_ctorsInFragmentW : ¬ CtorsInFragmentW convGc [] [withConvIndType] :=
  not_ctorsInFragmentW_of_ctor (j := 0) (q := 0) rfl rfl withConv_ctorTrW?_none

end FragEx

/-- **The boundary, as a general theorem.**  The `.app` case fails exactly when the function's
inferred type is not *syntactically* a `∀`; nothing about the argument, the environment or the
context can rescue it.  Repairing this needs `HasType f' (.const c us) → HasType f' (.forallE A B)`,
i.e. `VEnv.IsDefEq.defeq` at a delta step — a conversion check, by definition.  That is why the
widening stops here and not one case later. -/
theorem ctorTrW?_app_eq_none_of_not_piOf {Γc : Name → Option VConstant} {Us : List Name}
    {f a : Expr} {Γ : List VExpr} {p : VExpr × VExpr}
    (hf : ctorTrW? Γc Us f Γ = some p) (hpi : piOf? p.2 = none) :
    ctorTrW? Γc Us (.app f a) Γ = none := by
  simp only [ctorTrW?, hf, Option.bind_some]
  cases h : ctorTrW? Γc Us a Γ with
  | none => rfl
  | some q => simp [hpi]

/-- The same for the original inferencer, so the claim is about the design and not about §3's
particular widening. -/
theorem ctorTr?_app_eq_none_of_not_piOf {Γc : Name → Option VConstant} {Us : List Name}
    {f a : Expr} {Γ : List VExpr} {p : VExpr × VExpr}
    (hf : ctorTr? Γc Us f Γ = some p) (hpi : piOf? p.2 = none) :
    ctorTr? Γc Us (.app f a) Γ = none := by
  simp only [ctorTr?, hf, Option.bind_some]
  cases h : ctorTr? Γc Us a Γ with
  | none => rfl
  | some q => simp [hpi]

/-! ## §6 Where the boundary is, and why — one entry per remaining exclusion

`TrExprSGeneral.lean` §6 costs the six omitted `Expr` constructors in prose.  This section replaces
each entry with a machine-checked statement, and re-classifies them: the exclusions are **not** all
of a kind, and only one of them is the conversion boundary.

| omitted | status after this round | why |
| --- | --- | --- |
| `.lam` | **admitted** (§3) | `VEnv.HasType.lam`; no new hypothesis |
| `.lit (.natVal _)` | **admitted** (§3a) | `ContainsLits` is one `Γc` lookup; typing by induction on `n` |
| `.lit (.strVal _)` | bookkeeping, unpaid | same idea, five constants instead of two |
| `.fvar`, `.mvar` | **vacuous, proved** (§6a) | ruled out by the guard loop's own `FVarsIn` invariant |
| `.letE` | real, not conversion (§6b) | needs `Γ` to be a `VLCtx` with `.vlet` entries |
| `.proj` | real, and *structurally* blocked (§6c) | `TrExprS.IsUnique (.proj ..) = False` kills §4's `↔` |
| non-syntactic `∀` | **the conversion boundary** (§5b) | needs `VEnv.IsDefEq`; poisons the cone |
-/

/-! ### §6a `.fvar` and `.mvar` are vacuous exclusions, proved

`Verify/Inductive/RunIdentity.lean`'s `BlockNoFVar` is the invariant
`Environment.addInductive`'s guard loop *does* supply: `FVarsIn (fun _ => False) c.type` for every
constructor of every member.  That single predicate rules out both heads at once (`FVarsIn` is
`fvars fv` at `.fvar` and `False` at `.mvar`).  So admitting them would widen the fragment on **no
constructor type the checker is ever asked to accept**, which is what "vacuous" has to mean if it
is to be a claim rather than a hope. -/

/-- The widened fragment plus the two heads a stored constructor type cannot contain. -/
def inFragmentFM : Expr → Bool
  | .sort _ => true
  | .bvar _ => true
  | .fvar _ => true
  | .mvar _ => true
  | .const _ _ => true
  | .app f a => inFragmentFM f && inFragmentFM a
  | .forallE _ d b _ => inFragmentFM d && inFragmentFM b
  | .lam _ d b _ => inFragmentFM d && inFragmentFM b
  | .lit (.natVal _) => true
  | .mdata _ e => inFragmentFM e
  | _ => false

/-- **The `.fvar`/`.mvar` exclusion is vacuous.**  On any `FVarsIn (fun _ => False)` expression the
two fragments coincide, so the round's widening loses nothing by stopping short of them. -/
theorem inFragmentFM_eq_inFragmentW :
    ∀ {e : Expr}, FVarsIn (fun _ => False) e → inFragmentFM e = inFragmentW e
  | .sort _, _ | .bvar _, _ | .const .., _ => rfl
  | .lit (.natVal _), _ | .lit (.strVal _), _ => rfl
  | .fvar _, h => absurd h id
  | .mvar _, h => absurd h id
  | .app f a, h => by
    simp [inFragmentFM, inFragmentW, inFragmentFM_eq_inFragmentW h.1,
      inFragmentFM_eq_inFragmentW h.2]
  | .forallE _ d b _, h => by
    simp [inFragmentFM, inFragmentW, inFragmentFM_eq_inFragmentW h.1,
      inFragmentFM_eq_inFragmentW h.2]
  | .lam _ d b _, h => by
    simp [inFragmentFM, inFragmentW, inFragmentFM_eq_inFragmentW h.1,
      inFragmentFM_eq_inFragmentW h.2]
  | .letE .., _ => rfl
  | .proj .., _ => rfl
  | .mdata _ e, h => inFragmentFM_eq_inFragmentW (e := e) h

/-! ### §6b `.letE` is real, and it is not a conversion problem

`TrExprS.letE` concludes `TrExprS Δ (.letE ..) body'` from
`TrExprS ((none, .vlet ty' val') :: Δ) body body'`.  The inferencer's context is `Γ : List VExpr`,
read through `bvarCtx`, whose whole virtue (`ExprConstructionScope.lean` §1) is that its `find?` is
free of `VLCtx.WF` and `VEnv.Ordered`.  A `.vlet` entry is not a `bvarCtx` entry, so admitting
`.letE` means replacing `Γ` by a `VLCtx` and re-proving that lemma — a generalisation of a file this
round does not own, and **no conversion check anywhere**.  Machine-checked residual: -/

theorem letE_still_out {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr}
    {n : Name} {t v b : Expr} {nd : Bool} : ctorTrW? Γc Us (.letE n t v b nd) Γ = none := rfl

/-! ### §6c `.proj` is not merely expensive — it breaks §4's `↔`

`TrExprS.IsUnique` is `False` at `.proj`, and `trIndCtorR_iff_of_ctorTrW`'s forward direction is
`TrExprS.unique` applied to `isUnique_of_ctorTrW`.  So a `.proj`-admitting inferencer cannot have
`isUnique_of_ctorTrW`, and the `↔` — the statement that the stored type is *forced* to be what the
inferencer computes — degenerates to the one-directional producer.  That is a structural reason to
stop, independent of `TrProj`'s cost and independent of the contamination in
`TrProj.weak'_inv`. -/

theorem not_isUnique_proj {s : Name} {i : Nat} {e : Expr} : ¬ TrExprS.IsUnique (.proj s i e) := id

theorem proj_still_out {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr}
    {s : Name} {i : Nat} {e : Expr} : ctorTrW? Γc Us (.proj s i e) Γ = none := rfl

theorem strVal_still_out {Γc : Name → Option VConstant} {Us : List Name} {Γ : List VExpr}
    {s : String} : ctorTrW? Γc Us (.lit (.strVal s)) Γ = none := rfl

/-! ## §7 The arity-0 witness, at the parameterised nested block

`InductiveDeclExamples.ntreeAux` — `NTree α` with a `List (NTree α)` field, `uvars = 1`,
`params = [Type u]`.  Reached through §4's general producer and nothing else.

**Structural exclusions.**  This file's only `import` is
`Lean4Lean.Verify.Inductive.TrExprSGeneral`.  Neither `Lean4Lean.Verify.Inductive.FlipConstruct`
(hence not `tr_ntreeNodeType`) nor `Lean4Lean.Verify.Inductive.TrTypeProducer` is in the import
closure at all, so no proof below can be routed through either — the exclusion is a property of
the module graph, not a promise about proof style.  No `trS_tac`, no `type_tac`. -/

namespace InductiveDeclExamples

/-- The widened inferencer computes the same restored constructor type as `ctorTr?` does — by
`rfl`, and *a fortiori* from `ctorTrW?_of_ctorTr?`.  So the widening did not perturb the case the
nested flip actually needs. -/
theorem ntreeNode_ctorTrW :
    ctorTrW? ntreeGc [`u] (exprOf% NTree.node) []
      = some (ntreeNode.typeR ntreeAux ntreeRestore 0,
        .sort (.imax (.succ (.succ (.param 0)))
          (.imax (.succ (.param 0))
            (.imax (.succ (.param 0)) (.succ (.param 0)))))) := rfl

/-- …and the block is in the widened fragment, through the general widening lemma rather than by
recomputation. -/
theorem ntree_ctorsInFragmentW : CtorsInFragmentW ntreeGc [`u] [ntreeIndType] :=
  ctorsInFragmentW_of_ctorsInFragment ntree_ctorsInFragment

/-- **`TrIndDeclN.trCtors`'s text, discharged at `ntreeAux` over the widened fragment**, through
§4's general producer. -/
theorem ntreeAux_trCtorsW {env₁ : VEnv} (h : VEnv.empty.addInduct' listDecl = some env₁) :
    ∀ F₁, env₁.addIndTypesC ntreeAux ntreeK = some F₁ →
    ∀ (j : Nat) t T, ([ntreeIndType] : List Lean.InductiveType)[j]? = some t →
      ntreeAux.types[j]? = some T →
    ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
      TrIndCtorR F₁ [`u] ntreeAux ntreeRestore j c C := by
  refine trCtorsW_of_ctorTrW (fun _ hF₁ => ntree_constLookup h hF₁) ?_
  rintro (_ | j) t T ht hT
  · cases ht
    rw [show ntreeAux.types[0]? = some
      { name := ``NTree, type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0))),
        indices := [], ctors := [ntreeNode] } from rfl] at hT
    cases hT
    rintro (_ | q) c C hc hC
    · cases hc; cases hC
      exact ⟨rfl, _, ntreeNode_ctorTrW⟩
    · simp [ntreeIndType] at hc
  · simp at ht

/-- **THE WITNESS — arity 0.**  Everything this round established, instantiated at the
parameterised nested block and existentially closed over the declaration history:

* the widened field text, in `TrIndDeclN`'s own staging (`trCtorsW_of_ctorTrW`, §4);
* widened-fragment membership, obtained from the old membership by the general widening lemma;
* non-degeneracy: this is not `nfnAux` (`uvars = 1`, a parameter, two members, two fields);
* anti-vacuity: the one member/constructor pair the clause bites at, named;
* **and the two facts that make the widening a widening rather than a rename** — a `.lam` and a
  nat literal on which the old inferencer returns `none` and the new one succeeds. -/
theorem ntreeAux_trCtorsW_witness :
    ∃ env₁ F₁ : VEnv, VEnv.empty.addInduct' listDecl = some env₁ ∧
      env₁.addIndTypesC ntreeAux ntreeK = some F₁ ∧
      -- non-degeneracy: this is not `nfnAux`
      ntreeAux.uvars = 1 ∧ ntreeAux.params = [.sort (.succ (.param 0))] ∧
      ntreeAux.types.length = 2 ∧ ntreeNode.fields.length = 2 ∧
      -- the block is in the widened fragment
      CtorsInFragmentW ntreeGc [`u] [ntreeIndType] ∧
      -- the field, in `TrIndDeclN`'s own staging, over the widened fragment
      (∀ F, env₁.addIndTypesC ntreeAux ntreeK = some F →
        ∀ (j : Nat) t T, ([ntreeIndType] : List Lean.InductiveType)[j]? = some t →
          ntreeAux.types[j]? = some T →
        ∀ (q : Nat) c C, t.ctors[q]? = some c → T.ctors[q]? = some C →
          TrIndCtorR F [`u] ntreeAux ntreeRestore j c C) ∧
      -- anti-vacuity: member 0, constructor 0 is a matching pair, and the clause is about it
      (∃ t c C, ([ntreeIndType] : List Lean.InductiveType)[0]? = some t ∧
        t.ctors[0]? = some c ∧ c.name = ``NTree.node ∧
        (ntreeAux.types[0]?.map (·.ctors)) = some [C] ∧ C = ntreeNode ∧
        TrIndCtorR F₁ [`u] ntreeAux ntreeRestore 0 c C) ∧
      -- the widening is strict: two terms the old inferencer rejects and the new one accepts
      (ctorTr? (fun _ => none) [] (.lam `x (.sort (.succ .zero)) (.bvar 0) .default) [] = none ∧
        ctorTrW? (fun _ => none) [] (.lam `x (.sort (.succ .zero)) (.bvar 0) .default) []
          = some (.lam (.sort (.succ .zero)) (.bvar 0),
            .forallE (.sort (.succ .zero)) (.sort (.succ .zero)))) ∧
      (ctorTr? FragEx.natGc [] (.lit (.natVal 3)) [] = none ∧
        ctorTrW? FragEx.natGc [] (.lit (.natVal 3)) [] = some (.natLit 3, .nat)) := by
  obtain ⟨env₁, -, -, F₁, -, h, -, -, hF₁, -⟩ := ntree_stage₂_exists
  exact ⟨env₁, F₁, h, hF₁, rfl, rfl, rfl, rfl, ntree_ctorsInFragmentW, ntreeAux_trCtorsW h,
    ⟨_, _, ntreeNode, rfl, rfl, rfl, rfl, rfl,
      ntreeAux_trCtorsW h F₁ hF₁ 0 _ _ rfl rfl 0 _ _ rfl rfl⟩,
    FragEx.lam_before_after, FragEx.lit_before_after⟩

end InductiveDeclExamples

/-! ## §8 What the translation side needs after this round

Two claims, kept apart, because conflating them is the error this area invites.

**Claim A — "all fields general".**  `TrIndDeclN.trCtors` now has a general producer over a
*widened* class: `trCtorsW_of_ctorTrW` (§4), with an `↔` (`trCtorsW_iff_of_fragmentW`) wherever
`CtorsInFragmentW` holds, from `ConstLookup` alone.  This is still **not** every block: §5b exhibits
a real declaration in the syntactic fragment that no environment can push through, and §6b/§6c leave
`.letE` and `.proj` out.  So Claim A is *general in `env`, `Us`, `types`, `D`, `K`, `R`, `Γc`* —
every field of the relation is a variable — but *conditional on a side condition about the block*.

**Claim B — "the constructor is constructible".**  At `ntreeAux` the side condition is discharged by
computation (§7), so there the field is unconditional.  That is a statement about **one block**, and
it does not upgrade Claim A.

What remains for the translation side, precisely:

1. `CtorsInFragmentW` (or its successor) must be discharged for the block `addDecl` is actually
   handed, not for a fixed example.  §5b is the obstruction: the general discharge cannot be
   syntactic, because the failing declarations are syntactically fine.
2. Therefore the next step on this path is **not** more head cases.  It is a `piOf?` that whnf's,
   which needs `HasType.defeq` at a delta step.  That is the conversion check the whole design
   avoids, and per the brief it touches the contaminated `IsDefEq.uniq` / `uniqU` /
   `checkType.WF` / `TrExprS.weakFV_inv` neighbourhood.  Nothing in this file does.
3. The honest alternative, and the one this round recommends: keep `ctorTrW?` for the class it
   settles (which now includes `.lam` and numerals, and provably includes both nested blocks), and
   obtain the general `trCtors` from the checker's *own* inference run rather than from a second
   inferencer — accepting that this route pays the conversion price once, in a place already paid
   for, instead of paying it again here.
-/

end Lean4Lean
