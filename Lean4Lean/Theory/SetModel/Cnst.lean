import Lean4Lean.Theory.SetModel.SoundInduction
import Lean4Lean.Theory.Typing.Env

/-!
# Building the constant assignment

`ModelData.cnst` is supplied rather than computed, which is what made the term
recursion in `SetModel/Interp.lean` structural.  This file discharges that
trade: `cnstOf` builds the assignment by recursion on the declaration list, and
the coherence obligations are met one declaration at a time.

## Shape

Every declaration form extends the environment in exactly two ways — a fold of
`addConst` and a fold of `addDefEq` — so the whole construction goes through two
step lemmas, `coherentOn_addConst` and `coherentOn_addDefEq`
(`SetModel/InterpSound.lean`), lifted here to lists.  Nothing is special-cased
per constructor beyond *where each value comes from*:

| Declaration | Value of `cnst` |
|---|---|
| `.def`, `.opaque` | `⟦value⟧` at the earlier stage — `defExtend` |
| `.example` | nothing; the environment is unchanged |
| `.axiom`, `.quot`, `.induct` | the oracle — `oracleExtend` |

The oracle is a parameter with an obligation (`OracleOK`), so the three forms
whose values the model must *supply* rather than *compute* are handled
uniformly. `.axiom`'s obligation is discharged by the axiom-freedom hypothesis
of the main theorem together with the three standard axioms' model-side
validations; `.quot`'s and `.induct`'s by `SetModel/Universe.lean` and
`SetModel/IndStage.lean`/`IndCard.lean` respectively.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {L : LevelAssign envF nv} {κ : ℕ → V} {ls : List ℕ}

/-- Extend an assignment along a list of names, each value taken from the
oracle.  Every declaration form that adds a *block* of constants — `quot`,
`induct` — goes through this, so the constructor list is not hardcoded anywhere
but in `cnstOf` itself. -/
noncomputable def oracleExtend (o : Name → List VLevel → V) :
    List Name → (Name → List VLevel → V) → (Name → List VLevel → V)
  | [], c => c
  | n :: ns, c => oracleExtend o ns (cnstUpdate c n (o n))

/-! ## Definitions: the value is the body's denotation -/

/-- `cnst` for a definition: the denotation of its body, at the assignment the
earlier declarations produced. -/
noncomputable def defExtend (L : LevelAssign envF nv) (κ : ℕ → V) (ls : List ℕ)
    (c : Name → List VLevel → V) (ci : VDefVal) : Name → List VLevel → V :=
  cnstUpdate c ci.name fun us ↦ (interp ⟨κ, ls, c⟩ L [] (ci.value.instL us)).toFun ∅

section Step

variable {env env' : VEnv} {c : Name → List VLevel → V} {R : List VExpr → List VExpr → Prop}
variable (hle : env ≤ envF) (henv : env.Ordered) (hS : L.Stable)
  (hC : CoherentOn ⟨κ, ls, c⟩ L env) (hR : CtxInvariant L R)
  (hRd : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
    env.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))

include hle henv hS hC hR hRd in
/-- **The constant a definition or an opaque declaration adds.**

Both obligations come straight from soundness at the *earlier* environment:
`const_congr` from `IsDefEq.instL_r` (instantiating at pointwise-equivalent
level lists gives definitionally equal terms), `const_type` from `IsDefEq.instL`
together with `VDefVal.WF`. -/
theorem coherentOn_defConst {ci : VDefVal} (hci : ci.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') :
    CoherentOn ⟨κ, ls, defExtend L κ ls c ci⟩ L env' := by
  have hocc := VEnv.IsDefEq.constsIn henv.constsIn hci trivial
  refine coherentOn_addConst L henv.constsClosed hadd hC (fun {us us'} hw hw' hdd ↦ ?_)
    (fun {us} hw hlen ↦ ?_)
  · exact Above.imp (sound_nil hle henv hS hC hR hRd
      (VEnv.IsDefEq.instL_r (Γ := []) henv trivial hw hw' hdd hci)) fun h ↦ h.1
  · have key : interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] (ci.type.instL us)
        = interp ⟨κ, ls, c⟩ L [] (ci.type.instL us) :=
      interp_cnst_congr L _ [] <| ConstsAgree.of_constsIn <|
        (VExpr.ConstsIn.instL.2 hocc.2.2).mono fun m hm _ ↦ by
          have hne : m ≠ ci.name := fun h ↦ by
            obtain ⟨_, hmm⟩ := hm
            rw [h, (VEnv.addConst_spec hadd).1] at hmm; exact absurd hmm nofun
          simp only [defExtend, cnstUpdate, if_neg hne]
    show Above _ (_ ∈ (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] _).toFun ∅)
    rw [key]
    exact Above.imp (sound_nil hle henv hS hC hR hRd (hci.instL hw)) fun h ↦ h.2

include hle henv hS hC hR hRd in
/-- **The defining equation a definition adds.**  `VDefVal.toDefEq` equates
`.const c (params)` with the body; at a level instantiation of the right length
`VLevel.inst_map_id` turns the parameter list into the instantiation itself, so
the left-hand side is exactly the value `defExtend` assigned. -/
theorem coherentOn_defEq {ci : VDefVal} (hci : ci.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') :
    CoherentOn ⟨κ, ls, defExtend L κ ls c ci⟩ L (env'.addDefEq ci.toDefEq) := by
  have hocc := VEnv.IsDefEq.constsIn henv.constsIn hci trivial
  have hstep := coherentOn_defConst hle henv hS hC hR hRd hci hadd
  have hfresh : ∀ {m : Name}, env.contains m → m ≠ ci.name := fun {m} hm h ↦ by
    obtain ⟨_, hmm⟩ := hm
    rw [h, (VEnv.addConst_spec hadd).1] at hmm; exact absurd hmm nofun
  have key : ∀ {e : VExpr}, e.ConstsIn env.contains →
      interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] e = interp ⟨κ, ls, c⟩ L [] e := fun he ↦
    interp_cnst_congr L _ [] <| ConstsAgree.of_constsIn <| he.mono fun m hm _ ↦ by
      simp only [defExtend, cnstUpdate, if_neg (hfresh hm)]
  -- the left-hand side's denotation *is* the assigned value
  have hlhs : ∀ {us : List VLevel}, us.length = ci.uvars →
      (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] (ci.toDefEq.lhs.instL us)).toFun ∅
        = (interp ⟨κ, ls, c⟩ L [] (ci.value.instL us)).toFun ∅ := by
    intro us hlen
    show (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L []
      (.const ci.name ((VLevel.params ci.uvars).map (VLevel.inst us)))).toFun ∅ = _
    rw [VLevel.inst_map_id hlen, interp_const]
    show defExtend L κ ls c ci ci.name us = _
    unfold defExtend cnstUpdate
    rw [if_pos rfl]
  refine coherentOn_addDefEq hstep (fun {us} hw hlen ↦ ?_) (fun {us} hw hlen ↦ ?_)
  · refine Above.pure ?_
    show _ = (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] (ci.value.instL us)).toFun ∅
    rw [hlhs hlen, key (VExpr.ConstsIn.instL.2 hocc.1)]
  · show Above _ (_ ∈ (interp ⟨κ, ls, defExtend L κ ls c ci⟩ L [] (ci.type.instL us)).toFun ∅)
    rw [hlhs hlen, key (VExpr.ConstsIn.instL.2 hocc.2.2)]
    exact Above.imp (sound_nil hle henv hS hC hR hRd (hci.instL hw)) fun h ↦ h.2

end Step

/-! ## The two step lemmas, in list form

`addConstList` and the `addDefEq` fold are the only two ways any declaration
form extends the environment, so lifting the single-step lemmas to lists covers
every form at once — including `addInduct'`, which is three `addConstList` folds
and one `addDefEq` fold. -/

section Lists

variable {c : Name → List VLevel → V} {o : Name → List VLevel → V}

/-- One step of `addConstList`, as an iff. -/
theorem addConstList_cons {q : Name × VConstant} {cs : List (Name × VConstant)}
    {env env' : VEnv} : env.addConstList (q :: cs) = some env' ↔
      ∃ env₁, env.addConst q.1 q.2 = some env₁ ∧ env₁.addConstList cs = some env' := by
  rw [VEnv.addConstList, List.foldlM_cons]
  cases env.addConst q.1 q.2 <;> simp [VEnv.addConstList]

/-- The names a block declares are fresh for the environment it is added to.
`addConstList` fails on a name already taken, so success gives this for free —
and for *every* name of the block, not just the first, because each later name
is fresh for a larger environment. -/
theorem addConstList_fresh :
    ∀ (cs : List (Name × VConstant)) {env env' : VEnv}, env.addConstList cs = some env' →
      ∀ p ∈ cs, ¬ env.contains p.1
  | [], _, _, _, _, h => absurd h List.not_mem_nil
  | q :: cs, env, env', hadd, p, hp => by
    obtain ⟨env₁, hq, hrest⟩ := addConstList_cons.1 hadd
    have hle : env ≤ env₁ := VEnv.addConst_le hq
    rcases List.mem_cons.1 hp with rfl | hp
    · exact fun ⟨_, hc⟩ ↦ by rw [(VEnv.addConst_spec hq).1] at hc; exact absurd hc nofun
    · exact fun hcon ↦ addConstList_fresh cs hrest p hp (hcon.imp fun _ ↦ hle.constants)

/-- Extending along a block of *fresh* names leaves untouched the denotation of
anything that mentions only old constants. -/
theorem interp_oracleExtend_eq (L : LevelAssign envF nv) (κ : ℕ → V) (ls : List ℕ)
    {P : Name → Prop} :
    ∀ (ns : List Name) (c : Name → List VLevel → V), (∀ n ∈ ns, ¬ P n) →
      ∀ {e : VExpr}, e.ConstsIn P →
        interp ⟨κ, ls, oracleExtend o ns c⟩ L [] e = interp ⟨κ, ls, c⟩ L [] e
  | [], _, _, _, _ => rfl
  | n :: ns, c, hfr, e, he => by
    rw [show oracleExtend o (n :: ns) c = oracleExtend o ns (cnstUpdate c n (o n)) from rfl,
      interp_oracleExtend_eq L κ ls ns _ (fun m hm ↦ hfr m (.tail _ hm)) he]
    exact interp_cnst_congr L _ [] <| ConstsAgree.of_constsIn <| he.mono fun m hm _ ↦ by
      simp only [cnstUpdate, if_neg (fun h : m = n ↦ hfr n (.head _) (h ▸ hm))]

/-- What the oracle owes for one constant, stated at the assignment the whole
block produces. -/
structure OracleOK (L : LevelAssign envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o c : Name → List VLevel → V) (n : Name) (ci : VConstant) : Prop where
  congr : ∀ {us us' : List VLevel}, (∀ l ∈ us, l.WF nv) → (∀ l ∈ us', l.WF nv) →
    List.Forall₂ (· ≈ ·) us us' → Above (V := V) ⟨κ, ls, c⟩ (o n us = o n us')
  type : ∀ {us : List VLevel}, (∀ l ∈ us, l.WF nv) → us.length = ci.uvars →
    Above (V := V) ⟨κ, ls, c⟩ (o n us ∈ (interp ⟨κ, ls, c⟩ L [] (ci.type.instL us)).toFun ∅)

/-- **The step lemma for a block of constants.** -/
theorem coherentOn_addConstList (L : LevelAssign envF nv) (o : Name → List VLevel → V) :
    ∀ (cs : List (Name × VConstant)) {env env' : VEnv} {c : Name → List VLevel → V},
      env.ConstsClosed → CoherentOn ⟨κ, ls, c⟩ L env →
      env.addConstList cs = some env' →
      (∀ p ∈ cs, p.2.type.ConstsIn env.contains) →
      (∀ p ∈ cs, OracleOK L κ ls o (oracleExtend o (cs.map (·.1)) c) p.1 p.2) →
      CoherentOn ⟨κ, ls, oracleExtend o (cs.map (·.1)) c⟩ L env'
  | [], _, _, _, _, hC, hadd, _, _ => by
    simp only [VEnv.addConstList, List.foldlM_nil, Option.pure_def, Option.some_inj] at hadd
    exact hadd ▸ hC
  | q :: cs, env, env', c, hcl, hC, hadd, hocc, hok => by
    obtain ⟨env₁, hq, hrest⟩ := addConstList_cons.1 hadd
    have hcf : oracleExtend o ((q :: cs).map (·.1)) c
        = oracleExtend o (cs.map (·.1)) (cnstUpdate c q.1 (o q.1)) := rfl
    rw [hcf]
    have hle : env ≤ env₁ := VEnv.addConst_le hq
    have hfr := addConstList_fresh (q :: cs) hadd
    have hfrl : ∀ n ∈ cs.map (·.1), ¬ env.contains n := by
      intro n hn
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn
      exact hfr p (.tail _ hp)
    have hbridge : ∀ {e : VExpr}, e.ConstsIn env.contains →
        interp ⟨κ, ls, oracleExtend o (cs.map (·.1)) (cnstUpdate c q.1 (o q.1))⟩ L [] e
          = interp ⟨κ, ls, cnstUpdate c q.1 (o q.1)⟩ L [] e := fun he ↦
      interp_oracleExtend_eq L κ ls _ _ hfrl he
    have hstep : CoherentOn ⟨κ, ls, cnstUpdate c q.1 (o q.1)⟩ L env₁ := by
      refine coherentOn_addConst L hcl hq hC
        (fun {us us'} hw hw' hdd ↦ (hok q (.head _)).congr hw hw' hdd)
        (fun {us} hw hlen ↦ ?_)
      refine Above.imp ((hok q (.head _)).type hw hlen) fun h ↦ ?_
      rw [hcf] at h
      rwa [hbridge (VExpr.ConstsIn.instL.2 (hocc q (.head _)))] at h
    exact coherentOn_addConstList L o cs (hcl.addConst hq (hocc q (.head _))) hstep hrest
      (fun p hp ↦ (hocc p (.tail _ hp)).mono fun _ ↦ hle.contains)
      (fun p hp ↦ hcf ▸ hok p (.tail _ hp))

/-! ### Reconciling a staged extension with a single one

`VEnv.addInduct'` adds a block in **three** `addConstList` steps — types, then
constructors, then recursors — while `cnstOf`'s `.induct` line performs **one**
`oracleExtend o D.allNames`.  The `.induct` coherence step has to reconcile
those, and the two lemmas below are what does it.

Without them the three steps would have to be chained, and each intermediate
`OracleOK` would be stated at a *partial* assignment — the type formers'
obligation at an assignment where the constructors are not yet assigned — which
would then need `interp_cnst_congr` to move.  Collapsing to a single
`addConstList D.allConsts` avoids that entirely: every obligation is stated at
the one assignment `cnstOf` actually produces. -/

theorem addConstList_append : ∀ (l₁ l₂ : List (Name × VConstant)) {env env' : VEnv},
    env.addConstList (l₁ ++ l₂) = some env' ↔
      ∃ env₁, env.addConstList l₁ = some env₁ ∧ env₁.addConstList l₂ = some env'
  | [], l₂, env, env' => by
    simp only [List.nil_append]
    exact ⟨fun h ↦ ⟨env, rfl, h⟩, fun ⟨_, h1, h2⟩ ↦ by cases h1; exact h2⟩
  | q :: l₁, l₂, env, env' => by
    rw [List.cons_append]
    simp only [addConstList_cons]
    constructor
    · rintro ⟨e₁, h1, h2⟩
      obtain ⟨e₂, h3, h4⟩ := (addConstList_append l₁ l₂).1 h2
      exact ⟨e₂, ⟨e₁, h1, h3⟩, h4⟩
    · rintro ⟨e₂, ⟨e₁, h1, h3⟩, h4⟩
      exact ⟨e₁, h1, (addConstList_append l₁ l₂).2 ⟨e₂, h3, h4⟩⟩

theorem oracleExtend_append (o : Name → List VLevel → V) :
    ∀ (l₁ l₂ : List Name) (c : Name → List VLevel → V),
      oracleExtend o (l₁ ++ l₂) c = oracleExtend o l₂ (oracleExtend o l₁ c)
  | [], _, _ => rfl
  | n :: l₁, l₂, c => oracleExtend_append o l₁ l₂ (cnstUpdate c n (o n))

/-- **The step lemma for a block of defining equations.**  `addDefEq` never
touches `constants`, so the fold needs no freshness bookkeeping at all: each
equation contributes exactly its own two obligations. -/
theorem coherentOn_addDefEqFold {M : ModelData V} :
    ∀ (dfs : List VDefEq) {env : VEnv}, CoherentOn M L env →
      (∀ df ∈ dfs, ∀ {us : List VLevel}, (∀ l ∈ us, l.WF nv) → us.length = df.uvars →
        Above M ((interp M L [] (df.lhs.instL us)).toFun ∅
            = (interp M L [] (df.rhs.instL us)).toFun ∅) ∧
          Above M ((interp M L [] (df.lhs.instL us)).toFun ∅
            ∈ (interp M L [] (df.type.instL us)).toFun ∅)) →
      CoherentOn M L (dfs.foldl VEnv.addDefEq env)
  | [], _, hC, _ => hC
  | df :: dfs, _, hC, h =>
    coherentOn_addDefEqFold dfs
      (coherentOn_addDefEq hC (fun hw hl ↦ (h df (.head _) hw hl).1)
        (fun hw hl ↦ (h df (.head _) hw hl).2))
      (fun d hd ↦ h d (.tail _ hd))

end Lists

/-! ## Inhabiting a `∀`-denotation

The oracle has to *produce* elements of `⟦ci.type⟧` for constants that are
primitive — the axioms, the `Quot` operations, an inductive's constructors and
recursors — so it needs introduction rules for the two branches of the `forallE`
clause.  These are the only place the model builds a witness from scratch rather
than from a term. -/

section Forall

variable {env₀ : VEnv} {M : ModelData V} {Γ : List VExpr} {A B : VExpr} {u v : VLevel} {ρ : V}

/-- **Introduction, propositional codomain.**  A `Prop` denotes a subset of
`{•}`, so inhabiting `⟦∀ x : A, B⟧` is exactly proving `B` pointwise — there is
no function to build.  This is the rule the `Prop`-valued axioms use. -/
theorem pt_mem_interp_forallE_prop (hle : env₀ ≤ envF)
    (hB : env₀.HasType nv (A :: Γ) B (.sort v)) (hwv : v.WF nv) (hv : v.eval M.ls = 0)
    (h : ∀ w ∈ (interp M L Γ A).toFun ρ, pt ∈ (interp M L (A :: Γ) B).toFun (snoc ρ w)) :
    (pt : V) ∈ (interp M L Γ (.forallE A B)).toFun ρ := by
  rw [interp_forallE_prop M L ((isProp_iff hle hB hwv).2 hv)]
  exact mem_mkForallProp_iff.2 ⟨rfl, h⟩

/-- **Introduction, proper codomain.**  Any definable pointwise-correct function
gives an element, as its graph. -/
theorem mkLam_mem_interp_forallE (hle : env₀ ≤ envF)
    (hB : env₀.HasType nv (A :: Γ) B (.sort v)) (hwv : v.WF nv) (hv : v.eval M.ls ≠ 0)
    {F : V → V} (hF : ℒₛₑₜ-function₁[V] F)
    (h : ∀ w ∈ (interp M L Γ A).toFun ρ, F w ∈ (interp M L (A :: Γ) B).toFun (snoc ρ w)) :
    mkLam (interp M L Γ A).toFun (interp M L Γ A).definable (fun _ w ↦ F w)
        (by definability) ρ
      ∈ (interp M L Γ (.forallE A B)).toFun ρ := by
  rw [interp_forallE_type M L (fun hp ↦ hv ((isProp_iff hle hB hwv).1 hp))]
  exact mkLam_mem_mkForallType h

/-- **Introduction, proper codomain, environment-passing form.**

The same statement as `mkLam_mem_interp_forallE` but with the fibre map taking
the environment, which is the form a *nested* λ needs — see
`SetModel/Definability.lean` on why capturing the outer variable instead breaks
the composition.

Proving it once, schematically, also matters for elaboration: applied directly,
`mkLam_mem_mkForallType` has to unify the two `ℒₛₑₜ`-definability *proof terms*,
and at a concrete call site those are large enough to hang `whnf`. Here they are
variables. -/
theorem mkLam_mem_interp_forallE' (hle : env₀ ≤ envF)
    (hB : env₀.HasType nv (A :: Γ) B (.sort v)) (hwv : v.WF nv) (hv : v.eval M.ls ≠ 0)
    {F : V → V → V} (hF : ℒₛₑₜ-function₂[V] F)
    (h : ∀ w ∈ (interp M L Γ A).toFun ρ,
      F ρ w ∈ (interp M L (A :: Γ) B).toFun (snoc ρ w)) :
    mkLam (interp M L Γ A).toFun (interp M L Γ A).definable F hF ρ
      ∈ (interp M L Γ (.forallE A B)).toFun ρ := by
  rw [interp_forallE_type M L (fun hp ↦ hv ((isProp_iff hle hB hwv).1 hp))]
  exact mkLam_mem_mkForallType h

/-- **The interpretation is insensitive to the value stored at a proof-sorted
application.**

`interp` sends `.app f a` to `•` whenever `f` is a proof, and whether `f` is a
proof is decided by `L.srt Γ f` and `M.ls` alone — **`M.cnst` does not appear**.
So if `f`'s type is a proposition, the denotation of `f a` is `•` no matter what
value the constant assignment gives to any constant occurring in `f`.

This is a fact about `interp`, not about any particular constant, and it is what
makes a degenerate `Prop` witness safe: assigning `•` to a `Prop`-valued
constant cannot corrupt anything downstream, because every elimination of it
short-circuits before the assignment is consulted.  Every `Prop`-valued
constructor of an inductive sits in this position. -/
theorem interp_app_of_proof_sorted (hle : env₀ ≤ envF) {Γ : List VExpr} {f A : VExpr}
    {v : VLevel} (hf : env₀.HasType nv Γ f A) (hA : env₀.HasType nv Γ A (.sort v))
    (hw : v.WF nv) (h0 : v.eval M.ls = 0) (a : VExpr) (ρ : V) :
    (interp M L Γ (.app f a)).toFun ρ = pt :=
  interp_app_proof M L ((isProof_iff hle hf hA hw).2 h0) ρ

end Forall

/-! ## Defining equations: peel by type agreement, split only at the bodies

Every ι-rule the model has to validate — `quotDefEq` now, every inductive's
recursor equation later — is an equation between two λ-nests over the *same*
binders, differing only in the bodies.  The step below is what peels one binder,
and stating it generally is worth doing once because the naive version has a
trap in it.

`interp` sends `.lam A b` to `•` when `b` is a proof and to a `mkLam` otherwise,
so an equation between two `lam`s needs the two bodies to *agree* on `IsProof`
before their pointwise equality is of any use.  **That agreement is not free.**
`IsProof` is syntactic — it is `(L.srt Γ b).eval M.ls = 0` — so it does not
follow from the bodies denoting the same thing at every valuation.

What it does follow from is the two bodies having the **same type**, via
`isProof_iff` on each side.  For a defining equation that is exactly the
situation: both sides are typed at `df.type`.  So the whole nest peels
*uniformly*, with no case analysis at any binder, and whatever level split the
equation needs appears once, at the bodies. -/

section DefEqStep

variable {env₀ : VEnv} {M : ModelData V} {Γ : List VExpr} {A B b b' : VExpr}
variable {w : VLevel} {ρ : V}

/-- **One binder of a defining equation, given the `IsProof` agreement.** -/
theorem interp_lam_congr
    (hp : L.IsProof M (A :: Γ) b ↔ L.IsProof M (A :: Γ) b')
    (h : ∀ x ∈ (interp M L Γ A).toFun ρ,
      (interp M L (A :: Γ) b).toFun (snoc ρ x) = (interp M L (A :: Γ) b').toFun (snoc ρ x)) :
    (interp M L Γ (.lam A b)).toFun ρ = (interp M L Γ (.lam A b')).toFun ρ := by
  by_cases hb : L.IsProof M (A :: Γ) b
  · rw [interp_lam_proof M L hb, interp_lam_proof M L (hp.1 hb)]
  · have hb' : ¬ L.IsProof M (A :: Γ) b' := fun h' ↦ hb (hp.2 h')
    ext y
    rw [mem_interp_lam_iff M L hb, mem_interp_lam_iff M L hb']
    exact ⟨fun ⟨x, hx, hy⟩ ↦ ⟨x, hx, by rw [hy, h x hx]⟩,
      fun ⟨x, hx, hy⟩ ↦ ⟨x, hx, by rw [hy, h x hx]⟩⟩

/-- **One binder of a defining equation, from the shared type.**  This is the
form a defeq obligation actually takes: the two bodies are typed at the same `B`,
which is what supplies the `IsProof` agreement. -/
theorem interp_lam_congr_of_type (hle : env₀ ≤ envF)
    (hb : env₀.HasType nv (A :: Γ) b B) (hb' : env₀.HasType nv (A :: Γ) b' B)
    (hB : env₀.HasType nv (A :: Γ) B (.sort w)) (hw : w.WF nv)
    (h : ∀ x ∈ (interp M L Γ A).toFun ρ,
      (interp M L (A :: Γ) b).toFun (snoc ρ x) = (interp M L (A :: Γ) b').toFun (snoc ρ x)) :
    (interp M L Γ (.lam A b)).toFun ρ = (interp M L Γ (.lam A b')).toFun ρ :=
  interp_lam_congr ((isProof_iff hle hb hB hw).trans (isProof_iff hle hb' hB hw).symm) h

end DefEqStep

/-! ## Discharging the oracle -/

section Oracle

variable {c o : Name → List VLevel → V} {n : Name} {ci : VConstant}

/-- The oracle's obligations, with the thresholds trivial.  Every primitive the
model supplies is built outright rather than approximated, so no chain length is
needed and `Above.pure` discharges both wrappers. -/
theorem oracleOK_of
    (hcg : ∀ {us us' : List VLevel}, (∀ l ∈ us, l.WF nv) → (∀ l ∈ us', l.WF nv) →
      List.Forall₂ (· ≈ ·) us us' → o n us = o n us')
    (hty : ∀ {us : List VLevel}, (∀ l ∈ us, l.WF nv) → us.length = ci.uvars →
      o n us ∈ (interp ⟨κ, ls, c⟩ L [] (ci.type.instL us)).toFun ∅) :
    OracleOK L κ ls o c n ci :=
  ⟨fun hw hw' hd ↦ Above.pure (hcg hw hw' hd), fun hw hl ↦ Above.pure (hty hw hl)⟩

/-- **The chain-dependent form, which is what `OracleOK` already asks for.**

`oracleOK_of` above takes *unconditional* obligations and wraps them with
`Above.pure`, which is right for the `Quot` primitives — every one of them is
built outright.  An inductive block is different: its signature's properties are
only available above a threshold (`docs/model-interface.md` §4), so its
obligations arrive already wrapped.

Nothing has to be unwrapped to use them. `OracleOK`'s two fields *are* `Above`s,
so this is the identity — and stating it is the point, because the shape of the
`.induct` step turns on noticing that the consumer already accepts the weaker
form. -/
theorem oracleOK_above
    (hcg : ∀ {us us' : List VLevel}, (∀ l ∈ us, l.WF nv) → (∀ l ∈ us', l.WF nv) →
      List.Forall₂ (· ≈ ·) us us' → Above (V := V) ⟨κ, ls, c⟩ (o n us = o n us'))
    (hty : ∀ {us : List VLevel}, (∀ l ∈ us, l.WF nv) → us.length = ci.uvars →
      Above (V := V) ⟨κ, ls, c⟩
        (o n us ∈ (interp ⟨κ, ls, c⟩ L [] (ci.type.instL us)).toFun ∅)) :
    OracleOK L κ ls o c n ci :=
  ⟨fun hw hw' hd ↦ hcg hw hw' hd, fun hw hl ↦ hty hw hl⟩

/-- **A `Prop`-valued primitive.**  Its witness is `•` regardless of the level
arguments, so `const_congr` is `rfl` and the whole obligation is that the
proposition holds in the model.  `propext` and `Quot.sound` are both of this
shape. -/
theorem oracleOK_prop (hpt : ∀ us, o n us = pt)
    (hty : ∀ {us : List VLevel}, (∀ l ∈ us, l.WF nv) → us.length = ci.uvars →
      (pt : V) ∈ (interp ⟨κ, ls, c⟩ L [] (ci.type.instL us)).toFun ∅) :
    OracleOK L κ ls o c n ci :=
  oracleOK_of (fun _ _ _ ↦ by rw [hpt, hpt]) (fun hw hl ↦ by rw [hpt]; exact hty hw hl)

end Oracle

/-! ## The assignment

`cnstOf` is a structural recursion on the declaration list, matching the order
`VEnv.WF'` gives.  `interp_cnst_congr` is what makes it *extend* rather than
revisit: a term already interpreted keeps its denotation, because the
interpretation depends on `cnst` only at the constants that occur in it. -/

/-- The names `VEnv.addQuot` declares, in the order it declares them. -/
def quotNames : List Name := [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]

/-- **The constant assignment of a declaration list.**

`o` is the oracle: it supplies the values the model cannot compute — axioms,
the `Quot` primitives, and whatever an inductive declaration introduces.  Its
obligations are `OracleOK`; everything else is computed. -/
noncomputable def cnstOf (L : LevelAssign envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o : Name → List VLevel → V) : List VDecl → (Name → List VLevel → V)
  | [] => fun _ _ ↦ ∅
  | .axiom ci :: ds => cnstUpdate (cnstOf L κ ls o ds) ci.name (o ci.name)
  | .def ci :: ds => defExtend L κ ls (cnstOf L κ ls o ds) ci
  | .opaque ci :: ds => defExtend L κ ls (cnstOf L κ ls o ds) ci
  | .example _ :: ds => cnstOf L κ ls o ds
  | .quot :: ds => oracleExtend o quotNames (cnstOf L κ ls o ds)
  | .induct D :: ds => oracleExtend o D.allNames (cnstOf L κ ls o ds)
  -- `.unsafeDef` has no image.  A self-referential block has no assignment at
  -- all (`Theory/MutualDefUnsound.lean`), which is why `VDecl.isPure` excludes
  -- it and why the coherence theorem will be stated for the pure fragment.
  | .unsafeDef _ :: ds => cnstOf L κ ls o ds

end Lean4Lean.SetModel
