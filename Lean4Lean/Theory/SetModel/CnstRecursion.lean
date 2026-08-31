import Lean4Lean.Theory.SetModel.Cnst
import Lean4Lean.Theory.SetModel.FalseProp
import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.Inductive.Nested
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# The outer recursion for `ModelData.cnst`, and the one obligation it cannot discharge

`SetModel/Cnst.lean` defines `cnstOf`, the constant assignment of a declaration
list, and proves the per-declaration coherence steps.  What was missing is the
*recursion*: `CoherentOn ⟨κ, ls, cnstOf L κ ls o ds⟩ L env` from
`VEnv.WF' ds env`.  This file proves it, and isolates what is left over.

## What is proved outright

`coherentOn_cnstOf` runs the whole induction over `VEnv.WF'`.  Of the seven
`VDecl` forms:

| form | discharged by |
|---|---|
| `.def` | `coherentOn_defEq` (Cnst.lean) — value *and* defining equation |
| `.opaque` | `coherentOn_defConst` (Cnst.lean) |
| `.example` | nothing to do: the environment and the assignment are both unchanged |
| `.unsafeDef` | excluded by `VDecl.noUnsafe`, which `VEnv.LeanWF` supplies |
| `.axiom` | `coherentOn_addConst` from the oracle obligation `OracleOK` |
| `.quot` | `coherentOn_addConstList'` + `coherentOn_addDefEq`, occurrence side-condition **proved** (`stagedOcc_quotConsts`) |
| `.induct` | **not discharged** — `InductOracleOK`, the residual |

So the reduction is: *H2 minus the `.induct` oracle*, plus the separately-tracked
inputs of §7 (`InaccModelInput`, `ModelFitsInput`).  §6 composes the recursion with
`FalseProp.lean` to `leanTTConsistent`; §7 states H2 from those two inputs
(`upper_bound_of`); §8 is the boundary control on the residual.  This is a
reduction, not a closure — the residual is named rather than hidden in a `sorry`,
and no joint witness for the full hypothesis set is exhibited anywhere.

## The boundary control, and a ledger correction

`docs/soundness-ledger.md` lists `coherentOn_addInduct` (`SetModel/IndInterp.lean`)
as a *proved step lemma* available to this recursion.  It is proved, but it is
**vacuous**: its occurrence hypothesis

    hocc : ∀ p ∈ D.allConsts, p.2.type.ConstsIn env.contains

is stated at the environment *before the whole block*, while
`env.addConstList D.allConsts = some e₁` forces every name of the block to be
fresh for that same `env`.  Any block one of whose declared types mentions
another name of the block therefore has an unsatisfiable hypothesis set.  Every
real inductive is such a block: a constructor's type mentions its own type
former.  `addConstList_hocc_unsat` proves the general statement and
`hocc_unsat_eqIndDecl` instantiates it at `eqIndDecl`, the first declaration of
`leanPrelude` — machine-checked, so this is a fact and not a reading.

The same defect is in `coherentOn_addConstList` (`SetModel/Cnst.lean`), which
`coherentOn_addInduct` is built from.  Neither file is edited here; the corrected
lemma `coherentOn_addConstList'` lives in this file, with the occurrence
condition **staged** (`StagedOcc`): each declaration's type mentions only
constants available at *its own* stage, which is what the proof actually needs
and what a real block actually satisfies.

`stagedOcc_separates` is the boundary control in the strict sense asked for: one
concrete two-constant block on which `StagedOcc` holds and the old hypothesis
provably fails.  So the corrected lemma is not vacuous, and it is not the old one
in disguise.
-/

namespace Lean4Lean.SetModel

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The occurrence condition, staged

`coherentOn_addConstList`'s proof needs exactly one thing from the occurrence
hypothesis: that the *head* declaration's type mentions no name that the *tail*
of the block will declare, so that extending the assignment along the tail leaves
its denotation alone.  Asking for `ConstsIn env.contains` at the block's initial
environment is one way to get that, and it is too strong — fatally so. -/

/-- **Each declaration's type mentions only constants available at its own
stage.**  The staged replacement for `coherentOn_addConstList`'s `hocc`.

Read the `cons` clause as: `p`'s type is checkable in the environment `p` is
added to, and the rest of the block satisfies the same condition one stage on.
Because `addConst` is deterministic on success, the `∀ env₁` is a single
obligation, not a family. -/
def StagedOcc : VEnv → List (Name × VConstant) → Prop
  | _, [] => True
  | env, p :: cs => p.2.type.ConstsIn env.contains ∧
      ∀ env₁, env.addConst p.1 p.2 = some env₁ → StagedOcc env₁ cs

theorem stagedOcc_nil {env : VEnv} : StagedOcc env [] := trivial

theorem stagedOcc_cons {env : VEnv} {p : Name × VConstant} {cs : List (Name × VConstant)}
    (h1 : p.2.type.ConstsIn env.contains)
    (h2 : ∀ env₁, env.addConst p.1 p.2 = some env₁ → StagedOcc env₁ cs) :
    StagedOcc env (p :: cs) := ⟨h1, h2⟩

/-- A name added by `addConst` is present afterwards. -/
theorem addConst_contains {env env' : VEnv} {n : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') : env'.contains n := by
  unfold VEnv.addConst at h
  split at h
  · exact absurd h nofun
  · cases h; exact ⟨ci, by simp⟩

/-! ## 2. Boundary control: the unstaged condition is unsatisfiable

This is the part that must be checked rather than argued, because the whole
point of the corrected lemma is that the original could never fire. -/

/-- **The original occurrence hypothesis is unsatisfiable for any block that
mentions its own names.**  `p` and `q` are members of the same block, and `p`'s
type mentions `q`'s name; `addConstList` succeeding says `q`'s name is fresh for
`env`, so `p`'s type cannot mention only constants of `env`.

Note that `p = q` is allowed: a self-referential type triggers it too. -/
theorem addConstList_hocc_unsat {env env' : VEnv} (cs : List (Name × VConstant))
    (hadd : env.addConstList cs = some env') {p q : Name × VConstant}
    (hp : p ∈ cs) (hq : q ∈ cs) (hmem : ¬ p.2.type.ConstsIn (fun n ↦ n ≠ q.1)) :
    ¬ ∀ r ∈ cs, r.2.type.ConstsIn env.contains := fun h ↦
  hmem <| (h p hp).mono fun n (hn : env.contains n) (hne : n = q.1) ↦
    addConstList_fresh cs hadd q hq (hne ▸ hn)

/-! ### Instantiated at the prelude's first declaration

`eqIndDecl` is the head of `leanPrelude`, so if the recursion cannot pass it the
recursion cannot start.  The two `rfl`s below are what make this concrete rather
than schematic: they compute the block's type constant and its constructor
constant, and the constructor's declared type visibly contains `.const `Eq`. -/

/-- `eqIndDecl`'s type constant, computed. -/
theorem eqIndDecl_typeConsts : eqIndDecl.typeConsts =
    [(`Eq, ⟨1, VExpr.mkPi [.sort (.param 0), .bvar 0, .bvar 1] (.sort .zero)⟩)] := rfl

/-- `eqIndDecl`'s constructor constant, computed.  `Eq.refl`'s declared type is
`∀ {α : Sort u} (a : α), Eq α a a` — it **mentions `Eq`**, which the same block
declares. -/
theorem eqIndDecl_ctorConsts : eqIndDecl.ctorConsts =
    [(`Eq.refl, ⟨1, (VExpr.sort (VLevel.param 0)).forallE
      ((VExpr.bvar 0).forallE
        ((((VExpr.const `Eq [VLevel.param 0]).app (VExpr.bvar 1)).app
          (VExpr.bvar 0)).app (VExpr.bvar 0)))⟩)] := rfl

/-- **The ledger correction, machine-checked.**  For `eqIndDecl` — the first
declaration of `leanPrelude` — `coherentOn_addConstList`'s and
`coherentOn_addInduct`'s occurrence hypothesis is *inconsistent with their own
`addConstList` hypothesis*.  So neither lemma can be applied to it, and by the
same argument neither can be applied to any inductive with a constructor
mentioning its type former, i.e. to any inductive with a constructor at all. -/
theorem hocc_unsat_eqIndDecl {env env' : VEnv}
    (hadd : env.addConstList eqIndDecl.allConsts = some env') :
    ¬ ∀ p ∈ eqIndDecl.allConsts, p.2.type.ConstsIn env.contains := by
  refine addConstList_hocc_unsat _ hadd
    (p := (`Eq.refl, ⟨1, (VExpr.sort (VLevel.param 0)).forallE
      ((VExpr.bvar 0).forallE
        ((((VExpr.const `Eq [VLevel.param 0]).app (VExpr.bvar 1)).app
          (VExpr.bvar 0)).app (VExpr.bvar 0)))⟩))
    (q := (`Eq, ⟨1, VExpr.mkPi [.sort (.param 0), .bvar 0, .bvar 1] (.sort .zero)⟩))
    ?_ ?_ ?_
  · simp [VInductDecl'.allConsts, eqIndDecl_ctorConsts]
  · simp [VInductDecl'.allConsts, eqIndDecl_typeConsts]
  · simp [VExpr.ConstsIn]

/-! ### And the staged condition *is* satisfiable on the same shape

Boundary control proper: a block whose second declaration's type mentions the
first.  `StagedOcc` holds; the unstaged condition provably does not.  The two
conditions are therefore not interchangeable, and the corrected lemma is not
vacuous. -/

/-- A two-constant block: `A : Prop`, then `B : A`. -/
def toyBlock : List (Name × VConstant) :=
  [(`ToyA, ⟨0, .sort .zero⟩), (`ToyB, ⟨0, .const `ToyA []⟩)]

theorem toyBlock_add : ∃ env', VEnv.empty.addConstList toyBlock = some env' := ⟨_, rfl⟩

/-- **The separation.**  On `toyBlock` over the empty environment the staged
condition holds and the unstaged one fails. -/
theorem stagedOcc_separates :
    StagedOcc VEnv.empty toyBlock ∧
      ¬ ∀ p ∈ toyBlock, p.2.type.ConstsIn VEnv.empty.contains := by
  refine ⟨⟨trivial, fun env₁ h ↦ ⟨?_, fun _ _ ↦ trivial⟩⟩, ?_⟩
  · exact addConst_contains h
  · intro h
    have := h (`ToyB, ⟨0, .const `ToyA []⟩) (by simp [toyBlock])
    obtain ⟨_, hc⟩ : VEnv.empty.contains `ToyA := this
    exact absurd hc nofun

/-! ## 3. The corrected block step lemma

Word for word `coherentOn_addConstList` with `hocc` replaced by `StagedOcc`.
The proof is unchanged: what the head step consumes is `hocc.1`, and what the
recursive call consumes is `hocc.2` at the intermediate environment — which is
precisely the information the unstaged form threw away. -/

section
variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

/-- **The step lemma for a block of constants, with the occurrence condition
staged.**  Replaces `coherentOn_addConstList`, whose hypotheses are jointly
unsatisfiable whenever the block mentions its own names
(`addConstList_hocc_unsat`). -/
theorem coherentOn_addConstList' (L : PropSplit envF nv) (o : Name → List VLevel → V) :
    ∀ (cs : List (Name × VConstant)) {env env' : VEnv} {c : Name → List VLevel → V},
      env.ConstsClosed → CoherentOn ⟨κ, ls, c⟩ L env →
      env.addConstList cs = some env' →
      StagedOcc env cs →
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
      rwa [hbridge (VExpr.ConstsIn.instL.2 hocc.1)] at h
    exact coherentOn_addConstList' L o cs (hcl.addConst hq hocc.1) hstep hrest
      (hocc.2 env₁ hq) (fun p hp ↦ hcf ▸ hok p (.tail _ hp))

end

/-! ## 4. Environment extensions as one `addConstList` plus one `addDefEq` fold

`.quot` and `.induct` both extend the environment as a block of constants
followed by a block of equations.  These two lemmas put them in that form, so a
single pair of step lemmas covers both. -/

/-- `addConstList` splits over `++` at the level of `Option`, not just as an
`iff` about success. -/
theorem addConstList_append' (l₁ l₂ : List (Name × VConstant)) (env : VEnv) :
    env.addConstList (l₁ ++ l₂) = (env.addConstList l₁).bind (·.addConstList l₂) := by
  rcases h : env.addConstList (l₁ ++ l₂) with _ | e
  · rcases h1 : env.addConstList l₁ with _ | e1
    · simp
    · simp only [Option.bind_some]
      rcases h2 : e1.addConstList l₂ with _ | e2
      · rfl
      · exact absurd (h.symm.trans ((addConstList_append l₁ l₂).2 ⟨e1, h1, h2⟩)) nofun
  · obtain ⟨e1, h1, h2⟩ := (addConstList_append l₁ l₂).1 h
    simp [h1, h2]

/-- The four constants `VEnv.addQuot` declares, paired with their types. -/
def quotConsts : List (Name × VConstant) :=
  [(``Quot, quotConst), (``Quot.mk, quotMkConst), (``Quot.lift, quotLiftConst),
   (``Quot.ind, quotIndConst)]

theorem quotNames_eq : quotNames = quotConsts.map (·.1) := rfl

/-- `addQuot` is one `addConstList` and one `addDefEq`. -/
theorem addQuot_eq (env : VEnv) :
    env.addQuot = (env.addConstList quotConsts).map (·.addDefEq quotDefEq) := by
  simp only [VEnv.addQuot, VEnv.addConstList, quotConsts, List.foldlM_cons, List.foldlM_nil]
  rcases env.addConst ``Quot quotConst with _ | e1 <;> simp
  rcases e1.addConst ``Quot.mk quotMkConst with _ | e2 <;> simp
  rcases e2.addConst ``Quot.lift quotLiftConst with _ | e3 <;> simp
  rcases e3.addConst ``Quot.ind quotIndConst with _ | e4 <;> simp

/-- `addInduct'` is one `addConstList` over `D.allConsts` and one `addDefEq`
fold over `D.iotaRules` — the collapse `Cnst.lean`'s
"Reconciling a staged extension with a single one" section is aimed at. -/
theorem addInduct'_iff {env env' : VEnv} {D : VInductDecl'} :
    env.addInduct' D = some env' ↔
      ∃ e, env.addConstList D.allConsts = some e ∧ env' = e.addIndRules D := by
  simp only [VEnv.addInduct', VEnv.addIndTypes, VEnv.addIndCtors, VEnv.addIndRecs,
    VInductDecl'.allConsts, addConstList_append']
  rcases env.addConstList D.typeConsts with _ | e1 <;> simp
  rcases e1.addConstList D.ctorConsts with _ | e2 <;> simp
  rcases e2.addConstList D.recConsts with _ | e3 <;> simp
  exact eq_comm

/-- The same statement against `addInduct'` rather than the bare
`addConstList` — the form `coherentOn_addInduct` is stated in. -/
theorem hocc_unsat_eqIndDecl' {env env' : VEnv}
    (hadd : env.addInduct' eqIndDecl = some env') :
    ¬ ∀ p ∈ eqIndDecl.allConsts, p.2.type.ConstsIn env.contains :=
  let ⟨_, h, _⟩ := addInduct'_iff.1 hadd; hocc_unsat_eqIndDecl h

/-! ### The `.quot` occurrence condition, discharged

`quotConsts` is a block whose later members mention its earlier ones
(`Quot.mk` mentions `Quot`; `Quot.lift` mentions `Quot` and `Eq`; `Quot.ind`
mentions `Quot` and `Quot.mk`), so by `addConstList_hocc_unsat` the *unstaged*
condition fails for it too.  Staged, it is provable — and this is the whole
occurrence-side obligation of the `.quot` case, so `.quot` needs nothing from the
residual. -/

theorem quotConst_constsIn {P : Name → Prop} : quotConst.type.ConstsIn P := by
  simp [quotConst, VExpr.ConstsIn]

theorem quotMkConst_constsIn {P : Name → Prop} (h : P ``Quot) :
    quotMkConst.type.ConstsIn P := by simp [quotMkConst, VExpr.ConstsIn, h]

theorem quotLiftConst_constsIn {P : Name → Prop} (h : P ``Quot) (h2 : P ``Eq) :
    quotLiftConst.type.ConstsIn P := by simp [quotLiftConst, VExpr.ConstsIn, h, h2]

theorem quotIndConst_constsIn {P : Name → Prop} (h : P ``Quot) (h2 : P ``Quot.mk) :
    quotIndConst.type.ConstsIn P := by simp [quotIndConst, VExpr.ConstsIn, h, h2]

/-- **The staged occurrence condition for the quotient block**, from
`VEnv.QuotReady` alone — which is exactly what `VDecl.WF.quot` provides. -/
theorem stagedOcc_quotConsts {env : VEnv} (hq : env.QuotReady) :
    StagedOcc env quotConsts := by
  have hEq : env.contains ``Eq := ⟨_, hq⟩
  refine ⟨quotConst_constsIn, fun e1 h1 ↦ ?_⟩
  have hle1 : env ≤ e1 := VEnv.addConst_le h1
  have hQ1 : e1.contains ``Quot := addConst_contains h1
  refine ⟨quotMkConst_constsIn hQ1, fun e2 h2 ↦ ?_⟩
  have hle2 : e1 ≤ e2 := VEnv.addConst_le h2
  have hMk2 : e2.contains ``Quot.mk := addConst_contains h2
  refine ⟨quotLiftConst_constsIn (hle2.contains hQ1) (hle2.contains (hle1.contains hEq)),
    fun e3 h3 ↦ ?_⟩
  have hle3 : e2 ≤ e3 := VEnv.addConst_le h3
  exact ⟨quotIndConst_constsIn (hle3.contains (hle2.contains hQ1)) (hle3.contains hMk2),
    fun _ _ ↦ trivial⟩


/-! ## 5. The recursion, and the residual

`coherentOn_cnstOf` is the induction over `VEnv.WF'`.  It takes one hypothesis
per *non-computed* declaration form — `.axiom`, `.quot`, `.induct` — bundled as
`OracleFits`, and discharges everything else.  Of the three:

* `.axiom`'s obligation is what the main theorem's axiom-validation supplies
  (`InterpSound.lean`'s `AxiomsValidated`; `PreludeSpec.lean` has the three
  witnesses).  It is a statement about the oracle at a single name.
* `.quot`'s is supplied by `SetModel/QuotInterp.lean` (`quotDefEq_ok` and the
  `quotFn`/`quotMkFn`/`quotLiftFn` inhabitation lemmas), once the oracle is
  *defined* to be those functions at the four quotient names.  The occurrence
  side condition is proved here (`stagedOcc_quotConsts`).
* `.induct`'s is **`InductOracleOK`, the residual**.  Nothing in the tree
  inhabits it, and §6 says exactly why.
-/

section Recursion

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

/-- What the model owes for one defining equation: both sides denote the same
element, and it lies in the equated type.  Exactly `coherentOn_addDefEq`'s pair
of hypotheses, named so that the ι-rule obligation can be quantified over a
list. -/
def DefEqOK (L : PropSplit envF nv) (M : ModelData V) (df : VDefEq) : Prop :=
  ∀ {us : List VLevel}, (∀ l ∈ us, l.WF nv) → us.length = df.uvars →
    Above M ((interp M L [] (df.lhs.instL us)).toFun ∅
        = (interp M L [] (df.rhs.instL us)).toFun ∅) ∧
      Above M ((interp M L [] (df.lhs.instL us)).toFun ∅
        ∈ (interp M L [] (df.type.instL us)).toFun ∅)

/-- What the oracle owes at a `.quot` step: the four quotient constants inhabit
their types, and the `Quot.lift`/`Quot.mk` ι-rule holds.  `SetModel/QuotInterp.lean`
proves both for the intended oracle. -/
structure QuotOracleOK (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o c : Name → List VLevel → V) : Prop where
  consts : ∀ p ∈ quotConsts, OracleOK L κ ls o c p.1 p.2
  rule : DefEqOK L ⟨κ, ls, c⟩ quotDefEq

/-- **The residual: what the oracle owes at an `.induct` step.**

`c` is the assignment *after* the block, i.e. `cnstOf` applied to the list whose
head is this declaration — so all three fields are stated at the one assignment
the construction actually produces, with no partial stage anywhere.

To inhabit this for a block `D` one must produce, from `D` alone:

1. `staged` — that each of `D`'s declared types (type formers, then constructors,
   then recursors, in `addInduct'`'s order) mentions only constants available at
   its own stage.  For the type formers this is `D.WF env`'s `params`/`types`
   fields; for the constructors it is its `ctors` field, which is *already*
   staged at `addIndTypes`; for the recursors it is a consequence of
   `addInduct_WF`, which is where the work is.
2. `consts` — a set-theoretic element of `⟦T.type⟧` for each type former, of
   `⟦C.type D j⟧` for each constructor, and of `⟦D.recType j⟧` for each
   recursor, each invariant under level-equivalent instantiations.  This is the
   inductive-types model: `SetModel/IndStage.lean`'s least fixed point for the
   type formers, `mkLam` nests for the constructors, and the recursion theorem
   for the recursors.
3. `rules` — that every ι-rule of `D` holds in the model, i.e. that the
   recursor's denotation applied to a constructor's denotation reduces to the
   corresponding minor premise.  `Cnst.lean`'s `interp_lam_congr_of_type` peels
   the λ-nest; the bodies are where the ι-computation happens.

**What blocks it today.** (2) and (3) need the translation from `VIndCtor` to the
argument/field data the fixed-point construction consumes (`CtorData₃`/`Args`);
per `docs/soundness-ledger.md` item 2 that translation is waiting on a
`Theory/Inductive/Decl.lean` clause making the recursive-argument position `Pos q a`
computable from `a`.  It is *not* blocked on anything in this file, and it is not
blocked on the `.quot`, `.axiom`, `.def` or `.opaque` cases, all of which are
discharged here. -/
structure InductOracleOK (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o c : Name → List VLevel → V) (D : VInductDecl') : Prop where
  staged : ∀ {env env' : VEnv}, env.addInduct' D = some env' → StagedOcc env D.allConsts
  consts : ∀ p ∈ D.allConsts, OracleOK L κ ls o c p.1 p.2
  rules : ∀ df ∈ D.iotaRules, DefEqOK L ⟨κ, ls, c⟩ df

/-- The oracle's obligation at one declaration step.  Only the three
non-computed forms carry one. -/
def OracleStepOK (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o : Name → List VLevel → V) : VDecl → List VDecl → Prop
  | .axiom ci, ds =>
    OracleOK L κ ls o (cnstOf L κ ls o (.axiom ci :: ds)) ci.name ci.toVConstant
  | .quot, ds => QuotOracleOK L κ ls o (cnstOf L κ ls o (.quot :: ds))
  | .induct D, ds => InductOracleOK L κ ls o (cnstOf L κ ls o (.induct D :: ds)) D
  | _, _ => True

/-- The oracle's obligations along a whole declaration list. -/
def OracleFits (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o : Name → List VLevel → V) : List VDecl → Prop
  | [] => True
  | d :: ds => OracleStepOK L κ ls o d ds ∧ OracleFits L κ ls o ds

/-- Coherence at the empty environment, for the assignment `cnstOf` starts
from.  `const_congr` is not vacuous here — it quantifies over *all* names, not
only declared ones — but the initial assignment is constant, so it is `rfl`. -/
theorem coherentOn_empty_cnstOf (L : PropSplit envF nv) (κ : ℕ → V) (ls : List ℕ)
    (o : Name → List VLevel → V) :
    CoherentOn (V := V) ⟨κ, ls, cnstOf L κ ls o []⟩ L .empty :=
  ⟨fun _ _ _ ↦ Above.pure rfl, fun h _ _ ↦ absurd h nofun,
   fun h _ _ ↦ h.elim, fun h _ _ ↦ h.elim⟩

theorem wf'_cons_inv {d : VDecl} {ds : List VDecl} {env : VEnv}
    (h : VEnv.WF' (d :: ds) env) : ∃ env₀, VDecl.WF env₀ d env ∧ VEnv.WF' ds env₀ := by
  cases h with | decl h1 h2 => exact ⟨_, h1, h2⟩

variable (L : PropSplit envF nv) (o : Name → List VLevel → V)
variable {R : List VExpr → List VExpr → Prop}
variable (hS : L.Stable) (hR : CtxInvariant L R)
variable (hRdF : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
  envF.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))

include hS hR hRdF in
/-- **The outer recursion.**  `CoherentOn` for the assignment `cnstOf` builds,
along any declaration list that is well formed, free of `partial`/`unsafe`
blocks, and whose non-computed declarations the oracle satisfies.

The `.def`, `.opaque` and `.example` cases consume no hypothesis beyond
soundness at the earlier environment; `.unsafeDef` is refuted by `noUnsafe`;
`.axiom` and `.quot` and `.induct` consume `OracleFits`. -/
theorem coherentOn_cnstOf :
    ∀ (ds : List VDecl) {env : VEnv}, VEnv.WF' ds env → env ≤ envF →
      (∀ d ∈ ds, d.noUnsafe) → OracleFits L κ ls o ds →
      CoherentOn ⟨κ, ls, cnstOf L κ ls o ds⟩ L env
  | [], env, hwf, _, _, _ => by
    cases hwf; exact coherentOn_empty_cnstOf L κ ls o
  | d :: ds, env, hwf, hle, hnu, hfits => by
    obtain ⟨env₀, hd, hds⟩ := wf'_cons_inv hwf
    have hle₀ : env₀ ≤ envF := VEnv.LE.trans (VDecl.WF.le hd) hle
    have henv₀ : env₀.Ordered := VEnv.WF.ordered ⟨ds, hds⟩
    have hC : CoherentOn ⟨κ, ls, cnstOf L κ ls o ds⟩ L env₀ :=
      coherentOn_cnstOf ds hds hle₀ (fun e he ↦ hnu e (.tail _ he)) hfits.2
    have hRd₀ : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
        env₀.IsDefEq nv Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ) :=
      fun h ↦ hRdF (VEnv.IsDefEq.mono hle₀ h)
    match d, hd, hfits.1 with
    | .axiom ci, .axiom _ hadd, hok =>
      exact coherentOn_addConst L henv₀.constsClosed hadd hC
        (fun hw hw' hdd ↦ hok.congr hw hw' hdd) (fun hw hlen ↦ hok.type hw hlen)
    | .def ci, .def hci hadd, _ =>
      exact coherentOn_defEq hle₀ henv₀ hS hC hR hRd₀ hci hadd
    | .opaque ci, .opaque hci hadd, _ =>
      exact coherentOn_defConst hle₀ henv₀ hS hC hR hRd₀ hci hadd
    | .example ci, .example _, _ => exact hC
    | .unsafeDef cis, _, _ => exact (hnu _ (.head _)).elim
    | .quot, .quot hqr hadd, hok =>
      rw [addQuot_eq] at hadd
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hadd
      have h1 := coherentOn_addConstList' L o quotConsts henv₀.constsClosed hC he
        (stagedOcc_quotConsts hqr) hok.consts
      exact coherentOn_addDefEq h1 (fun {_} hw hl ↦ (hok.rule hw hl).1)
        (fun {_} hw hl ↦ (hok.rule hw hl).2)
    | .induct D, .induct _ hadd, hok =>
      obtain ⟨e, he, rfl⟩ := addInduct'_iff.1 hadd
      have h1 := coherentOn_addConstList' L o D.allConsts henv₀.constsClosed hC he
        (hok.staged hadd) hok.consts
      exact coherentOn_addDefEqFold D.iotaRules h1 (fun df hdf ↦ hok.rules df hdf)

end Recursion


/-! ## 6. From the recursion to consistency

Composing with `FalseProp.lean`.  The only extra input at this step is the one
`falseProp_above_false`'s docstring names: a `κ` that really does carry a chain
of inaccessibles of *every* finite length, so that `Above M P` can be collapsed
to `P`. -/

section Consistency

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {env : VEnv} {κ : ℕ → V} {ls : List ℕ}

/-- **Consistency of one environment**, from the recursion.  `hκ` is the
threshold input: `Above M P` unwinds to `P` exactly when `κ` carries a chain of
the required length, and the required length is not known in advance, so what is
needed is *every* length. -/
theorem consistent_of (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (L : PropSplit env 0) (o : Name → List VLevel → V)
    {R : List VExpr → List VExpr → Prop} (hS : L.Stable) (hR : CtxInvariant L R)
    (hRd : ∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
      env.IsDefEq 0 Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ))
    {ds : List VDecl} (hwf : VEnv.WF' ds env) (hnu : ∀ d ∈ ds, d.noUnsafe)
    (hfits : OracleFits L κ ls o ds) : env.Consistent := by
  intro h
  obtain ⟨m, hm⟩ := exists_threshold_not_hasType_falseProp
    (M := (⟨κ, ls, cnstOf L κ ls o ds⟩ : ModelData V))
    VEnv.LE.rfl (VEnv.WF.ordered ⟨ds, hwf⟩) hS
    (coherentOn_cnstOf L o hS hR hRd ds hwf VEnv.LE.rfl hnu hfits) hR hRd h
  exact hm (hκ m)

/-- Every declaration of `leanPrelude` is `noUnsafe` — the prelude has axioms
but no `partial`/`unsafe` block. -/
theorem leanPrelude_noUnsafe : ∀ d ∈ leanPrelude, d.noUnsafe := by
  intro d hd
  simp only [leanPrelude, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

/-- **`VEnv.LeanWF` supplies `noUnsafe` for the whole list**, prelude included.
This is what lets the recursion's `.unsafeDef` case be *refuted* rather than
assumed away: the user part is `isPure` and the prelude part is checked above. -/
theorem noUnsafe_of_leanWF {env : VEnv} (h : env.LeanWF) :
    ∃ ds, VEnv.WF' ds env ∧ ∀ d ∈ ds, d.noUnsafe := by
  obtain ⟨ds, hwf, hpure⟩ := h
  refine ⟨_, hwf, fun d hd ↦ ?_⟩
  rcases List.mem_append.1 hd with hd | hd
  · exact VDecl.isPure.noUnsafe (hpure d hd)
  · exact leanPrelude_noUnsafe d (List.mem_reverse.1 hd)

/-- **The model-side data the recursion needs at one environment.**

Three unrelated things are bundled here because `L` and `o` have to be chosen
together, and it is worth being explicit about which is which:

1. `L : PropSplit env 0` with `L.Stable`, and `R` with `CtxInvariant L R` — the
   proof-split input.  `docs/model-interface.md`'s standing label applies:
   **nothing in the tree exhibits a `PropSplit`**.  `PropSplitAudit.exists_propSplit`
   reduces it to `VEnv.PropUniq` and `VEnv.PropTypeAgree`, both open, and
   `L.Stable` to `PropDescend`.
2. `OracleFits`' `.axiom` and `.quot` clauses — suppliable from the tree
   (`PreludeSpec.lean`, `QuotInterp.lean`) once `o` is *defined* at those names.
3. `OracleFits`' `.induct` clause — `InductOracleOK`, **the residual**. -/
def ModelFits (κ : ℕ → V) (env : VEnv) (ds : List VDecl) : Prop :=
  ∃ (ls : List ℕ) (L : PropSplit env 0) (o : Name → List VLevel → V)
      (R : List VExpr → List VExpr → Prop),
    L.Stable ∧ CtxInvariant L R ∧
    (∀ {Γ : List VExpr} {A A' : VExpr} {u : VLevel},
      env.IsDefEq 0 Γ A A' (.sort u) → R (A' :: Γ) (A :: Γ)) ∧
    OracleFits L κ ls o ds

/-- **`leanTTConsistent` from one model.**  Everything on the declaration-list
side is discharged; what remains as a hypothesis is `ModelFits` (per
environment) and `hκ` (once). -/
theorem leanTTConsistent_of (κ : ℕ → V) (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (H : ∀ (env : VEnv) (ds : List VDecl), VEnv.WF' ds env → (∀ d ∈ ds, d.noUnsafe) →
      ModelFits κ env ds) :
    leanTTConsistent := by
  intro env hlw
  obtain ⟨ds, hwf, hnu⟩ := noUnsafe_of_leanWF hlw
  obtain ⟨ls, L, o, R, hS, hR, hRd, hfits⟩ := H env ds hwf hnu
  exact consistent_of hκ L o hS hR hRd hwf hnu hfits

end Consistency

/-! ## 7. The reduction, assembled — and exactly what it is not

Two inputs stand between §6 and H2, and they are *separate* from the residual. -/

/-- **Input A — model existence.**  From consistency of `𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰`, anything
provable in every `SetStructure` model of `𝗭𝗙𝗖` carrying an inaccessible chain of
every finite length.

Stated as an elimination principle over an arbitrary `P` so that no `Type` has to
be bundled into a `Prop`.  Foundation supplies the two halves separately and
neither is applied here:

* `LO.FirstOrder.small_satisfiable_of_consistent` plus
  `LO.FirstOrder.SetTheory.QuotNormalize`/`standardStructure` turn `Consistent`
  into a `[SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰]`;
* `Inaccessible.lean`'s `exists_inaccessibleChain` gives, for each `n`, *some* `κ`
  with `IsInaccessibleChain n κ` — **one `κ` per `n`**.  The `∀ m` here needs a
  single `κ` good for all `m` at once (e.g. one enumerating the least
  inaccessibles).  That reordering is a real gap, not bookkeeping; see the report
  in `docs/soundness-ledger.md`. -/
def InaccModelInput : Prop :=
  ∀ P : Prop, (∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
      [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] (κ : ℕ → V), (∀ m : ℕ, IsInaccessibleChain m κ) → P) →
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → P

/-- **Input B — the per-environment model data**, i.e. `ModelFits` uniformly.
Contains the residual (`InductOracleOK`) *and* the proof-split input; see
`ModelFits`. -/
def ModelFitsInput : Prop :=
  ∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
    (κ : ℕ → V), (∀ m : ℕ, IsInaccessibleChain m κ) →
    ∀ (env : VEnv) (ds : List VDecl), VEnv.WF' ds env → (∀ d ∈ ds, d.noUnsafe) →
      ModelFits κ env ds

/-- **H2, reduced.**  `Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent` from
the two inputs above, with the whole declaration-list recursion discharged.

This is a *reduction*.  It is not a proof of H2, and `ModelFitsInput` is not the
`.induct` residual alone — it also carries the proof-split input, which is
independently open. -/
theorem upper_bound_of (hA : InaccModelInput) (hB : ModelFitsInput) :
    Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent := fun hc ↦
  hA leanTTConsistent
    (fun V _ _ _ _ κ hκ ↦ leanTTConsistent_of κ hκ (hB V κ hκ)) hc

/-! ## 8. Boundary control on the residual

`sortConv_encoding_vacuous` (`Theory/Typing/NormalEqStrengthen.lean`) is the model
for this: a reduction is only worth anything if the thing reduced to is neither
trivially true (the reduction says nothing) nor plainly false (the reduction is
to nonsense).  Both are checked. -/

section Control

variable {V : Type*} [SetStructure V] [Nonempty V]
variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖]
variable {envF : VEnv} {nv : ℕ} {κ : ℕ → V} {ls : List ℕ}

/-- **The residual is refutable**, so it is not trivially true and no
uniform proof of it can exist.  `OracleOK` at a constant whose declared type is
`∀ p : Prop, p` asks for an element of `⟦falseProp⟧ = ∅`.

This is the exact analogue, for the oracle, of `InterpSound.lean`'s observation
that `Coherent` is unprovable for arbitrary well-formed environments: `VDecl.WF`
asks that a declared type *be a type*, never that it be inhabited, so
inhabitation is genuinely extra information — which is why the residual is a
residual and not a lemma. -/
theorem not_oracleOK_falseProp (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (L : PropSplit envF nv) (o c : Name → List VLevel → V) (n : Name) :
    ¬ OracleOK L κ ls o c n ⟨0, falseProp⟩ := by
  intro h
  obtain ⟨m, hm⟩ := h.type (us := []) (by simp) rfl
  have := hm (hκ m)
  rw [show (VConstant.mk 0 falseProp).type.instL [] = falseProp from rfl,
    interp_falseProp] at this
  simp at this

/-- The same, transported to the residual itself: a block declaring a constant of
type `∀ p : Prop, p` has no `InductOracleOK`. -/
theorem not_inductOracleOK_falseProp (hκ : ∀ m : ℕ, IsInaccessibleChain m κ)
    (L : PropSplit envF nv) (o c : Name → List VLevel → V) {D : VInductDecl'} {n : Name}
    (hp : (n, ⟨0, falseProp⟩) ∈ D.allConsts) :
    ¬ InductOracleOK L κ ls o c D := fun h ↦
  not_oracleOK_falseProp (ls := ls) hκ L o c n (h.consts _ hp)

/-- **The residual is satisfiable**, so it is not plainly false.  A block with no
type formers declares nothing and has no ι-rules, so all three fields hold.

(Such a `D` is not `VInductDecl'.WF` — `types_ne` forbids it — which is the
point: `InductOracleOK` constrains only what `D` *declares*, so the residual has
no hidden inconsistency of its own.  The content is entirely in blocks that
declare something.) -/
theorem inductOracleOK_empty (L : PropSplit envF nv) (o c : Name → List VLevel → V) :
    InductOracleOK L κ ls o c
      { uvars := 0, params := [], lvl := .zero, types := [], isLE := false } :=
  ⟨fun _ ↦ trivial, fun _ h ↦ absurd h nofun, fun _ h ↦ absurd h nofun⟩

end Control

end Lean4Lean.SetModel
