import Lean4Lean.Verify.Inductive.RunIdentity
import Lean4Lean.Verify.SoundnessAssembly
import Lean4Lean.Verify.Soundness

/-!
# Where a closedness side condition on `addDecl.WF` ends up

`Verify/Inductive/RunIdentity.lean` §5 refutes `AddInductiveStepWF` and `AddInductiveRunRealises`
at a block whose constructor type carries a *loose* bound variable small enough to be captured
by a parameter binder (`LooseBVarWitness.fooBad`): the checker accepts, `Expr.abstract`
captures, the stored constructor type differs from the input, and `TrIndDecl`/`TrIndDeclN`
require the *input* to be closed.  §4/§7 there repair the statements with the premise
`BlockClosed types`.

`docs/vacuity-ledger.md` row 108d rules that `addDecl.WF`/`AddDeclPost` will carry that
condition, and leaves **unmeasured** whether it propagates to `Lean4Lean.kernel_sound`, whose
statement is frozen.  This file measures that, and prices the alternative the ruling rejected.

## The measurement, in one line

**As a premise the condition reaches `kernel_sound`'s statement; as a weakening of the
inductive step's postcondition it does not; and a one-line implementation guard removes it
entirely with no statement change anywhere.**

The three sections that establish this:

* §2 — the lift.  `AddDeclWFClosed` (the step with the premise) folds only under
  `∀ d ∈ ds, DeclClosed d` (`foldlM_addDecl_WF_closed`).  Chained through
  `foldAddDecl_tr_closed` and `not_leanTTConsistent_of_kernel_proves_false_closed` the
  hypothesis arrives at the frozen statement's own `ds` (`kernel_sound_of_closed`), reduced by
  §1's `stdPrelude_closed` from `pre ++ ds` to `ds`.  It cannot be discharged there:
  `not_closedFromAccept` refutes recovering it from acceptance, and `hax`/`hfalse` say nothing
  about bound variables.

  Whether the fold *carries* it as a hypothesis or as an antecedent inside its postcondition is
  immaterial — closedness of `dₙ` is a property of `dₙ` alone, so no fold-level invariant can
  produce it — and only two places can discharge it: `kernel_sound`'s statement, or the
  inductive step itself.  §3 and §4 are those two.

* §3 — the absorber.  The *only* thing the fold consumes from the inductive step is the
  `TrEnv'` step, and that factors through `InductStepOut`, which does not mention the input
  block at all (`InductStepNested.out`, `InductStepOut.trEnv'`).  So the `TrIndDeclN` conjunct
  of `AddInductPost` — the one and only conjunct the refutation attacks
  (`not_inductStepNested_of_looseBVar` goes through `trExprS_looseBVarRange_nil`) — is dead
  weight for everything downstream of `addDecl.WF`.  `trEnv'_survives_looseBVar` states both
  halves at once: `InductStepNested … [fooBad] …` is false while the `TrEnv'` step follows from
  the *stored* block.

  The cost of §3, named: `AddInductPost`'s `types` argument is what makes the specification say
  *the environment realises a translation of the declaration you submitted*.  Reparameterising it
  by the stored block weakens that to *of some declaration* — correct at `fooBad`, where the
  checker really did store something else, but a loss at every closed block, which is all of
  them.  The guard of §4 is the only option that keeps the strong input-facing specification
  **and** costs no premise, because the inputs at which the two differ are exactly the ones it
  rejects.

* §4 — the price of rejecting.  `Except.WF x Q = ∀ a, x = .ok a → Q a`, so a rejection
  satisfies every postcondition.  Hence `addInductiveStepWF_of_reject`: if
  `Environment.addInductive` rejected non-closed blocks, the **unrestricted**
  `AddInductiveStepWF` would follow from `AddInductiveStepWFClosed` — no premise on
  `addDecl.WF`, no premise on `AddDeclPost`, nothing to lift, nothing to ask a human about.

## What is measured and what is asserted

Everything named above is a theorem.  Three things are *not*:

1. that `Environment.addInductive` accepts `fooBad` — an `#eval` (§5), for the reason
   `not_addInductiveStepWF`'s docstring gives: `Expr.abstract` is `opaque`, so this cannot be a
   kernel proof.  `not_closedFromAccept` therefore takes acceptance as a hypothesis.
2. that `InductStepOut` holds at `fooBad`'s stored block.  §3 proves only that
   `InductStepOut` is *not refuted* by the witness (it does not mention the block) and that it
   is satisfiable (`inductStepOut_sat`, from `inductStepNested_wit_closed`).  Whether the
   checker-side proof can build the `D` is the same open work as `AddInductiveStepWFClosed`.
3. that adding the guard costs nothing in practice.  §5's third `#eval` scans every
   `.inductInfo`/`.ctorInfo` in the running environment for a loose bvar; it is evidence, not a
   proof, and it says nothing about inputs the Kernel Arena feeds that no elaborator produced.

## `BlockClosed` covers constructor types only — and that turns out to be right

`TrIndDeclN.trType` demands `TrIndType env Us t T`, i.e. `TrExprS env Us [] t.type T.type`,
which forces the *member's own* type closed too, and the pre-`run` guard loop does not check it
(§5's second `#eval` confirms `checkNoMVarNoFVar` accepts an open member type).  So
`BlockClosedFull` (§1) is the conservative premise, and it is what `DeclClosed` uses here.

But the same `#eval` shows the member-type half is **not reachable**, and the mechanism is the
asymmetry that makes the constructor case interesting in the first place: `run.loop` round-trips
only the *constructor* types through `withParams`/`mkForall` (`run_loop_id` rebuilds
`{ t with ctors := … }`), so a loose bvar in a member's own type is never captured — it survives
to `AddInductive.run`'s type checker, which rejects with "does not support loose bound
variables".  Verified at `Bar : ∀ (α : Type) (x : #1), Type`, `np = 1`, the exact analogue of
`fooBad`.

So on today's evidence `BlockClosedFull`'s first conjunct is *dischargeable from the checker's
success* while the second is not — one witness, so this is a bound rather than a proof.  Nothing
below turns on it: the two conjuncts propagate identically, and every verdict in §2–§4 is stated
for `DeclClosed`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-! ## 1. The condition, at declaration and at list level -/

/-- `BlockClosed` extended to the members' own types, which `TrIndDeclN.trType` also forces
closed (see the module docstring's correction). -/
def BlockClosedFull (types : List InductiveType) : Prop :=
  (∀ t ∈ types, t.type.looseBVarRange' = 0) ∧ BlockClosed types

theorem BlockClosedFull.toBlockClosed {types} (h : BlockClosedFull types) : BlockClosed types :=
  h.2

/-- The closedness condition, lifted from a block to a declaration.  Only `.inductDecl` is
constrained: the other six branches of `addDecl.WF` are proved today with no closedness
premise at all. -/
def DeclClosed : Declaration → Prop
  | .inductDecl _ _ types _ => BlockClosedFull types
  | _ => True

theorem declClosed_of_not_inductDecl {d : Declaration}
    (h : ∀ lp np types iu, d ≠ .inductDecl lp np types iu) : DeclClosed d := by
  cases d with
  | inductDecl lp np types iu => exact absurd rfl (h lp np types iu)
  | _ => trivial

/-! ### The prelude is closed

`stdPrelude` is seven concrete `Declaration` literals in the frozen `Verify/Soundness.lean`,
three of which are `.inductDecl`s.  All three are closed, by `decide`. -/

/-- `BlockClosedFull` at a singleton block, by `decide` on the member. -/
theorem blockClosedFull_singleton {t : InductiveType}
    (h1 : t.type.looseBVarRange' = 0) (h2 : ∀ c ∈ t.ctors, c.type.looseBVarRange' = 0) :
    BlockClosedFull [t] := by
  refine ⟨?_, ?_⟩ <;> intro s hs <;> rw [List.mem_singleton] at hs <;> subst hs
  · exact h1
  · exact h2

theorem blockClosedFull_eqDecl : DeclClosed eqDecl :=
  blockClosedFull_singleton (by decide) (by decide)

theorem blockClosedFull_iffDecl : DeclClosed iffDecl :=
  blockClosedFull_singleton (by decide) (by decide)

theorem blockClosedFull_nonemptyDecl : DeclClosed nonemptyDecl :=
  blockClosedFull_singleton (by decide) (by decide)

/-- **The prelude satisfies the condition.**  So the list-level hypothesis reduces from
`pre ++ ds` to `ds`, and what remains is a constraint on the theorem's own universally
quantified argument. -/
theorem stdPrelude_closed : ∀ d ∈ stdPrelude, DeclClosed d := by
  intro d hd
  simp only [stdPrelude, List.mem_cons, List.not_mem_nil, or_false] at hd
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl := hd
  · exact blockClosedFull_eqDecl
  · exact blockClosedFull_iffDecl
  · trivial
  · trivial
  · trivial
  · exact blockClosedFull_nonemptyDecl
  · trivial

theorem declClosed_append {pre ds : List Declaration}
    (hpre : ∀ d ∈ pre, DeclClosed d) (hds : ∀ d ∈ ds, DeclClosed d) :
    ∀ d ∈ pre ++ ds, DeclClosed d := by
  intro d hd
  rcases List.mem_append.1 hd with h | h
  · exact hpre d h
  · exact hds d h

/-! ## 2. The lift: the premise reaches `kernel_sound`'s own `ds`

Each link below is `Verify/Bridge.lean`'s, with the closedness premise added and nothing else
changed, so the diff between the two chains *is* the propagation.  All four are proved. -/

/-- `Bridge.AddDeclWF` with the premise. -/
def AddDeclWFClosed (fuel : FuelConfig) : Prop :=
  ∀ {env : Kernel.Environment} {ves : VEnvs}, ves.WF env → ∀ decl : Declaration,
    DeclClosed decl →
    (addDecl env decl (check := true) (fuel := fuel)).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety

/-- **Link 1 → 2: the premise must be lifted to the list.**  `foldlM` applies the step at every
`d ∈ ds`, and there is nothing in scope at step *n* from which `DeclClosed dₙ` could be
recovered, so the hypothesis is `∀ d ∈ ds, DeclClosed d`.  Verdict (b). -/
theorem foldlM_addDecl_WF_closed {fuel : FuelConfig} (H : AddDeclWFClosed fuel) :
    ∀ (ds : List Declaration), (∀ d ∈ ds, DeclClosed d) →
      ∀ {env : Kernel.Environment} {ves : VEnvs}, ves.WF env →
      (ds.foldlM (fun env d => addDecl env d (check := true) (fuel := fuel)) env).WF
        fun env' => ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
  | [], _, _, _, wf => Except.WF.pure ⟨_, wf, fun _ => VEnv.LE.rfl⟩
  | d :: ds, hcl, _, _, wf => by
    refine Except.WF.bind (H wf d (hcl d List.mem_cons_self)) fun env₁ ⟨ves₁, wf₁, le₁⟩ => ?_
    exact (foldlM_addDecl_WF_closed H ds
        (fun x hx => hcl x (List.mem_cons_of_mem _ hx)) wf₁).mono
      fun _ ⟨ves₂, wf₂, le₂⟩ => ⟨ves₂, wf₂, fun safety => VEnv.LE.trans (le₁ safety) (le₂ safety)⟩

/-- **Links 2 → 5: absorbed, all four.**  `foldAddDecl_WF'`, `foldAddDecl_WF` and
`foldAddDecl_tr` add nothing that could discharge the hypothesis, and nothing that could
consume it either; it passes through unchanged. -/
theorem foldAddDecl_tr_closed {fuel : FuelConfig} (H : AddDeclWFClosed fuel)
    {ds : List Declaration} (hcl : ∀ d ∈ ds, DeclClosed d)
    {env : Kernel.Environment} (hok : Bridge.foldAddDecl fuel ds = .ok env) :
    ∃ venv : VEnv, TrEnv .safe env venv ∧ venv.WF := by
  obtain ⟨_, wf₀⟩ := Bridge.hasEmptyModel
  obtain ⟨ves, wf, -⟩ := foldlM_addDecl_WF_closed H ds hcl wf₀ _ hok
  exact ⟨ves.venv .safe, wf.tr, wf.tr.wf⟩

/-- **Link 6: absorbed.**  `PreludeBridge`, `hasType_falseProp` and the contraposition speak
only about the output environment and its model, so the hypothesis is untouched — and still
present. -/
theorem not_leanTTConsistent_of_kernel_proves_false_closed {fuel : FuelConfig}
    (H : AddDeclWFClosed fuel)
    {pre : List Declaration} (hpre : Bridge.PreludeBridge pre)
    (ds : List Declaration) (env : Kernel.Environment)
    (hcl : ∀ d ∈ pre ++ ds, DeclClosed d)
    (hok : Bridge.foldAddDecl fuel (pre ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Bridge.Declaration.IsAxiomFree d)
    (hfalse : Bridge.ContainsSafeProofOfFalse env) : ¬ leanTTConsistent := by
  obtain ⟨venv, htr, hwf⟩ := foldAddDecl_tr_closed H hcl hok
  exact fun hcon => hcon venv (hpre ds fuel env venv hok hax htr)
    (Bridge.hasType_falseProp htr hwf hfalse)

/-- **Links 7–8, and the answer.**  `kernel_sound_of` / `kernel_sound_of_equiconsistent` /
`kernel_sound` add no hypothesis that could discharge closedness, and at the frozen call site
`pre := stdPrelude`, whose closedness §1 proves.  What survives is exactly
`∀ d ∈ ds, DeclClosed d` on the theorem's own argument.

**This statement is what `kernel_sound` would have to say** if the condition is carried as a
premise.  Compare the frozen statement, which has `hok`, `hax`, `hfalse` and nothing else. -/
theorem kernel_sound_of_closed {fuel : FuelConfig} (H : AddDeclWFClosed fuel)
    (hpre : Bridge.PreludeBridge stdPrelude)
    (hub : Entailment.Consistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 → leanTTConsistent)
    (ds : List Declaration) (env : Kernel.Environment)
    (hcl : ∀ d ∈ ds, DeclClosed d)
    (hok : Bridge.foldAddDecl fuel (stdPrelude ++ ds) = .ok env)
    (hax : ∀ d ∈ ds, Bridge.Declaration.IsAxiomFree d)
    (hfalse : Bridge.ContainsSafeProofOfFalse env) :
    Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰 :=
  inconsistent_of_upper_bound hub
    (not_leanTTConsistent_of_kernel_proves_false_closed H hpre ds env
      (declClosed_append stdPrelude_closed hcl) hok hax hfalse)

/-! ### …and it cannot be discharged from acceptance

The one candidate for discharging `∀ d ∈ ds, DeclClosed d` inside the theorem is `hok` itself.
It fails, and this is the same refutation as `RunIdentity` §5 read at the top of the chain. -/

/-- The witness, as a `Declaration`: `LooseBVarWitness.fooBad` at `np = 1`. -/
def badInductDecl : Declaration := .inductDecl [] 1 [LooseBVarWitness.fooBad] false

theorem not_declClosed_badInductDecl : ¬ DeclClosed badInductDecl := fun h =>
  LooseBVarWitness.fooBad_not_closed h.2

/-- "Acceptance implies closedness" — the only route to discharging §2's hypothesis inside
`kernel_sound`. -/
def ClosedFromAccept : Prop :=
  ∀ (fuel : FuelConfig) (ds : List Declaration) (env : Kernel.Environment),
    Bridge.foldAddDecl fuel ds = .ok env → ∀ d ∈ ds, DeclClosed d

/-- **Refuted**, at any environment where the checker accepts the loose-bvar block.  §5's first
`#eval` exhibits `hok`, both bare and after `stdPrelude` — i.e. at exactly the shape
`kernel_sound` quantifies over.  Acceptance is an executed observation and provably cannot be a
kernel proof (`not_addInductiveStepWF`'s docstring), so it is a hypothesis here. -/
theorem not_closedFromAccept {fuel : FuelConfig} {env : Kernel.Environment}
    (hok : Bridge.foldAddDecl fuel [badInductDecl] = .ok env) : ¬ ClosedFromAccept := fun H =>
  not_declClosed_badInductDecl (H fuel _ env hok badInductDecl List.mem_cons_self)

/-- The same at the prelude-prefixed list, which is the literal shape of `kernel_sound`'s
`hok`. -/
theorem not_closedFromAccept_prelude {fuel : FuelConfig} {env : Kernel.Environment}
    (hok : Bridge.foldAddDecl fuel (stdPrelude ++ [badInductDecl]) = .ok env) :
    ¬ ClosedFromAccept := fun H =>
  not_declClosed_badInductDecl
    (H fuel _ env hok badInductDecl (List.mem_append.2 (.inr List.mem_cons_self)))

/-! ## 3. The absorber: what the fold actually consumes

`AddInductPost` bundles four things.  The refutation attacks exactly one of them — the
`TrIndDeclN` conjunct, via `trExprS_looseBVarRange_nil`.  This section shows that conjunct is
not what anything downstream of `addDecl.WF` uses. -/

/-- `InductStepNested` with the input-facing conjunct dropped.  Note the signature: no `types`,
no `lp`, no `np`, no `numNested` — the predicate **cannot** be refuted by a fact about the
input block, because it does not mention one. -/
def InductStepOut (m m' : ConstMap) (venv venv' : VEnv) : Prop :=
  ∃ (D : VInductDecl') (K : List Name) (R : VIndRestore),
    (∃ et, venv.addIndTypes D = some et) ∧ D.WF venv ∧ AddInductStagesR m venv D K R m' venv'

theorem InductStepNested.out {m m' : ConstMap} {venv venv' : VEnv} {lp np types nn}
    (h : InductStepNested m m' venv venv' lp np types nn) : InductStepOut m m' venv venv' :=
  let ⟨D, K, R, _, het, hwfD, hadd⟩ := h; ⟨D, K, R, het, hwfD, hadd⟩

/-- **The `TrEnv'` step needs nothing about the input block.**  Same proof as
`InductStepNested.trEnv'`, which already discards its `TrIndDeclN` argument; this states that
fact where it can be quoted. -/
theorem InductStepOut.trEnv' {safety : DefinitionSafety} {m m' : ConstMap}
    {venv venv' : VEnv} {Q : Bool} (hflip : AddInductFlip)
    (h : InductStepOut m m' venv venv') (H : TrEnv' safety m Q venv) :
    TrEnv' safety m' Q venv' :=
  let ⟨_, _, _, _, hwfD, hadd⟩ := h; .induct hwfD (hflip hadd) H

theorem InductStepOut.le {m m' : ConstMap} {venv venv' : VEnv}
    (h : InductStepOut m m' venv venv') : venv ≤ venv' :=
  let ⟨_, _, _, _, _, hadd⟩ := h; hadd.le

theorem InductStepOut.map_wf {m m' : ConstMap} {venv venv' : VEnv}
    (h : InductStepOut m m' venv venv') (hwf : m.WF) : m'.WF :=
  let ⟨_, _, _, _, _, hadd⟩ := h; hadd.map_wf hwf

/-- **Non-vacuity** (instrument 7): `InductStepOut` has a model, at the same closed environment
`inductStepNested_wit_closed` uses. -/
theorem inductStepOut_sat {env₂ : VEnv}
    (h : VEnv.empty.addInduct' InductiveDeclExamples.pfnDecl = some env₂)
    {m : ConstMap} (hwf : m.WF) (hfr : ∀ n, m.find? n = none) :
    ∃ m' env', InductStepOut m m' env₂ env' := by
  obtain ⟨m', env', hstep, -⟩ := NestedWit.inductStepNested_wit_closed h hwf hfr
  exact ⟨m', env', hstep.out⟩

/-- **The pivot, both halves in one statement.**  At the loose-bvar witness the input-facing
statement is false for every `numNested`, and yet the `TrEnv'` step — the only thing
`Verify/Bridge.lean`'s chain consumes from the inductive branch — follows from the *stored*
block, which is closed (`fooGood_closed`).

So a closedness premise is **not forced** by anything below `addDecl.WF`.  It is forced only by
`AddInductPost`'s own choice to relate the model to the *input* block. -/
theorem trEnv'_survives_looseBVar {safety : DefinitionSafety} {m m' : ConstMap}
    {venv venv' : VEnv} {Q : Bool} {nn nn' : Nat} (hflip : AddInductFlip)
    (hstored : InductStepNested m m' venv venv' [] 1 [LooseBVarWitness.fooGood] nn)
    (H : TrEnv' safety m Q venv) :
    TrEnv' safety m' Q venv' ∧
      ¬ InductStepNested m m' venv venv' [] 1 [LooseBVarWitness.fooBad] nn' :=
  ⟨hstored.out.trEnv' hflip H,
   not_inductStepNested_of_looseBVar (types := [LooseBVarWitness.fooBad])
     LooseBVarWitness.fooBad_zero LooseBVarWitness.fooBad_ctor_zero
     LooseBVarWitness.fooBadCtor_looseBVar⟩

/-! ## 4. The price of the alternative the ruling rejected

`Except.WF x Q` is `∀ a, x = .ok a → Q a`, so an `.error` satisfies every postcondition.  That
makes the arithmetic of the rejecting alternative trivial and worth stating: the guard is not a
weakening of any statement, it is a strengthening of the *implementation* that makes the
unrestricted statement true. -/

theorem Except.WF_of_no_ok {ε α} {x : Except ε α} {Q : α → Prop}
    (h : ∀ a, x ≠ .ok a) : x.WF Q := fun a ha => absurd ha (h a)

/-- The guard, as a statement about the implementation: `Environment.addInductive` rejects a
block that is not closed.  This is what one line in `Lean4Lean/Inductive/Add.lean`'s pre-`run`
guard loop would buy, provable by the pattern of `guardLoop_blockNoFVar`. -/
def RejectsNonClosed : Prop :=
  ∀ (env : Environment) (lp : List Name) (np : Nat) (types : List InductiveType)
    (ap : Bool) (fuel : FuelConfig), ¬ BlockClosed types →
    ∀ env', Environment.addInductive env lp np types false ap fuel ≠ .ok env'

/-- **The priced comparison.**  With the guard, the **unrestricted** `AddInductiveStepWF` — the
statement `docs/vacuity-ledger.md` row 108 refutes, and the statement `addDecl.WF_honest`,
`AddDeclPost`, `Bridge.AddDeclWF`, the fold and `kernel_sound` all consume unchanged — follows
from `AddInductiveStepWFClosed`.

Nothing in §2 happens: no premise on `addDecl.WF`, no `∀ d ∈ ds, DeclClosed d`, no frozen-file
question. -/
theorem addInductiveStepWF_of_reject (Hcl : AddInductiveStepWFClosed) (Hrej : RejectsNonClosed) :
    AddInductiveStepWF := by
  intro env ves wf lp np types ap fuel
  by_cases hcl : BlockClosed types
  · exact Hcl wf lp np types ap fuel hcl
  · exact Except.WF_of_no_ok (Hrej env lp np types ap fuel hcl)

/-- And then `addDecl.WF_honest` is available at its published statement, with no closedness
anywhere in sight. -/
theorem addDecl_WF_honest_of_reject (Hcl : AddInductiveStepWFClosed) (Hrej : RejectsNonClosed)
    {env : Environment} {ves : VEnvs} (wf : ves.WF env) (decl : Declaration)
    (fuel : FuelConfig := {}) :
    (Lean4Lean.addDecl env decl (check := true) (fuel := fuel)).WF (AddDeclPost env decl ves) :=
  addDecl.WF_honest (addInductiveStepWF_of_reject Hcl Hrej) wf decl fuel

/-! ## 5. The instruments

Three `#eval`s.  All three `throwError` when the fact they report stops holding.  None is a
kernel proof. -/

/- **Acceptance, at the shape `kernel_sound` quantifies over.**  `hok` of
`not_closedFromAccept` and `not_closedFromAccept_prelude`: `Lean4Lean.addDecl` accepts the
loose-bvar block from the empty environment *and* after `stdPrelude`, and stores the captured
constructor type in both cases. -/
#eval show Lean.CoreM Unit from do
  let check (label : String) (ds : List Declaration) : Lean.CoreM Unit := do
    match Bridge.foldAddDecl {} ds with
    | .error e => throwError "accept/{label}: REJECTED ({e.toMessageData {}}) -- \
        not_closedFromAccept has no witness at this list and must be withdrawn"
    | .ok env =>
      unless (env.find? LooseBVarWitness.fooGoodCtor.name).map (·.type)
          == some LooseBVarWitness.fooGoodCtor.type do
        throwError "accept/{label}: the stored constructor type is not the captured one"
  check "bare" [badInductDecl]
  check "prelude" (stdPrelude ++ [badInductDecl])
  logInfo "accept: addDecl accepts the loose-bvar block bare AND after stdPrelude, storing the \
    captured constructor type -- so `hok` cannot yield `DeclClosed` ✓"

/- **`BlockClosed` is not the whole condition.**  `TrIndDeclN.trType` forces the *member's own*
type closed too.  This checks that nothing in the pre-`run` guard loop rejects a member whose
own type carries a loose bvar, i.e. that `BlockClosedFull`'s first conjunct is as unsupplied as
its second. -/
#eval show Lean.CoreM Unit from do
  let kenv := Kernel.Environment.empty `main
  let openMember : InductiveType :=
    { name := `Lean4Lean.ClosednessProp.Bar
      type := .forallE `α (.sort (.succ .zero)) (.bvar 1) .default
      ctors := [] }
  unless openMember.type.looseBVarRange == 1 do
    throwError "member: the probe member's own type is closed after all"
  match kenv.checkNoMVarNoFVar openMember.name openMember.type with
  | .error _ =>
    throwError "member: the pre-run guard rejects an open member type -- \
      BlockClosedFull's first conjunct IS supplied and the docstring's correction is wrong"
  | .ok _ =>
    match checkNoNestedAux openMember.name openMember.type with
    | .error (_ : Kernel.Exception) =>
      throwError "member: the reserved-prefix guard rejects it -- unexpected"
    | .ok _ => pure ()
  -- …and the whole of `addInductive` accepts one, with the loose bvar captured by the
  -- parameter binder exactly as in `fooBad`: `Bar : ∀ (α : Type) (x : #1), Type` at `np = 1`
  -- is stored as `Bar : ∀ (α : Type) (x : α), Type`.
  let barOpen : InductiveType :=
    { name := `Lean4Lean.ClosednessProp.Bar
      type := .forallE `α (.sort (.succ .zero))
        (.forallE `x (.bvar 1) (.sort (.succ .zero)) .default) .default
      ctors := [{ name := `Lean4Lean.ClosednessProp.Bar.mk
                  type := .forallE `α (.sort (.succ .zero))
                    (.forallE `x (.bvar 0)
                      (.app (.app (.const `Lean4Lean.ClosednessProp.Bar []) (.bvar 1))
                        (.bvar 0)) .default) .default }] }
  let barClosedTy : Expr := .forallE `α (.sort (.succ .zero))
    (.forallE `x (.bvar 0) (.sort (.succ .zero)) .default) .default
  unless barOpen.type.looseBVarRange == 1 do
    throwError "member: the probe block's member type is closed after all"
  match Environment.addInductive kenv [] 1 [barOpen] false false with
  | .error e =>
    logInfo m!"member: the pre-run guard loop accepts a member whose OWN type has a loose \
      bvar, so BlockClosedFull's first conjunct is unsupplied before `run`; the full \
      `addInductive` nevertheless rejects this probe ({e.toMessageData {}}), so the member-type \
      half is NOT known to be reachable ⚠"
  | .ok env' =>
    unless (env'.find? barOpen.name).map (·.type) == some barClosedTy do
      throwError "member: accepted, but the stored member type is not the captured one"
    logInfo "member: `addInductive` ACCEPTS a block whose MEMBER's own type carries a loose \
      bvar and stores the captured type -- so BlockClosedFull's first conjunct is load-bearing \
      for truth, exactly as BlockClosed is ✓"

/- **What the guard of §4 would cost, empirically.**  Every `.inductInfo` and `.ctorInfo` in
the running environment is scanned for a loose bvar in its stored type.  A nonzero count would
mean the guard rejects declarations the toolchain itself produces; zero is evidence that it
rejects nothing an elaborator emits.  It is *not* evidence about the Kernel Arena's inputs. -/
#eval show Lean.CoreM Unit from do
  let env ← getEnv
  let mut inds := 0
  let mut ctors := 0
  let mut openInds : List Name := []
  let mut openCtors : List Name := []
  for (n, ci) in env.constants.toList do
    match ci with
    | .inductInfo _ =>
      inds := inds + 1
      unless ci.type.looseBVarRange == 0 do openInds := n :: openInds
    | .ctorInfo _ =>
      ctors := ctors + 1
      unless ci.type.looseBVarRange == 0 do openCtors := n :: openCtors
    | _ => pure ()
  if openInds.isEmpty && openCtors.isEmpty then
    logInfo s!"guard cost: {inds} inductives and {ctors} constructors in the running \
      environment, ZERO with a loose bvar in the stored type -- the §4 guard rejects nothing \
      this toolchain produced ✓"
  else
    throwError "guard cost: loose bvars found -- inds {openInds}, ctors {openCtors}"

/-! ## 6. The verdict, and the frozen edit that is *not* made here

### Link-by-link

| link | verdict for a closedness premise on `addDecl.WF` |
| --- | --- |
| `Bridge.addDeclWF` | (b) — the premise is the step's own |
| `foldlM_addDecl_WF` | **(b) lifted to the list**: `∀ d ∈ ds, DeclClosed d` (`foldlM_addDecl_WF_closed`) |
| `foldAddDecl_WF'` / `foldAddDecl_WF` / `foldAddDecl_tr` | (a) absorbed as *carried*, not discharged |
| `not_leanTTConsistent_of_kernel_proves_false` | (a) absorbed as carried |
| `kernel_sound_of` / `kernel_sound_of_equiconsistent` | (a) absorbed as carried; `pre := stdPrelude` is discharged by `stdPrelude_closed` |
| `kernel_sound` | **reaches the statement** — `∀ d ∈ ds, DeclClosed d` survives, and `not_closedFromAccept` refutes discharging it from `hok` |

### The frozen edit, stated and not made

`Verify/Soundness.lean` cannot name `DeclClosed` (this module imports it, so the dependency runs
the wrong way), so the premise route needs a **definition** as well as a hypothesis there, and it
must be phrased in upstream vocabulary — `Expr.looseBVarRange`, whose bridge to
`looseBVarRange'` is `Expr.looseBVarRange_eq`'s `BVarBounded` side condition:

    def Declaration.IsClosed : Declaration → Prop
      | .inductDecl _ _ types _ =>
        (∀ t ∈ types, t.type.looseBVarRange = 0) ∧
        (∀ t ∈ types, ∀ c ∈ t.ctors, c.type.looseBVarRange = 0)
      | _ => True

    theorem kernel_sound (ds : List Declaration) (fuel : FuelConfig)
        (env : Kernel.Environment)
        (hcl : ∀ d ∈ ds, Declaration.IsClosed d)          -- ADDED
        (hok : foldAddDecl fuel (stdPrelude ++ ds) = .ok env)
        (hax : ∀ d ∈ ds, Declaration.IsAxiomFree d)
        (hfalse : ContainsSafeProofOfFalse env) :
        Entailment.Inconsistent 𝗭𝗙𝗖+𝗜𝗻𝗮𝗰𝗰

and `kernel_complete`'s conclusion would gain the matching conjunct, or tightness is lost.  That
is a narrowing of the frozen statement, which is exactly what `CLAUDE.md` and the brief forbid,
so **it is written here and nowhere else**, and it is the human's call.

### Against which: the guard

`addInductiveStepWF_of_reject` needs **no** statement change at all — not in `addDecl.WF`, not in
`AddDeclPost`, not in `Bridge.AddDeclWF`, not in the fold, not in `kernel_sound`.  Measured price:

* one pre-`run` check in `Environment.addInductive`'s existing guard loop, and a lemma of the
  shape `guardLoop_blockNoFVar` to expose it.  No new axiom: `Lean.Expr.hasLooseBVar_eq` is
  already frozen and already used, and a pure recursive check needs nothing at all;
* one `divergences.md` entry — a **restrictive** divergence, since C++ accepts and silently
  reinterprets (`docs/vacuity-ledger.md` row 108c), which is also the `bugs-found.md` candidate
  that row already left open;
* one Arena re-run.  Nothing in the suite is at risk on today's evidence: all 43 inductive blocks
  in the arena's ten `.ndjson` tests have closed member and constructor types, and §5's third
  `#eval` finds 0 of 10902 inductive/constructor types in the running environment with a loose
  bvar.
-/

end Lean4Lean
