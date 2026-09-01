import Lean4Lean.Verify.Inductive.Add
import Lean4Lean.Verify.Inductive.AddDeclWF

/-!
# Row 113e: the bookkeeping half of `AddInductStages`' stages 1 and 2

`docs/vacuity-ledger.md` row 113e: the nearest closable piece at the `AddInductStages` node is
the `M.WF` pair for `declareInductiveTypes` and `declareConstructors` — the two functions that
*build* the constant map `AddInductStages`' first two folds are about.  Each gives, per member,
`c.env.find? name = none` before and `env'.find? name = some (.inductInfo ⟨…⟩)` /
`some (.ctorInfo ⟨…⟩)` after, with the record's fields spelled out; §4 turns those into
`IndShapeOf D id` and `CtorShape` given the two numeric facts that relate the checked block to
the abstract declaration.

**What this unblocks: nothing, by itself.**  `AddInductStages`' `cons` step also carries
`TrConstant .safe env ci ci'`, whose third conjunct is `TrExprS env ci.levelParams [] ci.type
ci'.type` — a statement about the *type checker's* environment that none of this reaches.  Row
113e says so and this file repeats it: what is closed here is the map bookkeeping, and the
shape predicates, and nothing else.

**Why it is worth having anyway.**  It reaches **no frozen axiom and no `sorryAx`** (§5's
`#print axioms` list), because it never touches the type checker: `checkName.WF`
(`Verify/Environment/Checker.lean`) and the `SMap` insert lemmas are the whole toolkit.  Contrast
`AddInductive.M.WF.positivity_none` and `AddInductive.M.WF.field_step`
(`Verify/Inductive/Add.lean`), which carry `sorryAx`.

## Instrument 7, up front

Every statement below is an `Except.WF`/`M.WF`, so **a rejecting input satisfies it for free**
and all the content lives in the *succeeding* case.  §6 exhibits the succeeding case: the
`R10.Wit.U` block, on which `declareInductiveTypes` and `declareConstructors` both return `.ok`
and the postconditions are the three entries `R113a.realMap`
(`Verify/Inductive/StagesFiring.lean`) is built from.  A `#eval` that only `logInfo`s is not a
guard, so §6's check throws on every failure path.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-! ## 1. `Kernel.Environment.add`, at a fresh name

Three facts, all about `SMap.insert`: the map stays well-formed, the new name resolves to the
new `ConstantInfo`, and **every other name is untouched**.  The third is what carries an earlier
member's entry forward past the inserts for the later ones, and it is the one
`Verify/Environment/Extension.lean` has only in its `= none` form
(`Environment.find?_add_of_ne`). -/

theorem r113e_constants_add {env : Environment} (ci : ConstantInfo) :
    (env.add ci).constants = env.constants.insert ci.name ci := rfl

theorem r113e_constants_wf_add {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none) : (env.add ci).constants.WF :=
  mapWF.insert ci.name ci (by rwa [← mapWF.find?'_eq_find?])

theorem r113e_find?_add_self {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none) :
    (env.add ci).find? ci.name = some ci := by
  have hnone : env.constants.find? ci.name = none := by rwa [← mapWF.find?'_eq_find?]
  change SMap.find?' (env.constants.insert ci.name ci) ci.name = some ci
  rw [(mapWF.insert ci.name ci hnone).find?'_eq_find?, mapWF.find?_insert]
  simp

theorem r113e_find?_add_ne {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none) {n : Name} (hne : ci.name ≠ n) :
    (env.add ci).find? n = env.find? n := by
  have hnone : env.constants.find? ci.name = none := by rwa [← mapWF.find?'_eq_find?]
  change SMap.find?' (env.constants.insert ci.name ci) n = _
  rw [(mapWF.insert ci.name ci hnone).find?'_eq_find?, mapWF.find?_insert,
    if_neg (by simpa using hne), Kernel.Environment.find?, mapWF.find?'_eq_find?]

/-! ## 2. `declareInductiveTypes`

The loop is `infos.foldlM (fun env info => do env.checkName info.name ap;
return env.add (.inductInfo info)) c.env`.  §2.1 is the loop rule for exactly that shape, over a
list and with the `ConstantInfo` produced by an arbitrary function of the element — which is all
the generality the two stages need. -/

/-- **The `checkName`-then-`add` loop rule.**  Freshness is *not* a hypothesis: `checkName`
supplies it at each step, and the third clause is what turns that into distinctness of the whole
list, so nothing here has to assume the block's names are distinct. -/
theorem r113e_addLoop_WF {α : Type} (g : α → ConstantInfo) (ap : Bool) :
    ∀ {xs : List α} {env : Environment}, env.constants.WF →
      (xs.foldlM (fun (e : Environment) a =>
          (do Environment.checkName e (g a).name ap
              pure (e.add (g a)) : Except Exception Environment)) env).WF fun env' =>
        env'.constants.WF ∧
        (∀ a ∈ xs, env.find? (g a).name = none) ∧
        (∀ a ∈ xs, env'.find? (g a).name = some (g a)) ∧
        (∀ n, (∀ a ∈ xs, (g a).name ≠ n) → env'.find? n = env.find? n)
  | [], env, mapWF => Except.WF.pure ⟨mapWF, nofun, nofun, fun _ _ => rfl⟩
  | a :: xs, env, mapWF => by
    rw [List.foldlM_cons]
    refine Except.WF.bind (Q := fun e' => e' = env.add (g a) ∧ env.find? (g a).name = none)
      (Except.WF.bind (checkName.WF mapWF (g a).name ap) fun _ h =>
        Except.WF.pure ⟨rfl, h.1⟩) fun _ h => ?_
    obtain ⟨rfl, hfr⟩ := h
    have mapWF' := r113e_constants_wf_add mapWF hfr
    refine (r113e_addLoop_WF g ap (xs := xs) mapWF').mono fun env' h => ?_
    obtain ⟨hwf', hnone, hsome, hother⟩ := h
    -- no later member shares `a`'s name: it is already `some (g a)` in `env.add (g a)`
    have hne : ∀ b ∈ xs, (g b).name ≠ (g a).name := by
      intro b hb hEq
      have h := hnone b hb
      rw [hEq, r113e_find?_add_self mapWF hfr] at h
      exact absurd h nofun
    refine ⟨hwf', ?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hfr
      · rw [← r113e_find?_add_ne mapWF hfr (Ne.symm (hne b hb))]; exact hnone b hb
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · rw [hother _ hne, r113e_find?_add_self mapWF hfr]
      · exact hsome b hb
    · intro n hn
      rw [hother n fun b hb => hn b (.tail _ hb), r113e_find?_add_ne mapWF hfr (hn a (.head _))]

/-- The `InductiveVal` `declareInductiveTypes` stores for member `indType` with `numIndices`
indices — the record spelled out, so that §4 can read its fields. -/
def r113eIndVal (lparams : List Name) (all : List Name) (numParams numNested : Nat)
    (isRec isReflexive isUnsafe : Bool) (indType : InductiveType) (numIndices : Nat) :
    InductiveVal :=
  { indType with
    numParams, numIndices, all, numNested, isUnsafe, isRec, isReflexive
    levelParams := lparams
    ctors := indType.ctors.map (·.name) }

/-- The `InductiveVal` array `declareInductiveTypes` folds over, as a named definition so that
the fold equation below is `rfl`. -/
def r113eIndInfos (lparams : List Name) (numParams numNested : Nat) (isUnsafe : Bool)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) : Array InductiveVal :=
  Array.zipWith (fun indType numIndices => r113eIndVal lparams ((indTypes.map (·.name)).toList)
      numParams numNested (AddInductive.isRec indTypes stats.indConsts)
      (AddInductive.isReflexive indTypes stats.indConsts) isUnsafe indType numIndices)
    indTypes stats.nindices

theorem r113e_indInfos_getElem? {lparams numParams numNested isUnsafe stats indTypes}
    {j : Nat} {t : InductiveType} {ni : Nat}
    (ht : indTypes[j]? = some t) (hni : stats.nindices[j]? = some ni) :
    (r113eIndInfos lparams numParams numNested isUnsafe stats indTypes)[j]? =
      some (r113eIndVal lparams ((indTypes.map (·.name)).toList) numParams numNested
        (AddInductive.isRec indTypes stats.indConsts)
        (AddInductive.isReflexive indTypes stats.indConsts) isUnsafe t ni) := by
  rw [r113eIndInfos, Array.getElem?_zipWith, ht, hni]

/-- `declareInductiveTypes` **is** the loop `r113e_addLoop_WF` is about. -/
theorem r113e_declareInductiveTypes_eq {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {numParams : Nat} {indTypes : Array InductiveType}
    {numNested : Nat} {isUnsafe : Bool} :
    AddInductive.declareInductiveTypes stats numParams indTypes numNested isUnsafe c =
      (r113eIndInfos c.lparams numParams numNested isUnsafe stats indTypes).foldlM
        (fun (e : Environment) (v : InductiveVal) =>
          (do Environment.checkName e (ConstantInfo.inductInfo v).name c.allowPrimitive
              pure (e.add (.inductInfo v)) : Except Exception Environment)) c.env := rfl

/-- **`declareInductiveTypes`, refined.**  Per member: fresh before, stored after, with every
field of the stored `InductiveVal` pinned.  The `isRec`/`isReflexive`/`numNested` fields are
carried verbatim rather than characterised — `IndShape`'s `isRec` clause is what needs content
about them, and that is R8's business (`Verify/Inductive/Add.lean`), not this loop's.

Instrument 7: an `M.WF`, so a **rejecting** block satisfies it for free; §6's check exhibits the
succeeding case. -/
theorem AddInductive.M.WF.declareInductiveTypes {c : AddInductive.Context}
    (mapWF : c.env.constants.WF) (stats : AddInductive.InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested isUnsafe).WF c
      fun env' =>
        env'.constants.WF ∧
        ∀ (j : Nat) (t : InductiveType) (ni : Nat),
          indTypes[j]? = some t → stats.nindices[j]? = some ni →
          c.env.find? t.name = none ∧
          env'.find? t.name = some (.inductInfo (r113eIndVal c.lparams
            ((indTypes.map (·.name)).toList) numParams numNested
            (AddInductive.isRec indTypes stats.indConsts)
            (AddInductive.isReflexive indTypes stats.indConsts) isUnsafe t ni)) := by
  intro env' hok
  rw [r113e_declareInductiveTypes_eq, ← Array.foldlM_toList] at hok
  obtain ⟨hwf', hnone, hsome, -⟩ :=
    r113e_addLoop_WF (α := InductiveVal) (g := .inductInfo) c.allowPrimitive
      (xs := (r113eIndInfos c.lparams numParams numNested isUnsafe stats indTypes).toList)
      mapWF env' hok
  refine ⟨hwf', fun j t ni ht hni => ?_⟩
  have hmem : _ ∈ (r113eIndInfos c.lparams numParams numNested isUnsafe stats indTypes).toList :=
    List.mem_iff_getElem?.2 ⟨j, by
      rw [Array.getElem?_toList]; exact r113e_indInfos_getElem? ht hni⟩
  exact ⟨hnone _ hmem, hsome _ hmem⟩

/-! ## 3. `declareConstructors`

Two nested folds: the outer over the block's types, the inner over one type's constructors with
a `cidx` counter threaded beside the environment.  §3.1 is the counter-carrying loop rule; the
name stored is independent of the counter, which is what `hname` records and what keeps the
freshness bookkeeping identical to §2's. -/

/-- The counter-carrying form of `r113e_addLoop_WF`: the `ConstantInfo` may depend on the index,
its **name** may not.  The `p.1 = k + xs.length` clause is what makes the `cidx` of the `q`-th
constructor come out as `q` rather than merely "some number". -/
theorem r113e_addLoopIdx_WF {α : Type} (nm : α → Name) (g : Nat → α → ConstantInfo) (ap : Bool)
    (hname : ∀ k a, (g k a).name = nm a) :
    ∀ {xs : List α} {k : Nat} {env : Environment}, env.constants.WF →
      (xs.foldlM (fun (x : Nat × Environment) a =>
          match x with
          | (cidx, e) =>
            (do Environment.checkName e (g cidx a).name ap
                pure (cidx + 1, e.add (g cidx a)) : Except Exception (Nat × Environment)))
        (k, env)).WF fun p =>
        p.2.constants.WF ∧ p.1 = k + xs.length ∧
        (∀ a ∈ xs, env.find? (nm a) = none) ∧
        (∀ (q : Nat) a, xs[q]? = some a → p.2.find? (nm a) = some (g (k + q) a)) ∧
        (∀ n, (∀ a ∈ xs, nm a ≠ n) → p.2.find? n = env.find? n)
  | [], k, env, mapWF => Except.WF.pure ⟨mapWF, by simp, nofun, by simp, fun _ _ => rfl⟩
  | a :: xs, k, env, mapWF => by
    rw [List.foldlM_cons]
    refine Except.WF.bind
      (Q := fun p => p = (k + 1, env.add (g k a)) ∧ env.find? (nm a) = none)
      (Except.WF.bind (checkName.WF mapWF (g k a).name ap) fun _ h =>
        Except.WF.pure ⟨rfl, hname k a ▸ h.1⟩) fun p h => ?_
    obtain ⟨rfl, hfr⟩ := h
    have hfr' : env.find? (g k a).name = none := hname k a ▸ hfr
    have mapWF' := r113e_constants_wf_add mapWF hfr'
    refine (r113e_addLoopIdx_WF nm g ap hname (xs := xs) (k := k + 1) mapWF').mono
      fun p h => ?_
    obtain ⟨hwf', hcnt, hnone, hsome, hother⟩ := h
    have hself : (env.add (g k a)).find? (nm a) = some (g k a) :=
      hname k a ▸ r113e_find?_add_self mapWF hfr'
    have hne : ∀ b ∈ xs, nm b ≠ nm a := by
      intro b hb hEq
      have h := hnone b hb
      rw [hEq, hself] at h
      exact absurd h nofun
    refine ⟨hwf', by simp [hcnt]; omega, ?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hfr
      · rw [← r113e_find?_add_ne mapWF hfr' (hname k a ▸ Ne.symm (hne b hb))]; exact hnone b hb
    · intro q b hq
      match q, hq with
      | 0, hq =>
        cases hq
        rw [hother _ hne, hself, Nat.add_zero]
      | q + 1, hq =>
        have := hsome q b hq
        rwa [show k + 1 + q = k + (q + 1) by omega] at this
    · intro n hn
      rw [hother n fun b hb => hn b (.tail _ hb),
        r113e_find?_add_ne mapWF hfr' (hname k a ▸ hn a (.head _))]

/-- The `ConstructorVal` `declareConstructors` stores.  `numFields` reproduces the
implementation's `assert!` verbatim; the two `panicWithPosWithDecl` terms are definitionally
equal (both reduce to `default`), which is why §3.2's fold equation is `rfl`. -/
def r113eCtorVal (lparams : List Name) (np : Nat) (isUnsafe : Bool) (tyName : Name)
    (cidx : Nat) (ctor : Constructor) : ConstructorVal :=
  { type := ctor.type, cidx, isUnsafe
    levelParams := lparams
    name := ctor.name
    induct := tyName
    numParams := np
    numFields :=
      assert! AddInductive.declareConstructors.arity 0 ctor.type ≥ np
      AddInductive.declareConstructors.arity 0 ctor.type - np }

theorem r113eCtorVal_name {lparams np isUnsafe tyName cidx ctor} :
    (ConstantInfo.ctorInfo (r113eCtorVal lparams np isUnsafe tyName cidx ctor)).name =
      ctor.name := rfl

/-- **The inner loop, instantiated.** -/
theorem r113e_ctorLoop_WF {lparams : List Name} {np : Nat} {isUnsafe : Bool} {tyName : Name}
    {ap : Bool} {ctors : List Constructor} {k : Nat} {env : Environment}
    (mapWF : env.constants.WF) :
    (ctors.foldlM (fun (x : Nat × Environment) (ctor : Constructor) =>
        match x with
        | (cidx, e) =>
          (do Environment.checkName e ctor.name ap
              pure (cidx + 1, e.add (.ctorInfo (r113eCtorVal lparams np isUnsafe tyName cidx ctor)))
            : Except Exception (Nat × Environment)))
      (k, env)).WF fun p =>
      p.2.constants.WF ∧ p.1 = k + ctors.length ∧
      (∀ ctor ∈ ctors, env.find? ctor.name = none) ∧
      (∀ (q : Nat) ctor, ctors[q]? = some ctor →
        p.2.find? ctor.name =
          some (ConstantInfo.ctorInfo
            (r113eCtorVal lparams np isUnsafe tyName (k + q) ctor))) ∧
      (∀ n, (∀ ctor ∈ ctors, ctor.name ≠ n) → p.2.find? n = env.find? n) :=
  r113e_addLoopIdx_WF (α := Constructor) (fun ctor => ctor.name)
    (fun cidx ctor => ConstantInfo.ctorInfo (r113eCtorVal lparams np isUnsafe tyName cidx ctor))
    ap (fun _ _ => rfl) mapWF

/-! ### 3.2 The outer loop -/

/-- **`declareConstructors`, refined.**  Per constructor of per member: fresh before, stored
after, `cidx` equal to its position in its own type's list, `induct` the owning type's name,
`numParams` the checked parameter count.

Instrument 7: an `M.WF`, so a rejecting block satisfies it for free; §6 exhibits the succeeding
case. -/
theorem r113e_ctorOuter_WF {lparams : List Name} {np : Nat} {isUnsafe : Bool} {ap : Bool} :
    ∀ {ts : List InductiveType} {env : Environment}, env.constants.WF →
      (ts.foldlM (fun (e : Environment) (indType : InductiveType) =>
          (do let x ← indType.ctors.foldlM (fun (x : Nat × Environment) (ctor : Constructor) =>
                  match x with
                  | (cidx, e') =>
                    (do Environment.checkName e' ctor.name ap
                        pure (cidx + 1, e'.add (.ctorInfo
                          (r113eCtorVal lparams np isUnsafe indType.name cidx ctor)))
                      : Except Exception (Nat × Environment)))
                (0, e)
              match x with
              | (_, e') => pure e' : Except Exception Environment)) env).WF fun env' =>
        env'.constants.WF ∧
        (∀ t ∈ ts, ∀ ctor ∈ t.ctors, env.find? ctor.name = none) ∧
        (∀ t ∈ ts, ∀ (q : Nat) ctor, t.ctors[q]? = some ctor →
          env'.find? ctor.name =
            some (.ctorInfo (r113eCtorVal lparams np isUnsafe t.name q ctor))) ∧
        (∀ n, (∀ t ∈ ts, ∀ ctor ∈ t.ctors, ctor.name ≠ n) → env'.find? n = env.find? n)
  | [], env, mapWF => Except.WF.pure ⟨mapWF, nofun, nofun, fun _ _ => rfl⟩
  | t :: ts, env, mapWF => by
    rw [List.foldlM_cons]
    refine Except.WF.bind
      (Q := fun e₁ => e₁.constants.WF ∧
        (∀ ctor ∈ t.ctors, env.find? ctor.name = none) ∧
        (∀ (q : Nat) ctor, t.ctors[q]? = some ctor →
          e₁.find? ctor.name = some (.ctorInfo (r113eCtorVal lparams np isUnsafe t.name q ctor))) ∧
        (∀ n, (∀ ctor ∈ t.ctors, ctor.name ≠ n) → e₁.find? n = env.find? n))
      (Except.WF.bind (r113e_ctorLoop_WF (lparams := lparams) (np := np) (isUnsafe := isUnsafe)
          (tyName := t.name) (ap := ap) (ctors := t.ctors) (k := 0) mapWF) fun p hp =>
        Except.WF.pure ⟨hp.1, hp.2.2.1, by simpa using hp.2.2.2.1, hp.2.2.2.2⟩)
      fun e₁ h => ?_
    obtain ⟨hwf₁, hnone₁, hsome₁, hother₁⟩ := h
    refine (r113e_ctorOuter_WF (ts := ts) hwf₁).mono fun env' h => ?_
    obtain ⟨hwf', hnone', hsome', hother'⟩ := h
    have hne : ∀ t' ∈ ts, ∀ c' ∈ t'.ctors, ∀ c ∈ t.ctors, c'.name ≠ c.name := by
      intro t' ht' c' hc' c hc hEq
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hc
      have h := hnone' t' ht' c' hc'
      rw [hEq, hsome₁ q c hq] at h
      exact absurd h nofun
    refine ⟨hwf', ?_, ?_, ?_⟩
    · intro t' ht' c' hc'
      rcases List.mem_cons.1 ht' with rfl | ht'
      · exact hnone₁ c' hc'
      · rw [← hother₁ _ fun c hc => Ne.symm (hne t' ht' c' hc' c hc)]
        exact hnone' t' ht' c' hc'
    · intro t' ht' q c' hq
      rcases List.mem_cons.1 ht' with rfl | ht'
      · rw [hother' _ fun t'' ht'' c'' hc'' => hne t'' ht'' c'' hc'' c'
          (List.mem_iff_getElem?.2 ⟨q, hq⟩)]
        exact hsome₁ q c' hq
      · exact hsome' t' ht' q c' hq
    · intro n hn
      rw [hother' n fun t' ht' c' hc' => hn t' (.tail _ ht') c' hc',
        hother₁ n fun c hc => hn t (.head _) c hc]

/-- `declareConstructors` **is** the nested loop above. -/
theorem r113e_declareConstructors_eq {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {indTypes : Array InductiveType} {isUnsafe : Bool} :
    AddInductive.declareConstructors stats indTypes isUnsafe c =
      indTypes.toList.foldlM (fun (e : Environment) (indType : InductiveType) =>
          (do let x ← indType.ctors.foldlM (fun (x : Nat × Environment) (ctor : Constructor) =>
                  match x with
                  | (cidx, e') =>
                    (do Environment.checkName e' ctor.name c.allowPrimitive
                        pure (cidx + 1, e'.add (.ctorInfo
                          (r113eCtorVal c.lparams stats.params.size isUnsafe indType.name
                            cidx ctor)))
                      : Except Exception (Nat × Environment)))
                (0, e)
              match x with
              | (_, e') => pure e' : Except Exception Environment)) c.env := by
  rw [Array.foldlM_toList]; rfl

/-- **`declareConstructors`, refined**, in `M.WF` form. -/
theorem AddInductive.M.WF.declareConstructors {c : AddInductive.Context}
    (mapWF : c.env.constants.WF) (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) :
    (AddInductive.declareConstructors stats indTypes isUnsafe).WF c fun env' =>
      env'.constants.WF ∧
      ∀ (j : Nat) (t : InductiveType), indTypes[j]? = some t →
        ∀ (q : Nat) (ctor : Constructor), t.ctors[q]? = some ctor →
          c.env.find? ctor.name = none ∧
          env'.find? ctor.name = some (.ctorInfo
            (r113eCtorVal c.lparams stats.params.size isUnsafe t.name q ctor)) := by
  intro env' hok
  rw [r113e_declareConstructors_eq] at hok
  obtain ⟨hwf', hnone, hsome, -⟩ := r113e_ctorOuter_WF mapWF env' hok
  refine ⟨hwf', fun j t ht q ctor hq => ?_⟩
  have htm : t ∈ indTypes.toList :=
    List.mem_iff_getElem?.2 ⟨j, by rw [Array.getElem?_toList]; exact ht⟩
  exact ⟨hnone t htm ctor (List.mem_iff_getElem?.2 ⟨q, hq⟩), hsome t htm q ctor hq⟩


/-! ## 4. From the stored records to `IndShapeOf` and `CtorShape`

The two numeric facts row 113e names are `stats.params.size = D.np` and
`stats.nindices[j] = T.indices.length`; the constructor side needs one more, the arity/field-count
correspondence, and it is stated as a hypothesis rather than proved — `arity` counts the stored
type's pi-binders and `C.fields.length` is the abstract field count, and identifying them is
`TrIndDecl`'s business, not this loop's.

`hall` is in `IndShapeOf`'s own two-halves shape (`Verify/Environment/Basic.lean`): the `∃` half
is non-vacuity and the `∀` half is pinning, and the second must be supplied per member because
the predicate constrains *every* member carrying the name. -/

/-- **`IndShapeOf` from `declareInductiveTypes`' record.** -/
theorem r113e_indShapeOf_of_indVal {D : VInductDecl'} {lparams all : List Name}
    {numParams numNested : Nat} {isRec isReflexive isUnsafe : Bool}
    {t : InductiveType} {ni : Nat}
    (hnp : numParams = D.np)
    (hex : ∃ T ∈ D.types, T.name = t.name)
    (hall : ∀ T ∈ D.types, T.name = t.name →
      ni = T.indices.length ∧ t.ctors.map (·.name) = T.ctors.map (·.name))
    (hrec : isRec = false → ∀ T' ∈ D.types, ∀ C ∈ T'.ctors, C.recFields = []) :
    IndShapeOf D id (.inductInfo (r113eIndVal lparams all numParams numNested
      isRec isReflexive isUnsafe t ni)) := by
  refine ⟨_, rfl, hex, fun T hT hn => ⟨_, rfl, hn.symm, hnp, ?_, ?_, hrec⟩⟩
  · have hn' : T.name = t.name := hn
    exact ((hall T hT hn').1).symm ▸ rfl
  · have hn' : T.name = t.name := hn
    show t.ctors.map (·.name) = _
    simpa using (hall T hT hn').2

/-- **`CtorShape` from `declareConstructors`' record.**  The `assert!`'s guard is a hypothesis:
where it fails the implementation stores a `panic`, and nothing here claims that value. -/
theorem r113e_ctorShape_of_ctorVal {D : VInductDecl'} {lparams : List Name} {np : Nat}
    {isUnsafe : Bool} {tyName : Name} {q : Nat} {ctor : Constructor} {C : VIndCtor}
    (hname : ctor.name = C.name) (hnp : np = D.np)
    (hge : AddInductive.declareConstructors.arity 0 ctor.type ≥ np)
    (hfields : AddInductive.declareConstructors.arity 0 ctor.type - np = C.fields.length) :
    CtorShape D id tyName C (.ctorInfo (r113eCtorVal lparams np isUnsafe tyName q ctor)) := by
  refine ⟨_, rfl, hname, rfl, hnp, ?_⟩
  show (if AddInductive.declareConstructors.arity 0 ctor.type ≥ np then _ else _) = _
  rw [if_pos hge]; exact hfields

/-! ## 5. Instrument 7's succeeding case, as theorems

The two record spellings are checked against the block `Verify/Inductive/StagesFiring.lean` uses:
at `R10.Wit.uIndType` they are `R10.Wit.uInd` and `R10.Wit.uCtor` **on the nose**, by `rfl`.
Together with that file's check R1 — which executes the run and compares the stored constants
against those same two values — this is the succeeding case an `Except.WF`/`M.WF` statement needs
in order to have content. -/

/-- `declareInductiveTypes`' record at the `U` block is exactly `R10.Wit.uInd`. -/
theorem r113e_indVal_uInd :
    r113eIndVal [] [`R10.Wit.U] 0 0 false false false R10.Wit.uIndType 0 = R10.Wit.uInd := rfl

/-- `declareConstructors`' record at the `U` block is exactly `R10.Wit.uCtor` — `numFields`
included, so the `assert!` branch really is the one taken. -/
theorem r113e_ctorVal_uCtor :
    r113eCtorVal [] 0 false `R10.Wit.U 0
      { name := `R10.Wit.U.unit, type := .const `R10.Wit.U [] } = R10.Wit.uCtor := rfl

/-- …and the `assert!`'s guard holds there, so §4's `hge` is satisfiable. -/
theorem r113e_arity_uCtor :
    AddInductive.declareConstructors.arity 0 (Expr.const `R10.Wit.U []) = 0 := rfl

/- **Check R2** (test, not a proof).  Both loops are run on the `U` block, from the empty
environment, through `checkInductiveTypes`' own `stats` — so the succeeding case of §2's and §3's
`M.WF` statements is exhibited rather than assumed, and the `stats` fields §4 quantifies over are
read out of the checker rather than guessed.  Throws on every failure path. -/
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let c0 : AddInductive.Context :=
    { env := Kernel.Environment.empty `main, lparams := [], safety := .safe,
      allowPrimitive := false }
  let run : Except Kernel.Exception (Nat × Array Nat × Environment × Environment) :=
    AddInductive.checkInductiveTypes 0 #[R10.Wit.uIndType]
      (fun stats => fun c => do
        let env1 ← AddInductive.declareInductiveTypes stats 0 #[R10.Wit.uIndType] 0 false c
        let env2 ← AddInductive.declareConstructors stats #[R10.Wit.uIndType] false
          { c with env := env1 }
        pure (stats.params.size, stats.nindices, env1, env2)) c0
  let .ok (nparams, nindices, env1, env2) := run
    | throwError "check R2: checkInductiveTypes/declare* REJECTED the U block, so §2 and §3 \
        have no exhibited succeeding case"
  unless nparams == 0 && nindices == #[0] do
    throwError "check R2: stats.params.size={nparams} nindices={nindices}, not 0 / #[0] -- \
      §4's two numeric hypotheses are instantiated at the wrong values"
  let some (.inductInfo iv) := env1.find? `R10.Wit.U
    | throwError "check R2: declareInductiveTypes stored no inductInfo at U"
  unless iv.name == R10.Wit.uInd.name && iv.levelParams == R10.Wit.uInd.levelParams &&
      iv.type == R10.Wit.uInd.type && iv.numParams == R10.Wit.uInd.numParams &&
      iv.numIndices == R10.Wit.uInd.numIndices && iv.all == R10.Wit.uInd.all &&
      iv.ctors == R10.Wit.uInd.ctors && iv.numNested == R10.Wit.uInd.numNested &&
      iv.isRec == R10.Wit.uInd.isRec && iv.isUnsafe == R10.Wit.uInd.isUnsafe &&
      iv.isReflexive == R10.Wit.uInd.isReflexive do
    throwError "check R2: declareInductiveTypes' stored InductiveVal is not r113eIndVal's -- \
      the record spelling in this file is wrong"
  let some (.ctorInfo cv) := env2.find? `R10.Wit.U.unit
    | throwError "check R2: declareConstructors stored no ctorInfo at U.unit"
  unless cv.name == R10.Wit.uCtor.name && cv.levelParams == R10.Wit.uCtor.levelParams &&
      cv.type == R10.Wit.uCtor.type && cv.induct == R10.Wit.uCtor.induct &&
      cv.cidx == R10.Wit.uCtor.cidx && cv.numParams == R10.Wit.uCtor.numParams &&
      cv.numFields == R10.Wit.uCtor.numFields && cv.isUnsafe == R10.Wit.uCtor.isUnsafe do
    throwError "check R2: declareConstructors' stored ConstructorVal is not r113eCtorVal's -- \
      the record spelling in this file is wrong"
  unless (env1.find? `R10.Wit.U.unit).isNone do
    throwError "check R2: declareInductiveTypes already declared U.unit, so §3's freshness \
      clause is not about a fresh name"
  logInfo m!"check R2: declareInductiveTypes and declareConstructors both SUCCEED on the U \
    block and store exactly r113eIndVal/r113eCtorVal (= R10.Wit.uInd/uCtor); \
    stats.params.size=0, stats.nindices=#[0] ✓"


end Lean4Lean
