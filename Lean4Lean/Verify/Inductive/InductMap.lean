import Lean4Lean.Verify.Inductive.DeclareStages
import Lean4Lean.Verify.Inductive.NestedRunInvariant

/-!
# `InductiveMapGate`: which names `Environment.addInductive` writes into the constant map

`Verify/Inductive/NoNestedAll.lean` reduces the `inductDecl` branch of `VEnv.NoNestedN` to one
residual, `InductiveMapGate`: `Environment.addInductive` preserves `SMap.WF` and adds no name
outside `indDeclNamesN types k`.  This file discharges it.

## The shape of the argument

`Environment.addInductive` (`Lean4Lean/Inductive/Add.lean`:1117) touches the constant map in
exactly two places, and they are the two branches of one `if`:

* `AddInductive.run np res.types numNested`, whose three `Environment.add` sites are
  `declareInductiveTypes` (one `.inductInfo` per member), `declareConstructors` (one `.ctorInfo`
  per constructor) and `run`'s own recursor loop (one `.recInfo` at `mkRecName` per member);
* when `numNested ≠ 0`, a `StateT.run (s := env)` block that **discards** that environment and
  rebuilds from the *original* `env`: one `.inductInfo` and its `.ctorInfo`s per *user* member,
  `mkRecName` of each user member, and one renamed `appendIndexAfter' (mkRecName types[0].name) i`
  per auxiliary member.

So the whole obligation is a delta calculus over `Environment.add`, and §1 gives it.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-! ## §1 A delta calculus for the constant map

`MapDeltaIn env env' B` is the gate's conclusion made composable: given that `env`'s map is
well-formed, `env'`'s is, everything `env` held `env'` still holds, and everything `env'` holds is
either `env`'s or a **member of the budget `B`, stored under its own name**.

Two design points, both measured rather than assumed.

* **No freshness clause.**  `Lean.SMap.WF` (`Lean4Lean/Std/SMap.lean`:29) is a *staging*
  invariant — `stage₁ = true` and `map₂ = .empty` — and `SMap.WF.insert`'s hypothesis
  `_hn : s.find? k = none` is **unused in its own proof**, as is any freshness in
  `WF.find?_insert`.  So both halves of the gate's conclusion are established by `add` with no
  side condition at all (§1.1), and the composition below needs no freshness bookkeeping.
  `DeclareStages.lean`'s `r113e_constants_wf_add` and `r113e_find?_add_ne` carry `hfresh` for
  historical reasons; §1.1 restates them without it.
* **The `ci.name = n` conjunct is load-bearing, not decoration.**  The nested branch reads an
  `.inductInfo` back out of the intermediate environment and re-adds it at *its own* `name` field
  (`Inductive/Add.lean`:1164), so a mis-keyed entry would let it write an arbitrary name.  `SMap.WF`
  does **not** forbid mis-keying, so this conjunct is what closes that hole. -/

/-- **The composable delta**, with the input map's well-formedness *discharged* rather than
assumed: every lemma below carries `mapWF` explicitly, because `checkName`'s freshness
postcondition needs it and a relativised form could not be used inside a loop body.  `B` is a
*budget*, fixed along a chain, which is what makes the loop invariant constant. -/
structure DeltaCore (env env' : Environment) (B : Name → Prop) : Prop where
  /-- the result's map is well-formed -/
  wf : env'.constants.WF
  /-- nothing is removed or overwritten -/
  mono : ∀ n ci, env.find? n = some ci → env'.find? n = some ci
  /-- nothing outside `B` is added, and a `B`-name is stored under itself -/
  keyed : ∀ n ci, env'.find? n = some ci → env.find? n = some ci ∨ (B n ∧ ci.name = n)

/-- The gate's own shape: `DeltaCore` relativised to a well-formed input map. -/
def MapDeltaIn (env env' : Environment) (B : Name → Prop) : Prop :=
  env.constants.WF → DeltaCore env env' B

theorem DeltaCore.rfl' {env : Environment} {B : Name → Prop} (wf : env.constants.WF) :
    DeltaCore env env B := ⟨wf, fun _ _ h => h, fun _ _ h => .inl h⟩

theorem DeltaCore.trans {e₀ e₁ e₂ : Environment} {B : Name → Prop}
    (h₁ : DeltaCore e₀ e₁ B) (h₂ : DeltaCore e₁ e₂ B) : DeltaCore e₀ e₂ B :=
  ⟨h₂.wf, fun n ci h => h₂.mono n ci (h₁.mono n ci h),
   fun n ci h => (h₂.keyed n ci h).elim (h₁.keyed n ci) .inr⟩

theorem DeltaCore.widen {env env' : Environment} {B B' : Name → Prop}
    (h : DeltaCore env env' B) (hs : ∀ n, B n → B' n) : DeltaCore env env' B' :=
  ⟨h.wf, h.mono, fun n ci hf => (h.keyed n ci hf).imp id fun p => ⟨hs n p.1, p.2⟩⟩

/-! ### §1.1 `Environment.add`, with no side condition

`SMap.WF` is preserved by `insert`, and `find?` after an `insert` is a conditional, both
unconditionally.  The two lemmas below are the freshness-free forms; `find?_add` is the equation
every step of the calculus reduces to. -/

theorem SMap_wf_insert {α β} [BEq α] [Hashable α] {s : Lean.SMap α β} (h : s.WF) (k : α) (v : β) :
    (s.insert k v).WF := by
  obtain ⟨st, m₁, m₂⟩ := s
  cases h.stage
  exact ⟨rfl, h.map₂⟩

theorem constants_wf_add {env : Environment} (mapWF : env.constants.WF) (ci : ConstantInfo) :
    (env.add ci).constants.WF :=
  r113e_constants_add ci ▸ SMap_wf_insert mapWF ci.name ci

/-- **The one equation.**  No freshness: an `add` at an occupied key overwrites, and the
right-hand side says so. -/
theorem find?_add {env : Environment} (mapWF : env.constants.WF) (ci : ConstantInfo) (n : Name) :
    (env.add ci).find? n = if ci.name = n then some ci else env.find? n := by
  change SMap.find?' (env.constants.insert ci.name ci) n = _
  rw [(SMap_wf_insert mapWF ci.name ci).find?'_eq_find?, mapWF.find?_insert,
    show Kernel.Environment.find? env n = env.constants.find? n from mapWF.find?'_eq_find? n]
  by_cases he : ci.name = n
  · simp [he]
  · simp [he, beq_iff_eq]

/-- **The step.**  One `add` at a budgeted, fresh key.  Freshness is needed only for the
monotonicity clause — an `add` at an occupied key really does destroy information — and every
call site has it from `checkName`. -/
theorem DeltaCore.add {env : Environment} {B : Name → Prop} {ci : ConstantInfo}
    (mapWF : env.constants.WF) (hB : B ci.name) (hfresh : env.find? ci.name = none) :
    DeltaCore env (env.add ci) B := by
  refine ⟨constants_wf_add mapWF ci, fun n c h => ?_, fun n c h => ?_⟩
  · rw [find?_add mapWF]
    split
    · next he => rw [← he, hfresh] at h; exact absurd h nofun
    · exact h
  · rw [find?_add mapWF] at h
    split at h
    · next he => cases h; exact .inr ⟨he ▸ hB, he⟩
    · exact .inl h

/-- The step with the environment already grown: the shape a `checkName`-then-`add` loop body
presents. -/
theorem DeltaCore.add_of {e₀ env : Environment} {B : Name → Prop} {ci : ConstantInfo}
    (h : DeltaCore e₀ env B) (hB : B ci.name) (hfresh : env.find? ci.name = none) :
    DeltaCore e₀ (env.add ci) B := h.trans (DeltaCore.add h.wf hB hfresh)

/-! ## §2 The CPS frames: `AddInductive.M`'s continuation-passing phases never touch the map

`AddInductive.run` is a chain of continuation-passing checks (`checkInductiveTypes`,
`checkConstructors`, `getElimLevel`, `isKTarget`, `mkRecInfos`) around three `Environment.add`
sites.  The checks change only the reader's `lctx` and `ngen` — **no `withEnv`, no `add`** — so any
postcondition mentioning only the environment passes straight through them.  That is what the
lemmas below say: each takes its continuation's `WF` *at every context with the same `env`*.

`AddInductive.M = ReaderT Context (Except Exception)`, so a "frame" here is literally a context
substitution; the binder rule is `rfl`. -/

namespace AddInductive

variable {α : Type}

/-- The binder rule at a plain `Context`: `Verify/Inductive/Add.lean`'s `M.WF.withLocalDecl` is
stated at a `VContext` and carries `TrExprS`/`IsType` obligations, which a statement about the
constant map does not need. -/
theorem withLocalDecl_frame {c : Context} {name : Name} {bi : BinderInfo} {ty : Expr}
    {k : Expr → M α} {Q : α → Prop}
    (H : ∀ c' : Context, c'.env = c.env → (k (.fvar ⟨c.ngen.curr⟩)).WF c' Q) :
    (withLocalDecl name bi ty k).WF c Q := H _ rfl

/-- Every `M` computation satisfies the trivial postcondition — the rule that discharges the
type-checker calls (`checkType`, `whnf`, `isDefEq`, `ensureSort`, `ensureType`,
`consumeAnnotations`) without touching `TypeChecker.M.WF`. -/
theorem M.WF.triv {c : Context} (x : M α) : x.WF c fun _ => True := fun _ _ => trivial

theorem M.WF.bind_triv {c : Context} {x : M α} {f : α → M β} {Q : β → Prop}
    (h : ∀ a, (f a).WF c Q) : (x >>= f).WF c Q := (M.WF.triv x).bind fun a _ => h a

/-- A `throw` in statement position: the rest of the `do` block is unreachable. -/
theorem WF_throw_bind {c : Context} {x : M PUnit} {f : PUnit → M β} {Q : β → Prop}
    (hx : x.WF c fun _ => False) : (x >>= f).WF c Q :=
  M.WF.bind (Q := fun _ => False) hx fun _ h => h.elim

/-- The inner telescope loop of `checkInductiveTypes`: parameters and indices, `whnf`'d one
binder at a time.  Only `lctx`/`ngen` move. -/
theorem WF_checkInductiveTypes_loop {c : Context} {Q : α → Prop} {np : Nat}
    {kk : Expr → InductiveStats → Nat → M α}
    (H : ∀ t s n (c' : Context), c'.env = c.env → (kk t s n).WF c' Q) :
    ∀ (fuel : Nat) (stats : InductiveStats) (type : Expr) (i ni : Nat) (c' : Context),
      c'.env = c.env →
      (checkInductiveTypes.loopInd.loop np stats type i ni fuel kk).WF c' Q := by
  intro fuel
  induction fuel with
  | zero => intro stats type i ni c' hc; exact M.WF.throw
  | succ fuel ih =>
    intro stats type i ni c' hc
    rw [checkInductiveTypes.loopInd.loop.eq_def]
    split
    · exact M.WF.throw
    · next fuel' heq =>
      obtain rfl : fuel' = fuel := (Nat.succ.inj heq).symm
      split
      · split
        · split
          · refine M.WF.bind_triv fun dom' => withLocalDecl_frame fun c'' hc'' => ?_
            exact M.WF.bind_triv fun _ => ih _ _ _ _ _ (hc''.trans hc)
          · refine M.WF.bind_triv fun _ => M.WF.bind_triv fun _ => ?_
            split
            · exact M.WF.bind_triv fun _ => ih _ _ _ _ _ hc
            · exact WF_throw_bind M.WF.throw
        · refine M.WF.bind_triv fun dom' => withLocalDecl_frame fun c'' hc'' => ?_
          exact M.WF.bind_triv fun _ => ih _ _ _ _ _ (hc''.trans hc)
      · split
        · exact WF_throw_bind M.WF.throw
        · exact H _ _ _ _ hc

/-- The member loop of `checkInductiveTypes`.  Well-founded on `indTypes.size - dIdx`, so the
induction is on a bound `m` for that measure. -/
theorem WF_checkInductiveTypes_loopInd {c : Context} {Q : α → Prop} {np : Nat}
    {its : Array InductiveType} {k : InductiveStats → M α}
    (H : ∀ stats (c' : Context), c'.env = c.env → (k stats).WF c' Q) :
    ∀ (m dIdx : Nat) (stats : InductiveStats) (c' : Context), its.size - dIdx ≤ m →
      c'.env = c.env → (checkInductiveTypes.loopInd np its k dIdx stats).WF c' Q := by
  intro m
  induction m with
  | zero =>
    intro dIdx stats c' hm hc
    rw [checkInductiveTypes.loopInd.eq_def]
    split
    · next hlt => exact absurd hlt (by omega)
    · exact H _ _ hc
  | succ m ih =>
    intro dIdx stats c' hm hc
    rw [checkInductiveTypes.loopInd.eq_def]
    split
    · next hlt =>
      repeat refine M.WF.bind_triv fun _ => ?_
      refine WF_checkInductiveTypes_loop (c := c) (fun t s n c'' hc'' => ?_) _ _ _ _ _ _ hc
      repeat refine M.WF.bind_triv fun _ => ?_
      try dsimp only
      split
      · refine M.WF.bind_triv fun _ => ?_
        exact ih (dIdx + 1) _ _ (by omega) hc''
      · split
        · exact WF_throw_bind M.WF.throw
        · exact ih (dIdx + 1) _ _ (by omega) hc''
    · exact H _ _ hc

/-- **`checkInductiveTypes` frames any environment-only postcondition.** -/
theorem WF_checkInductiveTypes {c : Context} {Q : α → Prop} {np : Nat}
    {its : Array InductiveType} {k : InductiveStats → M α}
    (H : ∀ stats (c' : Context), c'.env = c.env → (k stats).WF c' Q) :
    (checkInductiveTypes np its k).WF c Q := by
  rw [checkInductiveTypes]
  repeat refine M.WF.bind_triv fun _ => ?_
  exact WF_checkInductiveTypes_loopInd H its.size 0 _ c (by omega) rfl

/-! ### §2.1 `mkRecInfos`

Seven nested continuation loops.  Only the six whose continuation carries the *rest* of the
computation need a frame; `loopUArgs` is used in value position (`let viTy ← loopUArgs …`), where
`M.WF.bind_triv` treats it as opaque. -/

theorem WF_loopArgs1 {c : Context} {Q : α → Prop} {stats : InductiveStats}
    {k : Array Expr → M α} (H : ∀ ids (c' : Context), c'.env = c.env → (k ids).WF c' Q) :
    ∀ (fuel : Nat) (type : Expr) (i : Nat) (ids : Array Expr) (c' : Context), c'.env = c.env →
      (mkRecInfos.loopArgs1 stats type i ids fuel k).WF c' Q := by
  intro fuel
  induction fuel with
  | zero => intro type i ids c' hc; exact M.WF.throw
  | succ fuel ih =>
    intro type i ids c' hc
    rw [mkRecInfos.loopArgs1.eq_def]
    split
    · exact M.WF.throw
    · next fuel' heq =>
      obtain rfl : fuel' = fuel := (Nat.succ.inj heq).symm
      try dsimp only
      split
      · split
        · exact M.WF.bind_triv fun _ => ih _ _ _ _ hc
        · refine M.WF.bind_triv fun _ => withLocalDecl_frame fun c'' hc'' => ?_
          exact M.WF.bind_triv fun _ => ih _ _ _ _ (hc''.trans hc)
      · exact H _ _ hc

theorem WF_loopInd1 {c : Context} {Q : α → Prop} {stats : InductiveStats}
    {its : Array InductiveType} {el : Level} {k : Array RecInfo → M α}
    (H : ∀ ris (c' : Context), c'.env = c.env → (k ris).WF c' Q) :
    ∀ (m dIdx : Nat) (ris : Array RecInfo) (c' : Context), its.size - dIdx ≤ m →
      c'.env = c.env → (mkRecInfos.loopInd1 stats its el dIdx ris k).WF c' Q := by
  intro m
  induction m with
  | zero =>
    intro dIdx ris c' hm hc
    rw [mkRecInfos.loopInd1.eq_def]
    split
    · next hlt => exact absurd hlt (by omega)
    · exact H _ _ hc
  | succ m ih =>
    intro dIdx ris c' hm hc
    rw [mkRecInfos.loopInd1.eq_def]
    split
    · next hlt =>
      repeat refine M.WF.bind_triv fun _ => ?_
      refine WF_loopArgs1 (c := c) (fun ids c'' hc'' => ?_) _ _ _ _ _ hc
      refine M.WF.bind_triv fun _ => withLocalDecl_frame fun c₃ h₃ => ?_
      repeat refine M.WF.bind_triv fun _ => ?_
      refine withLocalDecl_frame fun c₄ h₄ => ?_
      exact ih (dIdx + 1) _ _ (by omega) (h₄.trans (h₃.trans hc''))
    · exact H _ _ hc

theorem WF_loopCtorArgs {c : Context} {Q : α → Prop} {stats : InductiveStats}
    {k : Expr → Array Expr → Array Expr → M α}
    (H : ∀ t bu u (c' : Context), c'.env = c.env → (k t bu u).WF c' Q) :
    ∀ (fuel : Nat) (t : Expr) (i : Nat) (bu u : Array Expr) (c' : Context), c'.env = c.env →
      (mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel).WF c' Q := by
  intro fuel
  induction fuel with
  | zero => intro t i bu u c' hc; exact M.WF.throw
  | succ fuel ih =>
    intro t i bu u c' hc
    rw [mkRecInfos.loopCtorArgs.loop.eq_def]
    split
    · exact M.WF.throw
    · next fuel' heq =>
      obtain rfl : fuel' = fuel := (Nat.succ.inj heq).symm
      try dsimp only
      split
      · split
        · exact ih _ _ _ _ _ hc
        · refine M.WF.bind_triv fun _ => withLocalDecl_frame fun c'' hc'' => ?_
          exact M.WF.bind_triv fun _ => ih _ _ _ _ _ (hc''.trans hc)
      · exact H _ _ _ _ hc

theorem WF_loopU {c : Context} {Q : α → Prop} {stats : InductiveStats} {u : Array Expr}
    {ris : Array RecInfo} {k : Array Expr → M α}
    (H : ∀ v (c' : Context), c'.env = c.env → (k v).WF c' Q) :
    ∀ (m i : Nat) (v : Array Expr) (c' : Context), u.size - i ≤ m → c'.env = c.env →
      (mkRecInfos.loopU stats u ris i v k).WF c' Q := by
  intro m
  induction m with
  | zero =>
    intro i v c' hm hc
    rw [mkRecInfos.loopU.eq_def]
    split
    · next hlt => exact absurd hlt (by omega)
    · exact H _ _ hc
  | succ m ih =>
    intro i v c' hm hc
    rw [mkRecInfos.loopU.eq_def]
    split
    · next hlt =>
      repeat refine M.WF.bind_triv fun _ => ?_
      refine withLocalDecl_frame fun c'' hc'' => ?_
      exact ih (i + 1) _ _ (by omega) (hc''.trans hc)
    · exact H _ _ hc

theorem WF_loopCtors {c : Context} {Q : α → Prop} {stats : InductiveStats} {nm : Name}
    {dIdx : Nat} {k : Array RecInfo → M α}
    (H : ∀ ris (c' : Context), c'.env = c.env → (k ris).WF c' Q) :
    ∀ (ctors : List Constructor) (ris : Array RecInfo) (c' : Context), c'.env = c.env →
      (mkRecInfos.loopCtors stats nm dIdx ris ctors k).WF c' Q := by
  intro ctors
  induction ctors with
  | nil => intro ris c' hc; exact H _ _ hc
  | cons ctor ctors ih =>
    intro ris c' hc
    rw [mkRecInfos.loopCtors.eq_def]
    try dsimp only
    refine WF_loopCtorArgs (c := c) (fun t bu uu c'' hc'' => ?_) _ _ _ _ _ _ hc
    try dsimp only
    refine WF_loopU (c := c) (fun v c₃ h₃ => ?_) uu.size 0 _ _ (by omega) hc''
    repeat refine M.WF.bind_triv fun _ => ?_
    refine withLocalDecl_frame fun c₄ h₄ => ?_
    exact ih _ _ (h₄.trans h₃)

theorem WF_loopInd2 {c : Context} {Q : α → Prop} {stats : InductiveStats}
    {its : Array InductiveType} {k : Array RecInfo → M α}
    (H : ∀ ris (c' : Context), c'.env = c.env → (k ris).WF c' Q) :
    ∀ (m dIdx : Nat) (ris : Array RecInfo) (c' : Context), its.size - dIdx ≤ m →
      c'.env = c.env → (mkRecInfos.loopInd2 stats its dIdx ris k).WF c' Q := by
  intro m
  induction m with
  | zero =>
    intro dIdx ris c' hm hc
    rw [mkRecInfos.loopInd2.eq_def]
    split
    · next hlt => exact absurd hlt (by omega)
    · exact H _ _ hc
  | succ m ih =>
    intro dIdx ris c' hm hc
    rw [mkRecInfos.loopInd2.eq_def]
    split
    · next hlt =>
      try dsimp only
      refine WF_loopCtors (c := c) (fun ris' c'' hc'' => ?_) _ _ _ hc
      exact ih (dIdx + 1) _ _ (by omega) hc''
    · exact H _ _ hc

/-- **`mkRecInfos` frames any environment-only postcondition.** -/
theorem WF_mkRecInfos {c : Context} {Q : α → Prop} {stats : InductiveStats}
    {its : Array InductiveType} {el : Level} {k : Array RecInfo → M α}
    (H : ∀ ris (c' : Context), c'.env = c.env → (k ris).WF c' Q) :
    (mkRecInfos stats its el k).WF c Q := by
  rw [mkRecInfos]
  refine WF_loopInd1 (c := c) (fun ris c' hc' => ?_) its.size 0 _ c (by omega) rfl
  exact WF_loopInd2 (c := c) H its.size 0 _ _ (by omega) hc'

/-! ## §3 The three `add` sites of `AddInductive.run`

`declareInductiveTypes`, `declareConstructors` and `run`'s own recursor loop.  The budget is
`runBudget`: a member name, a constructor name, or `mkRecName` of a member name. -/

/-- Every name `AddInductive.run` may write, given the (possibly nesting-expanded) block it is
called on. -/
def runBudget (its : List InductiveType) (n : Name) : Prop :=
  (∃ t ∈ its, t.name = n) ∨ (∃ t ∈ its, ∃ ct ∈ t.ctors, ct.name = n) ∨
    (∃ t ∈ its, Lean.mkRecName t.name = n)

/-- `r113e_addLoop_WF`'s four clauses, read as a `DeltaCore`. -/
theorem deltaCore_of_addLoop {β : Type} {g : β → ConstantInfo} {xs : List β}
    {env env' : Environment} (hwf : env'.constants.WF)
    (hnone : ∀ a ∈ xs, env.find? (g a).name = none)
    (hsome : ∀ a ∈ xs, env'.find? (g a).name = some (g a))
    (hother : ∀ n, (∀ a ∈ xs, (g a).name ≠ n) → env'.find? n = env.find? n) :
    DeltaCore env env' (fun n => ∃ a ∈ xs, (g a).name = n) := by
  refine ⟨hwf, fun n ci h => ?_, fun n ci h => ?_⟩
  · by_cases hs : ∃ a ∈ xs, (g a).name = n
    · obtain ⟨a, ha, rfl⟩ := hs
      rw [hnone a ha] at h; exact absurd h nofun
    · rw [hother n (by simpa using hs)]; exact h
  · by_cases hs : ∃ a ∈ xs, (g a).name = n
    · obtain ⟨a, ha, he⟩ := hs
      have := hsome a ha
      rw [he] at this
      rw [this] at h
      cases h
      exact .inr ⟨⟨a, ha, he⟩, he⟩
    · rw [hother n (by simpa using hs)] at h; exact .inl h

/-- The `InductiveVal`s `declareInductiveTypes` folds over are indexed by the block's members, so
each one's name is a member name. -/
theorem r113eIndInfos_name {lparams : List Name} {np nn : Nat} {iu : Bool}
    {stats : InductiveStats} {its : Array InductiveType} {v : InductiveVal}
    (h : v ∈ (r113eIndInfos lparams np nn iu stats its).toList) :
    ∃ t ∈ its.toList, t.name = v.name := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  rw [Array.getElem?_toList, r113eIndInfos, Array.getElem?_zipWith] at hj
  cases ht : its[j]? with
  | none => rw [ht] at hj; exact absurd hj nofun
  | some t =>
    cases hni : stats.nindices[j]? with
    | none => rw [ht, hni] at hj; exact absurd hj nofun
    | some ni =>
      rw [ht, hni] at hj
      cases hj
      exact ⟨t, List.mem_iff_getElem?.2 ⟨j, by rwa [Array.getElem?_toList]⟩, rfl⟩

/-- **`declareInductiveTypes`, as a delta.** -/
theorem WF_declareInductiveTypes {c : Context} (mapWF : c.env.constants.WF)
    {stats : InductiveStats} {np nn : Nat} {its : Array InductiveType} {iu : Bool} :
    (declareInductiveTypes stats np its nn iu).WF c fun env' =>
      DeltaCore c.env env' (runBudget its.toList) := by
  intro env' hok
  rw [r113e_declareInductiveTypes_eq, ← Array.foldlM_toList] at hok
  obtain ⟨hwf, hnone, hsome, hother⟩ :=
    r113e_addLoop_WF (α := InductiveVal) (g := .inductInfo) c.allowPrimitive
      (xs := (r113eIndInfos c.lparams np nn iu stats its).toList) mapWF env' hok
  refine (deltaCore_of_addLoop hwf hnone hsome hother).widen fun n hn => ?_
  obtain ⟨v, hv, he⟩ := hn
  obtain ⟨t, ht, hnm⟩ := r113eIndInfos_name hv
  exact .inl ⟨t, ht, hnm.trans he⟩

/-- **`declareConstructors`, as a delta.** -/
theorem WF_declareConstructors {c : Context} (mapWF : c.env.constants.WF)
    {stats : InductiveStats} {its : Array InductiveType} {iu : Bool} :
    (declareConstructors stats its iu).WF c fun env' =>
      DeltaCore c.env env' (runBudget its.toList) := by
  intro env' hok
  rw [r113e_declareConstructors_eq] at hok
  obtain ⟨hwf, hnone, hsome, hother⟩ := r113e_ctorOuter_WF (lparams := c.lparams)
    (np := stats.params.size) (isUnsafe := iu) (ap := c.allowPrimitive) mapWF env' hok
  refine ⟨hwf, fun n ci h => ?_, fun n ci h => ?_⟩
  · by_cases hs : ∃ t ∈ its.toList, ∃ ct ∈ t.ctors, ct.name = n
    · obtain ⟨t, ht, ct, hct, rfl⟩ := hs
      rw [hnone t ht ct hct] at h; exact absurd h nofun
    · rw [hother n ?_]
      · exact h
      · intro t ht ct hct he; exact hs ⟨t, ht, ct, hct, he⟩
  · by_cases hs : ∃ t ∈ its.toList, ∃ ct ∈ t.ctors, ct.name = n
    · obtain ⟨t, ht, ct, hct, he⟩ := hs
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hct
      have hst := hsome t ht q ct hq
      rw [he] at hst
      rw [hst] at h
      cases h
      exact .inr ⟨.inr (.inl ⟨t, ht, ct, hct, he⟩), he⟩
    · rw [hother n (fun t ht ct hct he => hs ⟨t, ht, ct, hct, he⟩)] at h
      exact .inl h

/-! ### §3.1 The recursor loop

`run`'s last phase is `for h : dIdx in [:indTypes.size]` inside the `StateT Nat` layer, with the
environment as the loop's accumulator.  `Verify/Inductive/Add.lean`'s `SM.WF.forIn` is stated for
`forIn` over a list; the source's loop binds the membership proof, so it is `forIn'`, and a range
rather than a list. -/

theorem SM_forIn' {γ β : Type} {c : Context} {Inv : β → Prop} :
    ∀ {xs : List γ} {f : (a : γ) → a ∈ xs → β → StateT Nat M (ForInStep β)} {b : β},
      (∀ a (h : a ∈ xs) b, Inv b → SM.WF c (f a h b) fun r => ∃ b', r = .yield b' ∧ Inv b') →
      Inv b → SM.WF c (forIn' xs b f) fun b' => Inv b'
  | [], _, _, _, h => SM.WF.pure h
  | a :: as, f, b, H, h => by
    rw [List.forIn'_cons]
    refine (H a (.head _) b h).bind fun r hr => ?_
    obtain ⟨b', rfl, hinv⟩ := hr
    exact SM_forIn' (fun v hv b hb => H v (.tail _ hv) b hb) hinv

/-- `checkName` in the `StateT Nat` layer, with its freshness postcondition. -/
theorem SM_checkName {c : Context} {env : Environment} (mapWF : env.constants.WF)
    (n : Name) (ap : Bool) :
    SM.WF c (liftM (liftM (Environment.checkName env n ap) : M PUnit) : StateT Nat M PUnit)
      fun _ => env.find? n = none :=
  SM.WF.lift (M.WF.liftExcept fun _ h => (checkName.WF mapWF n ap _ h).1)

/-! ### §3.2 `AddInductive.run`, assembled -/

set_option maxHeartbeats 1000000 in
/-- **The map side of `AddInductive.run`.**  Every constant it writes is a member name, a
constructor name, or `mkRecName` of a member name — of the block *it* was called on, which for
`Environment.addInductive` is `res.types`, not `types`. -/
theorem WF_run {c : Context} (mapWF : c.env.constants.WF) (np : Nat)
    (types : List InductiveType) (nn : Nat) :
    (run np types nn).WF c fun env' => DeltaCore c.env env' (runBudget types) := by
  rw [run]
  repeat refine M.WF.bind_triv fun _ => ?_
  refine WF_checkInductiveTypes_loopInd (c := c) (fun stats c₁ h₁ => ?_)
    types.toArray.size 0 _ c (by omega) rfl
  refine M.WF.bind (Q := fun e₁ => DeltaCore c.env e₁ (runBudget types)) ?_ fun e₁ hd₁ => ?_
  · intro e₁ he
    have h := WF_declareInductiveTypes (c := c₁) (by rw [h₁]; exact mapWF) e₁ he
    rw [h₁] at h
    simpa using h
  · refine M.WF.withReader ?_
    refine M.WF.bind_triv fun _ => ?_
    refine M.WF.bind (Q := fun e₂ => DeltaCore c.env e₂ (runBudget types)) ?_ fun e₂ hd₂ => ?_
    · intro e₂ he
      exact hd₁.trans (by
        simpa using WF_declareConstructors (c := { c₁ with env := e₁ }) hd₁.wf e₂ he)
    · refine M.WF.withReader ?_
      refine M.WF.bind_triv fun _ => M.WF.bind_triv fun _ => ?_
      refine WF_mkRecInfos (c := { c₁ with env := e₂ }) (fun ris c₃ h₃ => ?_)
      try dsimp only
      refine M.WF.bind_triv fun _ => M.WF.bind_triv fun _ => ?_
      refine M.WF.stateT_run' ?_
      refine SM.WF.bind (SM.WF.lift (M.WF.getEnv (Q := fun e => e = c₃.env) rfl)) fun e he => ?_
      refine SM.WF.bind (Q := fun _ => True) (fun _ _ _ _ => trivial) fun _ _ => ?_
      try dsimp only
      simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
      refine SM.WF.bind (SM_forIn'
        (Inv := fun env => DeltaCore c.env env (runBudget types)) ?_ (he ▸ h₃ ▸ hd₂))
        fun env' hd => SM.WF.pure hd
      intro dIdx hmem env hInv
      try dsimp only
      refine SM.WF.bind (Q := fun _ => True) (fun _ _ _ _ => trivial) fun _ _ => ?_
      refine SM.WF.bind (SM_checkName hInv.wf _ _) fun _ hfr => ?_
      refine SM.WF.pure ⟨_, rfl, hInv.add_of ?_ hfr⟩
      exact .inr (.inr ⟨_, Array.getElem_mem_toList .., rfl⟩)

end AddInductive

/-! ## §3.3 Residual A: `newTypes` grows only alongside `nestedAux`

`ElimNestedInductive.run` reports `numNested = 0` exactly when its `nestedAux` stayed empty, and the
*only* `newTypes.push` in the whole development (`Inductive/Add.lean`:858) sits in the same
`for J_name in I_val.all` body as the `nestedAux.push` (:845), **after** it.  So the invariant is

    Bal L s :  s.nestedAux = #[] → s.newTypes.size = L

which every step preserves **except** the `newTypes.push`, and that step is reached only in a state
where `nestedAux` is already non-empty.  No *flat* invariant can do this job: an invariant bounding
`newTypes.size` by `nestedAux.size` is broken by the `newTypes.push`, and one bounding it the other
way by the `nestedAux.push`, so the body has to be walked once with a **changing** postcondition —
which is what `MWF.bind'` (`Verify/Inductive/NestedRunInvariant.lean`:126) is for. -/

namespace ElimNestedInductive

/-- `nestedAux` is non-empty: what the `newTypes.push` needs, and what the `nestedAux.push`
establishes. -/
def NE (s : State) : Prop := s.nestedAux ≠ #[]

/-- The coupling, in the only form that is an invariant. -/
def Bal (L : Nat) (s : State) : Prop := s.nestedAux = #[] → s.newTypes.size = L

theorem NE.toBal {L : Nat} {s : State} (h : NE s) : Bal L s := fun he => absurd he h

theorem NE.push_nestedAux {s : State} {x : Expr × Name} :
    NE { s with nestedAux := s.nestedAux.push x } := by
  intro h
  have h' : s.nestedAux.push x = #[] := h
  have : (s.nestedAux.push x).size = 0 := by rw [h']; rfl
  simp [Array.size_push] at this

theorem NE.push_newTypes {s : State} {T : InductiveType} (h : NE s) :
    NE { s with newTypes := s.newTypes.push T } := h

theorem Bal.push_nestedAux {L : Nat} {s : State} {x : Expr × Name} :
    Bal L { s with nestedAux := s.nestedAux.push x } := NE.push_nestedAux.toBal

theorem Bal.set {L : Nat} {s : State} {i : Nat} {T : InductiveType} (h : Bal L s) :
    Bal L { s with newTypes := s.newTypes.set! i T } := by
  intro he
  rw [show ({ s with newTypes := s.newTypes.set! i T } : State).newTypes.size
    = s.newTypes.size from by simp [Array.set!]]
  exact h he

theorem Bal.ngen {L : Nat} {s : State} (h : Bal L s) :
    Bal L { s with ngen := s.ngen.next } := h

theorem MWF.mkUniqueName_gen {env : Environment} {I : State → Prop}
    (hI : ∀ (s : State) (i : Nat), I s → I { s with nextIdx := i }) (n : Name) :
    MWF env I (mkUniqueName n) (fun _ => I) := by
  intro s a s' hs h
  rw [mkUniqueName_state h]
  exact hI s _ hs

theorem MWF.replaceParams_gen {env : Environment} {I : State → Prop}
    (params As : Array Expr) (e : Expr) :
    MWF env I (replaceParams params e As) (fun _ => I) := by
  intro s a s' hs h
  unfold replaceParams at h
  split at h
  · rw [pure_eq] at h; cases h; exact hs
  · rw [panic_eq] at h; cases h; exact hs

/-- The automation.  Every `M`-operation `replaceIfNested` and `run.loop` perform is one of
`NestedRunInvariant.lean` §5's nine, plus the two `modify`s.  The **switch** alternative — the
`MWF.bind'` whose first component is the `nestedAux.push` with postcondition `NE` — is what makes a
non-flat invariant automatable: from there on the chain runs at `NE`, which the `newTypes.push`
preserves, and the final `pure` weakens `NE` back to `Bal L`. -/
syntax "mwf_bal" : tactic
macro_rules
  | `(tactic| mwf_bal) => `(tactic|
      repeat (first
        | exact MWF.pure' fun _ h => h
        | exact MWF.pure' fun _ h => NE.toBal h
        | exact MWF.throw' _
        | exact MWF.panic' _ _ _ _ _
        | exact MWF.liftExcept' _
        | exact MWF.replaceParams_gen _ _ _
        | exact MWF.mkUniqueName_gen (fun _ _ h => h) _
        | exact MWF.get_inv
        | exact MWF.read_inv
        | exact MWF.modify' fun _ h => h
        | exact MWF.modify' fun _ h => Bal.set h
        | exact MWF.modify' fun _ _ => NE.push_nestedAux
        | refine MWF.bind' (MWF.modify' (Q := fun _ => NE) fun _ _ => NE.push_nestedAux)
            fun _ => ?_
        | rw [Lean.Expr.withApp_eq]
        | dsimp only
        | refine MWF.bind_inv ?_ fun _ => ?_
        | refine MWF.forIn_inv (fun _ _ => ?_) _ _
        | refine MWF.mapM' (fun _ => ?_) _
        | refine MWF.replaceNoCacheT (fun _ => ?_) _
        | split))

set_option maxHeartbeats 4000000 in
/-- **`replaceIfNested` keeps the coupling.** -/
theorem MWF.replaceIfNested_bal {env : Environment} {L : Nat}
    (lctx : LocalContext) (params As : Array Expr) (e : Expr) :
    MWF env (Bal L) (replaceIfNested lctx params As e) (fun _ => Bal L) := by
  unfold replaceIfNested
  refine MWF.bind' (MWF.isNestedApp' e) fun o => ?_
  cases o with
  | none => exact MWF.pure' fun _ h => h
  | some I_val => mwf_bal

theorem MWF.replaceAllNested_bal {env : Environment} {L : Nat}
    (lctx : LocalContext) (params As : Array Expr) (e : Expr) :
    MWF env (Bal L) (replaceAllNested lctx params As e) (fun _ => Bal L) :=
  MWF.replaceNoCacheT (fun _ => MWF.replaceIfNested_bal lctx params As _) e

/-- `aux2nested` is a cons-fold of `nestedAux`, so it is empty only if `nestedAux` is. -/
theorem foldl_cons_length {β : Type} {g : Expr × Name → β} :
    ∀ (l : List (Expr × Name)) (acc : List β),
      (l.foldl (fun m a => g a :: m) acc).length = l.length + acc.length
  | [], acc => by simp
  | a :: l, acc => by
    rw [List.foldl_cons, foldl_cons_length l]
    simp; omega

theorem nestedAux_empty_of_aux2nested {arr : Array (Expr × Name)}
    (h : arr.foldl (fun m (p : Expr × Name) => (p.2, p.1) :: m) [] = []) : arr = #[] := by
  have hl : (arr.toList.foldl (fun m (p : Expr × Name) => (p.2, p.1) :: m) []).length = 0 := by
    rw [← Array.foldl_toList] at h; rw [h]; rfl
  rw [foldl_cons_length (g := fun p => (p.2, p.1))] at hl
  simp at hl
  exact hl

set_option maxHeartbeats 2000000 in
/-- **`run.loop` keeps the coupling**, and reports it at the point where the `Result` is built. -/
theorem MWF.run_loop_bal {env : Environment} {L : Nat} (np : Nat) (lctx : LocalContext)
    (params : Array Expr) :
    ∀ (fuel i : Nat), MWF env (Bal L) (run.loop np lctx params i fuel)
      (fun r s => Bal L s ∧ (r.aux2nested = [] → r.types.length = L)) := by
  intro fuel
  induction fuel with
  | zero => intro i; rw [run.loop]; exact MWF.throw' _
  | succ fuel ih =>
    intro i
    rw [run.loop]
    refine MWF.bind' MWF.get' fun s0 => ?_
    split
    · refine MWF.weaken (P := Bal L) ?_ (fun s' h => h.1)
      refine MWF.bind' (MWF.mapM' (fun ctor => ?_) _) fun ctors => ?_
      · refine MWF.withParams' (fun _ h => h) np (fun lctx' t As hAs => ?_) _
        rw [hAs]
        simp only [beq_self_eq_true, if_true]
        exact MWF.bind' (MWF.replaceAllNested_bal lctx' params As t) fun _ =>
          MWF.pure' fun _ h => h
      · exact MWF.bind' (MWF.modify' fun _ h => Bal.set h) fun _ => ih (i + 1)
    · refine MWF.pure' fun s h => ⟨h.1, fun hz => ?_⟩
      obtain ⟨hb, rfl⟩ := h
      have := hb (nestedAux_empty_of_aux2nested hz)
      simpa using this

theorem MWF.run_bal {env : Environment} {L : Nat} (fuel np : Nat)
    (types : List InductiveType) :
    MWF env (Bal L) (run fuel np types)
      (fun r s => Bal L s ∧ (r.aux2nested = [] → r.types.length = L)) := by
  unfold run
  split
  · refine MWF.bind' (MWF.modify' (Q := fun _ => Bal L) fun _ h => h) fun _ => ?_
    exact MWF.withParams' (fun _ h => h) np
      (fun lctx t ps _ => MWF.run_loop_bal np lctx ps fuel 0) _
  · exact MWF.throw' _

end ElimNestedInductive

/-! ## §4 `Environment.addInductive`: the non-nested branch

`Environment.addInductive` runs its guard loop, then `ElimNestedInductive.run`, then
`AddInductive.run`, and **exits at `if numNested = 0 then return env'`** unless the nesting
elimination actually produced auxiliary members.  §3's `WF_run` is the whole of that exit; the two
things still owed are named here and nowhere else. -/

/-- The gate's own budget: `indDeclNamesN types k` for some `k`, membership only. -/
def indBudget (types : List InductiveType) (n : Name) : Prop :=
  ∃ k, n ∈ Lean4Lean.indDeclNamesN types k

theorem indBudget_of_runBudget {types : List InductiveType} {n : Name}
    (h : AddInductive.runBudget types n) : indBudget types n := by
  refine ⟨0, ?_⟩
  rw [indDeclNamesN_zero, indDeclNames, List.mem_append, List.mem_append]
  rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, ct, hct, rfl⟩ | ⟨t, ht, rfl⟩
  · exact .inl (.inl (List.mem_map_of_mem ht))
  · exact .inl (.inr (List.mem_flatMap.2 ⟨t, ht, List.mem_map_of_mem hct⟩))
  · exact .inr (List.mem_map_of_mem ht)

/-- **Residual A.**  `ElimNestedInductive.run` pushes a member to `newTypes` only inside the
`for J_name in I_val.all` loop of `replaceIfNested`, which pushes to `nestedAux` first
(`Inductive/Add.lean`:845 before :858), so reporting no nesting means it added no member.  Compare
`Verify/Inductive/NestedRunInvariant.lean`'s `runSkelExtends`, which gives the *prefix* half of this
unconditionally; what is owed is only that the extension is empty. -/
def ElimNoAuxGate : Prop :=
  ∀ (env : Environment) (fuel np : Nat) (types : List InductiveType)
    (s : ElimNestedInductive.State) (r : ElimNestedInductive.Result)
    (s' : ElimNestedInductive.State),
    s.newTypes.toList = types → s.nestedAux = #[] →
    ElimNestedInductive.run fuel np types env s = .ok (r, s') →
    r.aux2nested = [] → r.types.length = types.length

/-- **Residual A, discharged** (§3.3). -/
theorem elimNoAuxGate : ElimNoAuxGate := by
  intro env fuel np types s r s' hs hne hrun hz
  exact (ElimNestedInductive.MWF.run_bal (L := types.length) fuel np types s r s'
    (fun _ => by rw [← hs]; simp) hrun).2 hz

/-- With residual A, the block `AddInductive.run` is handed has the input block's names. -/
theorem runBudget_of_noAux (G : ElimNoAuxGate) {env : Environment} {fuel np : Nat}
    {types : List InductiveType} {r : ElimNestedInductive.Result}
    {s : ElimNestedInductive.State} (hs : s.newTypes.toList = types) (hne : s.nestedAux = #[])
    (hres : (ElimNestedInductive.run fuel np types env).run' s = .ok r)
    (hz : r.aux2nested = []) {n : Name} (h : AddInductive.runBudget r.types n) :
    AddInductive.runBudget types n := by
  obtain ⟨s', hs'⟩ := ElimNestedInductive.run'_ok hres
  have hlen := G env fuel np types _ r s' hs hne hs' hz
  have hpre := ElimNestedInductive.run_prefix hs hs'
  have key : ∀ t ∈ r.types, ∃ u ∈ types, t.name = u.name ∧
      t.ctors.map (·.name) = u.ctors.map (·.name) := by
    intro t ht
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    have hjlt : j < types.length := by
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨u, hu, h1, h2⟩ := hpre j t hj hjlt
    exact ⟨u, List.mem_iff_getElem?.2 ⟨j, hu⟩, h1, h2⟩
  rcases h with ⟨t, ht, he⟩ | ⟨t, ht, ct, hct, he⟩ | ⟨t, ht, he⟩
  · obtain ⟨u, hu, h1, -⟩ := key t ht; exact .inl ⟨u, hu, h1 ▸ he⟩
  · obtain ⟨u, hu, -, h2⟩ := key t ht
    have : ct.name ∈ u.ctors.map (·.name) := h2 ▸ List.mem_map_of_mem hct
    obtain ⟨ct', hct', he'⟩ := List.mem_map.1 this
    exact .inr (.inl ⟨u, hu, ct', hct', he'.trans he⟩)
  · obtain ⟨u, hu, h1, -⟩ := key t ht; exact .inr (.inr ⟨u, hu, h1 ▸ he⟩)

/-! ### §4.1 The split, and the branch that is closed

**Residual B**, the nested rebuild, is assumed at the level of the whole function rather than as a
statement about the `StateT.run (s := env)` block, because that block is a term with no name: it
mentions `res`, `recNameMap'` and `allIndNames`, all local.  The guard
`∀ res, … → res.aux2nested ≠ []` is exactly the negation of the case §4 closes, so the two
hypotheses partition the input space with no overlap and no gap. -/

set_option maxHeartbeats 1000000 in
/-- **The gate, on the branch `AddInductive.run` alone decides.**  `WF_run` is the content; the two
hypothesis is residual B (the nested rebuild); residual A is `elimNoAuxGate`, proved in §3.3. -/
theorem addInductive_mapDelta
    (GB : ∀ {env env' : Environment} {lparams : List Name} {np : Nat}
        {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig},
        env.constants.WF → Environment.addInductive env lparams np types iu ap fuel = .ok env' →
        (∀ res, (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
            { lvls := lparams.map .param, newTypes := types.toArray } = .ok res →
            res.aux2nested ≠ []) →
        DeltaCore env env' (indBudget types))
    {env : Environment} {lparams : List Name} {np : Nat} {types : List InductiveType}
    {iu ap : Bool} {fuel : FuelConfig} (mapWF : env.constants.WF) :
    (Environment.addInductive env lparams np types iu ap fuel).WF
      fun env' => DeltaCore env env' (indBudget types) := by
  by_cases hz : ∃ res, (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok res ∧ res.aux2nested = []
  · obtain ⟨res, hres, hz0⟩ := hz
    unfold Environment.addInductive
    refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
    refine Except.WF.bind_self fun res' hres' => ?_
    have hz0' : res'.aux2nested = [] := by
      cases Except.ok.inj (hres.symm.trans hres'); exact hz0
    simp only [hz0', List.length_nil]
    refine Except.WF.bind_self fun env2 henv2 => ?_
    simp only [if_true]
    refine Except.WF.pure
      ((AddInductive.WF_run ?_ np res'.types 0 env2 henv2).widen fun n hn => ?_)
    · exact mapWF
    · exact indBudget_of_runBudget (runBudget_of_noAux elimNoAuxGate (by simp) rfl hres' hz0' hn)
  · exact fun env' h => GB mapWF h fun res hres hne => hz ⟨res, hres, hne⟩

/-- **`InductiveMapGate`, verbatim.**  Restated here rather than imported (`NoNestedAll.lean`
imports `RestoreFaithful`, and this file must stay below it), so that the bridge from `DeltaCore` to
the gate's own `constants.find?` phrasing is machine-checked and not asserted: `Environment.find?`
is `constants.find?'`, and `SMap.WF.find?'_eq_find?` is what identifies the two — at **both**
environments, which is why the delta has to report `env'.constants.WF` and not merely relay
`env`'s. -/
theorem inductiveMapGate_of
    (GB : ∀ {env env' : Environment} {lparams : List Name} {np : Nat}
        {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig},
        env.constants.WF → Environment.addInductive env lparams np types iu ap fuel = .ok env' →
        (∀ res, (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
            { lvls := lparams.map .param, newTypes := types.toArray } = .ok res →
            res.aux2nested ≠ []) →
        DeltaCore env env' (indBudget types)) :
    ∀ {env env' : Environment} {lparams : List Name} {np : Nat} {types : List InductiveType}
      {iu ap : Bool} {fuel : FuelConfig},
      Environment.addInductive env lparams np types iu ap fuel = .ok env' → env.constants.WF →
        env'.constants.WF ∧ ∀ n ci, env'.constants.find? n = some ci →
          env.constants.find? n = some ci ∨ ∃ k, n ∈ Lean4Lean.indDeclNamesN types k := by
  intro env env' lparams np types iu ap fuel h mapWF
  have d := addInductive_mapDelta GB mapWF env' h
  refine ⟨d.wf, fun n ci hf => ?_⟩
  have hf' : env'.find? n = some ci := by
    rw [show env'.find? n = env'.constants.find?' n from rfl, d.wf.find?'_eq_find?]; exact hf
  rcases d.keyed n ci hf' with h1 | ⟨hb, -⟩
  · refine .inl ?_
    rw [show env.find? n = env.constants.find?' n from rfl, mapWF.find?'_eq_find?] at h1
    exact h1
  · exact .inr hb

/-! ## §5 The firing, and the axiom trail

"Instantiate, don't admire": §4's theorem is an `Except.WF`, so a *rejecting* input satisfies it for
free.  The `#eval` below checks that `Environment.addInductive` really does accept a block on the
branch §4 closes — `inductive Foo : Prop | mk`, from the empty kernel environment, with
`numNested = 0` — and that the resulting map holds exactly the three names `indDeclNames` allows and
nothing else.  It **throws** on every failure path, so it is a guard rather than a log line. -/

/-- `inductive Foo : Prop | mk`, the smallest block that reaches all three `add` sites. -/
def fooIndType : InductiveType :=
  { name := `Foo, type := .sort .zero,
    ctors := [{ name := `Foo.mk, type := .const `Foo [] }] }

#eval show Lean.CoreM Unit from do
  let kenv := Lean.Kernel.Environment.empty `main
  let some env' := (Lean4Lean.Environment.addInductive kenv [] 0 [fooIndType] false false).toOption
    | throwError "InductMap/§5: Environment.addInductive REJECTS `inductive Foo : Prop | mk` from \
        the empty environment -- §4's theorem is vacuous on the branch it closes"
  let added := env'.constants.toList.map (·.1)
  let budget := Lean4Lean.indDeclNames [fooIndType]
  let extra := added.filter fun n => !budget.contains n
  unless extra.isEmpty do
    throwError "InductMap/§5: the map after one accepted addInductive holds {extra.length} names \
      outside indDeclNames -- addInductive_mapDelta's conclusion is FALSE at this input: {extra}"
  let missing := budget.filter fun n => !added.contains n
  unless missing.isEmpty do
    throwError "InductMap/§5: addInductive stored none of {missing} -- the block reaches fewer \
      than three add sites, so the firing does not exercise the recursor loop"
  Lean.logInfo m!"InductMap/§5: `inductive Foo : Prop | mk` is ACCEPTED from the empty environment; \
    the resulting map holds exactly the {budget.length} names of indDeclNames and no others -- \
    all three add sites fired and §4's conclusion is non-vacuous ✓"

#print axioms Lean4Lean.AddInductive.WF_run
#print axioms Lean4Lean.AddInductive.WF_declareInductiveTypes
#print axioms Lean4Lean.AddInductive.WF_declareConstructors
#print axioms Lean4Lean.AddInductive.WF_mkRecInfos
#print axioms Lean4Lean.AddInductive.WF_checkInductiveTypes
#print axioms Lean4Lean.ElimNestedInductive.MWF.replaceIfNested_bal
#print axioms Lean4Lean.ElimNestedInductive.MWF.run_bal
#print axioms Lean4Lean.elimNoAuxGate
#print axioms Lean4Lean.runBudget_of_noAux
#print axioms Lean4Lean.indBudget_of_runBudget
#print axioms Lean4Lean.addInductive_mapDelta
#print axioms Lean4Lean.inductiveMapGate_of
#print axioms Lean4Lean.find?_add
#print axioms Lean4Lean.DeltaCore.add

end Lean4Lean
