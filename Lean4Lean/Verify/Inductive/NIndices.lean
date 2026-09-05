import Lean4Lean.Verify.Inductive.InductMap

/-!
# `stats.nindices.size = indTypes.size`, and the first field of `RunFreshGate`

`Verify/Inductive/NestedRebuild.lean` §1.1 measured that residual B of `InductiveMapGate` is
**false** without member-name freshness in the input environment, named the missing content
`Lean4Lean.RunFreshGate`, and identified its `member` field as the falsity barrier.  The mechanism it
gives, restated so this file can discharge it:

* the gate quantifies over every `env` with `env.constants.WF`, and `SMap.WF` does not forbid a
  **mis-keyed** entry (`Lean4Lean/Std/SMap.lean`:34-38 — the freshness binder is literally `_hn` and
  the body never uses it);
* so an `env` holding `.inductInfo ind` under key `types[0].name` with `ind.name` outside every
  budget would be inherited by `env'` and would refute `DeltaCore.keyed`;
* the **only** rejector is `Environment.checkName info.name` inside
  `AddInductive.declareInductiveTypes` (`Inductive/Add.lean`:298), whose fold runs over
  `indTypes.zipWith (bs := stats.nindices) …` (`:289`).  `Array.zipWith` truncates to the *shorter*
  argument, so `checkName` fires at index `j` only when `j < stats.nindices.size`.

That is why `AddInductive.M.WF.declareInductiveTypes` (`DeclareStages.lean`:166) guards its per-member
freshness clause by `stats.nindices[j]? = some ni`, and why the array-size equality is load-bearing
rather than cosmetic.  `Inductive/Add.lean`:254 is the implementation's own `assert!` of exactly it.

## What is proved

§1 strengthens the two CPS frames of `checkInductiveTypes` (`InductMap.lean` §2) so that the
continuation may **assume** the equality:

* the inner telescope loop leaves `nindices` alone (`WF_checkInductiveTypes_loop_ni`);
* the member loop's invariant is `stats.nindices.size = dIdx ∧ dIdx ≤ indTypes.size`
  (`WF_checkInductiveTypes_loopInd_ni`) — the `≤` half is what turns the loop's exit condition
  `¬ dIdx < indTypes.size` into the *equality* rather than `≥`.

§2 spends it: `WF_run_member` is `RunFreshGate.member` proved outright, and `WF_run_ctor` is
`RunFreshGate.ctor`.  `RunFreshGate.of_ctors` then reduces the three-field barrier to one field.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive

variable {α : Type}

/-! ## §1 The `nindices`-aware frames

**The measured obstacle, and why this section is bigger than "one array-size invariant".**  The
continuation `k` of `checkInductiveTypes` is *not* applied to the `stats` the member loop threads: it
is applied to the four-fold `assert!` chain at `Inductive/Add.lean`:253-257,

    k <| assert! stats.levels.length == lparams.length
         assert! stats.nindices.size == indTypes.size
         assert! stats.indConsts.size == indTypes.size
         assert! stats.params.size == nparams
         stats

and `panicWithPosWithDecl` is an opaque `panicCore`, so in a failing branch nothing at all can be
proved about the delivered stats.  Hence the postcondition `stats.nindices.size = indTypes.size` is
**not** provable from a `nindices`-only invariant: *all four* assert conditions have to be discharged
first, or the delivered stats may be the panic value, whose `nindices` is not `stats.nindices`.
Three of the four are pushed-in-lockstep bookkeeping; the fourth, `params.size = nparams`, is a
genuine invariant of the **inner** telescope loop and is why `LoopInv` below has five fields.

`c'.lparams = c.lparams` also has to be threaded, which `InductMap.lean` §2's frames do not carry
(they export only `c'.env = c.env`): the first assert compares against the *reader's* `lparams`. -/

/-- `read` in statement position: `AddInductive.M = ReaderT Context (Except Exception)`, so the
bind is a substitution and the rule is `rfl`.  `InductMap.lean` §2's frames discard the read value
(`M.WF.bind_triv`), which is not enough here: the first `assert!` compares `stats.levels.length`
against the **read** context's `lparams`. -/
theorem WF_read_bind {c : Context} {f : Context → M α} {Q : α → Prop}
    (h : (f c).WF c Q) : ((read : M Context) >>= f).WF c Q :=
  M.WF.bind (M.WF.read (Q := (· = c)) rfl) fun _ ha => ha ▸ h

/-- `withLocalDecl` moves `lctx` and `ngen` only, so `lparams` frames exactly as `env` does. -/
theorem withLocalDecl_frame' {c : Context} {name : Name} {bi : BinderInfo} {ty : Expr}
    {k : Expr → M α} {Q : α → Prop}
    (H : ∀ c' : Context, c'.env = c.env → c'.lparams = c.lparams →
      (k (.fvar ⟨c.ngen.curr⟩)).WF c' Q) :
    (withLocalDecl name bi ty k).WF c Q := H _ rfl rfl

/-- **The inner telescope loop's invariant** (`Inductive/Add.lean`:211-236).  `nindices`, `indConsts`
and `levels` are untouched along it; `params` is pushed once per parameter binder, but *only* while
`indConsts` is empty — for every member after the first the loop instead *reads* `params[i]!` and
`params` is already full.  Hence the two `params` clauses, whose disjunction at `i = nparams` is the
fourth `assert!`. -/
structure LoopInv (np nl : Nat) (A : Array Nat) (C : Array Expr)
    (s : InductiveStats) (i : Nat) : Prop where
  nind : s.nindices = A
  icst : s.indConsts = C
  lev : s.levels.length = nl
  parE : s.indConsts.isEmpty = true → s.params.size = i
  parN : s.indConsts.isEmpty = false → s.params.size = np

/-- At the loop's exit `i = nparams`, so both `params` clauses deliver the same conclusion: the
fourth `assert!`. -/
theorem LoopInv.params_eq {np nl A C s} (h : LoopInv np nl A C s np) : s.params.size = np := by
  cases hE : s.indConsts.isEmpty
  · exact h.parN hE
  · exact h.parE hE

/-- The inner telescope loop of `checkInductiveTypes`, with `LoopInv` carried to the continuation. -/
theorem WF_checkInductiveTypes_loop_inv {c : Context} {Q : α → Prop} {np nl : Nat}
    {A : Array Nat} {C : Array Expr} {kk : Expr → InductiveStats → Nat → M α}
    (H : ∀ t s n (c' : Context), LoopInv np nl A C s np →
      c'.env = c.env → c'.lparams = c.lparams → (kk t s n).WF c' Q) :
    ∀ (fuel : Nat) (stats : InductiveStats) (type : Expr) (i ni : Nat) (c' : Context),
      LoopInv np nl A C stats i → c'.env = c.env → c'.lparams = c.lparams →
      (checkInductiveTypes.loopInd.loop np stats type i ni fuel kk).WF c' Q := by
  intro fuel
  induction fuel with
  | zero => intro stats type i ni c' hI hc hl; exact M.WF.throw
  | succ fuel ih =>
    intro stats type i ni c' hI hc hl
    rw [checkInductiveTypes.loopInd.loop.eq_def]
    split
    · exact M.WF.throw
    · next fuel' heq =>
      obtain rfl : fuel' = fuel := (Nat.succ.inj heq).symm
      split
      · split
        · split
          · next hE =>
            refine M.WF.bind_triv fun dom' => withLocalDecl_frame' fun c'' hc'' hl'' => ?_
            refine M.WF.bind_triv fun _ => ih _ _ _ _ _ ?_ (hc''.trans hc) (hl''.trans hl)
            refine ⟨hI.nind, hI.icst, hI.lev, fun _ => ?_, fun hE' => absurd hE' (by simp [hE])⟩
            simp only [Array.size_push, hI.parE hE]
          · next hE =>
            refine M.WF.bind_triv fun _ => M.WF.bind_triv fun _ => ?_
            split
            · refine M.WF.bind_triv fun _ => ih _ _ _ _ _ ?_ hc hl
              exact ⟨hI.nind, hI.icst, hI.lev, fun hE' => absurd hE' (by simp [hE]), hI.parN⟩
            · exact WF_throw_bind M.WF.throw
        · refine M.WF.bind_triv fun dom' => withLocalDecl_frame' fun c'' hc'' hl'' => ?_
          exact M.WF.bind_triv fun _ => ih _ _ _ _ _ hI (hc''.trans hc) (hl''.trans hl)
      · split
        · exact WF_throw_bind M.WF.throw
        · next hne =>
          obtain rfl : i = np := by simpa using hne
          exact H _ _ _ _ hI hc hl

/-- **The member loop's invariant.**  `nindices` and `indConsts` are pushed in lockstep, one entry per
member (`Inductive/Add.lean`:247-249), so both sizes are `dIdx`; `levels` is set once, before the loop;
and `params` is empty until the first member fills it to `nparams`.  Carrying `dIdx ≤ indTypes.size`
alongside is what turns the exit condition `¬ dIdx < indTypes.size` into an *equality*, and
`0 < indTypes.size` is what makes the fourth `assert!` hold at the exit — for an **empty** block the
loop exits at `dIdx = 0` with `params.size = 0`, so `params.size == nparams` genuinely fails whenever
`nparams ≠ 0` and the delivered stats is then the panic value (see §2's `WF_run_member`, which splits
on `its = []` and finds its goal vacuous there). -/
theorem WF_checkInductiveTypes_loopInd_inv {c : Context} {Q : α → Prop} {np : Nat}
    {its : Array InductiveType} {k : InductiveStats → M α}
    (H : ∀ stats (c' : Context), stats.nindices.size = its.size → c'.env = c.env →
      c'.lparams = c.lparams → (k stats).WF c' Q) :
    ∀ (m dIdx : Nat) (stats : InductiveStats) (c' : Context), its.size - dIdx ≤ m →
      dIdx ≤ its.size → 0 < its.size →
      stats.nindices.size = dIdx → stats.indConsts.size = dIdx →
      stats.levels.length = c.lparams.length →
      (stats.indConsts.isEmpty = true → stats.params.size = 0) →
      (stats.indConsts.isEmpty = false → stats.params.size = np) →
      c'.env = c.env → c'.lparams = c.lparams →
      (checkInductiveTypes.loopInd np its k dIdx stats).WF c' Q := by
  intro m
  induction m with
  | zero =>
    intro dIdx stats c' hm hle hpos hni hic hlev hpE hpN hc hl
    rw [checkInductiveTypes.loopInd.eq_def]
    split
    · next hlt => exact absurd hlt (by omega)
    · next hlt =>
      obtain rfl : dIdx = its.size := by omega
      have hp : stats.params.size = np := hpN (by
        rw [Array.isEmpty_eq_false_iff_exists_mem]
        exact ⟨stats.indConsts[0], Array.getElem_mem (by omega)⟩)
      refine WF_read_bind ?_
      rw [hl]
      simp only [hlev, hni, hic, hp, beq_self_eq_true, if_true]
      exact H _ _ hni hc hl
  | succ m ih =>
    intro dIdx stats c' hm hle hpos hni hic hlev hpE hpN hc hl
    rw [checkInductiveTypes.loopInd.eq_def]
    split
    · next hlt =>
      repeat refine M.WF.bind_triv fun _ => ?_
      refine WF_checkInductiveTypes_loop_inv (c := c) (nl := c.lparams.length)
        (A := stats.nindices) (C := stats.indConsts)
        (fun t s n c'' hI hc'' hl'' => ?_) _ _ _ _ _ _ ⟨rfl, rfl, hlev, hpE, hpN⟩ hc hl
      have hsni : s.nindices.size = dIdx := by rw [hI.nind]; exact hni
      have hsic : s.indConsts.size = dIdx := by rw [hI.icst]; exact hic
      have hsp : s.params.size = np := hI.params_eq
      repeat refine M.WF.bind_triv fun _ => ?_
      try dsimp only
      split
      · refine M.WF.bind_triv fun _ => ?_
        refine ih (dIdx + 1) _ _ (by omega) (by omega) hpos ?_ ?_ hI.lev ?_ ?_ hc'' hl''
        · show (s.nindices.push n).size = dIdx + 1
          rw [Array.size_push, hsni]
        · show (s.indConsts.push _).size = dIdx + 1
          rw [Array.size_push, hsic]
        · intro hE; simp at hE
        · intro _; exact hsp
      · split
        · exact WF_throw_bind M.WF.throw
        · refine ih (dIdx + 1) _ _ (by omega) (by omega) hpos ?_ ?_ hI.lev ?_ ?_ hc'' hl''
          · show (s.nindices.push n).size = dIdx + 1
            rw [Array.size_push, hsni]
          · show (s.indConsts.push _).size = dIdx + 1
            rw [Array.size_push, hsic]
          · intro hE; simp at hE
          · intro _; exact hsp
    · next hlt =>
      obtain rfl : dIdx = its.size := by omega
      have hp : stats.params.size = np := hpN (by
        rw [Array.isEmpty_eq_false_iff_exists_mem]
        exact ⟨stats.indConsts[0], Array.getElem_mem (by omega)⟩)
      refine WF_read_bind ?_
      rw [hl]
      simp only [hlev, hni, hic, hp, beq_self_eq_true, if_true]
      exact H _ _ hni hc hl

/-- **`checkInductiveTypes` hands its continuation the array-size equality its own `assert!`
asserts** (`Inductive/Add.lean`:254), for any non-empty block. -/
theorem WF_checkInductiveTypes_ni {c : Context} {Q : α → Prop} {np : Nat}
    {its : Array InductiveType} {k : InductiveStats → M α} (hpos : 0 < its.size)
    (H : ∀ stats (c' : Context), stats.nindices.size = its.size → c'.env = c.env →
      c'.lparams = c.lparams → (k stats).WF c' Q) :
    (checkInductiveTypes np its k).WF c Q := by
  rw [checkInductiveTypes]
  refine WF_read_bind ?_
  refine WF_checkInductiveTypes_loopInd_inv H its.size 0 _ c (by omega) (by omega) hpos
    rfl rfl (by simp) (fun _ => rfl) ?_ rfl rfl
  intro h
  exact absurd h (by simp; rfl)

/-- **The limit of §1, and why it is a limit rather than a bug.**  At an empty block the member loop
exits at `dIdx = 0` with `params` still empty, so the *fourth* `assert!`'s condition is `false` for
every `nparams ≠ 0` — this is that condition.  What then reaches the continuation is `panicCore`, an
`opaque` with no body, so no equation about its `nindices` is provable: at `its = #[]` the target
statement is **unprovable**, not false (the runtime value of the panic is `default`, whose `nindices`
is `#[]`, so it is very likely true — just not derivable).  Hence `0 < its.size` in
`WF_checkInductiveTypes_ni`, and hence §2's split on `its = []`. -/
theorem params_assert_fails_at_empty {np : Nat} (h : np ≠ 0) :
    ((default : InductiveStats).params.size == np) = false := by
  have h0 : (default : InductiveStats).params.size = 0 := rfl
  rw [h0]
  simpa using Ne.symm h

/-! ## §2 What the equality buys: `RunFreshGate.member`

`AddInductive.M.WF.declareInductiveTypes` (`DeclareStages.lean`:166) already carries the per-member
freshness clause `c.env.find? t.name = none`, but **guarded** by
`indTypes[j]? = some t → stats.nindices[j]? = some ni` — the second guard being exactly the `zipWith`
truncation of `Inductive/Add.lean`:289.  §1's equality is what discharges it. -/

/-- **`RunFreshGate.member`, proved.**  Every member name of the block is absent from the input
environment whenever `AddInductive.run` accepts.  `its = []` is handled first: there the conclusion is
vacuous, which is precisely why §1's `0 < its.size` hypothesis costs nothing here. -/
theorem WF_run_member {c : Context} (mapWF : c.env.constants.WF) (np : Nat)
    (its : List InductiveType) (nn : Nat) :
    (run np its nn).WF c fun _ => ∀ t ∈ its, c.env.find? t.name = none := by
  rcases its with _ | ⟨t0, rest⟩
  · exact fun _ _ t ht => absurd ht (by simp)
  · have hpos : 0 < (t0 :: rest).toArray.size := by simp
    rw [run]
    -- exactly three binds precede `checkInductiveTypes` (`(← read).safety`, `let {lparams,..} ← read`,
    -- `checkDuplicatedUnivParams`); a `repeat` here would eat `checkInductiveTypes`' own `read` and
    -- with it the identification of the reader's `lparams` with `c`'s, which assert (1) needs.
    refine M.WF.bind_triv fun _ => M.WF.bind_triv fun _ => M.WF.bind_triv fun _ => ?_
    refine WF_checkInductiveTypes_ni (c := c) hpos (fun stats c₁ hsz h₁ hl₁ => ?_)
    refine M.WF.bind (Q := fun _ => ∀ t ∈ t0 :: rest, c.env.find? t.name = none) ?_
      (fun _ h => fun _ _ => h)
    intro e₁ he
    have h := AddInductive.M.WF.declareInductiveTypes (c := c₁) (by rw [h₁]; exact mapWF)
      stats np (t0 :: rest).toArray nn _ e₁ he
    intro t ht
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.1 hj
    have hj' : (t0 :: rest).toArray[j]? = some t := by rw [List.getElem?_toArray]; exact hj
    have hjlt' : j < stats.nindices.size := by
      rw [hsz]; simpa using hjlt
    have hni : stats.nindices[j]? = some stats.nindices[j] := Array.getElem?_eq_getElem hjlt'
    have := (h.2 j t _ hj' hni).1
    rw [← h₁]; exact this

/-! ## §3 `RunFreshGate.ctor`

`NestedRebuild.lean` §5's grading is confirmed: the constructor half needs **nothing** of §1 —
`AddInductive.M.WF.declareConstructors`' freshness clause is guarded only by `indTypes[j]? = some t`,
with no `nindices` companion, so the plain frame from `InductMap.lean` suffices.  What it needs
instead is a *descent*: `declareConstructors` reports freshness in the environment **it** starts from,
which is the post-`declareInductiveTypes` `e₁`, not `c.env`.  `AddInductive.M.WF.declareInductiveTypes`
discards the `hother` clause of `r113e_addLoop_WF`, so the descent is proved here from that loop rule
directly. -/

/-- **`declareInductiveTypes` only adds.**  A name absent from its output was absent from its input:
the fourth clause of `r113e_addLoop_WF` for names off the member list, and its third clause (which
says an on-list name is `some`) for the rest. -/
theorem WF_declareInductiveTypes_mono {c : Context} (mapWF : c.env.constants.WF)
    (stats : InductiveStats) (numParams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) :
    (declareInductiveTypes stats numParams indTypes numNested isUnsafe).WF c
      fun env' => env'.constants.WF ∧ ∀ n, env'.find? n = none → c.env.find? n = none := by
  intro env' hok
  rw [r113e_declareInductiveTypes_eq, ← Array.foldlM_toList] at hok
  obtain ⟨hwf', -, hsome, hother⟩ :=
    r113e_addLoop_WF (α := InductiveVal) (g := .inductInfo) c.allowPrimitive
      (xs := (r113eIndInfos c.lparams numParams numNested isUnsafe stats indTypes).toList)
      mapWF env' hok
  refine ⟨hwf', fun n hn => ?_⟩
  by_cases hmem : ∃ v ∈ (r113eIndInfos c.lparams numParams numNested isUnsafe stats
      indTypes).toList, (ConstantInfo.inductInfo v).name = n
  · obtain ⟨v, hv, rfl⟩ := hmem
    rw [hsome v hv] at hn; exact absurd hn nofun
  · rw [← hother n fun v hv he => hmem ⟨v, hv, he⟩]; exact hn

/-- **`RunFreshGate.ctor`, proved.** -/
theorem WF_run_ctor {c : Context} (mapWF : c.env.constants.WF) (np : Nat)
    (its : List InductiveType) (nn : Nat) :
    (run np its nn).WF c fun _ => ∀ t ∈ its, ∀ ct ∈ t.ctors, c.env.find? ct.name = none := by
  rw [run]
  repeat refine M.WF.bind_triv fun _ => ?_
  refine WF_checkInductiveTypes_loopInd (c := c) (fun stats c₁ h₁ => ?_)
    its.toArray.size 0 _ c (by omega) rfl
  refine M.WF.bind (Q := fun e₁ => e₁.constants.WF ∧
    ∀ n, e₁.find? n = none → c.env.find? n = none) ?_ fun e₁ h₁' => ?_
  · intro e₁ he
    have h := WF_declareInductiveTypes_mono (c := c₁) (by rw [h₁]; exact mapWF)
      stats np its.toArray nn _ e₁ he
    rw [h₁] at h; exact h
  · refine M.WF.withReader ?_
    refine M.WF.bind_triv fun _ => ?_
    refine M.WF.bind (Q := fun _ => ∀ t ∈ its, ∀ ct ∈ t.ctors, c.env.find? ct.name = none) ?_
      (fun _ h => fun _ _ => h)
    intro e₂ he
    have h := AddInductive.M.WF.declareConstructors (c := { c₁ with env := e₁ }) h₁'.1
      stats its.toArray _ e₂ he
    intro t ht ct hct
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hct
    have hj' : its.toArray[j]? = some t := by rw [List.getElem?_toArray]; exact hj
    exact h₁'.2 _ (h.2 j t hj' q ct hq).1

/-! ## §4 `RunFreshGate.ctors`

The third field needs §1 again (the stored `InductiveVal` comes from the same `zipWith`), **plus** a
value-preservation walk over everything `run` does afterwards: `declareConstructors` and the recursor
loop each `checkName`-then-`add`, and a name they add is fresh in the environment they add it to,
whereas a member name is already `some` there — so the two names differ and `r113e_find?_add_ne`
applies.  That is the whole argument; the rest is the same plumbing as `InductMap.lean`'s `WF_run`. -/

/-- The member entries of the block, pinned with the one field `RunFreshGate.ctors` asks about. -/
def CtorsPinned (its : List InductiveType) (env : Environment) : Prop :=
  ∀ t ∈ its, ∃ ind : InductiveVal, env.find? t.name = some (.inductInfo ind) ∧
    ind.ctors = t.ctors.map (·.name)

/-- An `add` at a name the environment does not yet have cannot disturb a member entry, because a
member entry's key *is* had. -/
theorem CtorsPinned.add {its : List InductiveType} {env : Environment} {ci : ConstantInfo}
    {n : Name} (mapWF : env.constants.WF) (h : CtorsPinned its env) (hn : ci.name = n)
    (hfresh : env.find? n = none) : CtorsPinned its (env.add ci) := by
  subst hn
  intro t ht
  obtain ⟨ind, hf, hc⟩ := h t ht
  refine ⟨ind, ?_, hc⟩
  rw [r113e_find?_add_ne mapWF hfresh (n := t.name) ?_]
  · exact hf
  · intro he; rw [he, hf] at hfresh; exact absurd hfresh nofun

theorem CtorsPinned.mono {its : List InductiveType} {e env : Environment}
    (h : CtorsPinned its e) (hp : ∀ n v, e.find? n = some v → env.find? n = some v) :
    CtorsPinned its env := fun t ht =>
  let ⟨ind, hf, hc⟩ := h t ht; ⟨ind, hp _ _ hf, hc⟩

/-- `declareConstructors` preserves every entry it starts with: the names it adds are fresh in that
starting environment (its second clause), so they differ from any name that is not. -/
theorem WF_declareConstructors_pres {c : Context} (mapWF : c.env.constants.WF)
    (stats : InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool) :
    (declareConstructors stats indTypes isUnsafe).WF c fun env' =>
      env'.constants.WF ∧ ∀ n v, c.env.find? n = some v → env'.find? n = some v := by
  intro env' hok
  rw [r113e_declareConstructors_eq] at hok
  obtain ⟨hwf', hnone, -, hother⟩ := r113e_ctorOuter_WF mapWF env' hok
  refine ⟨hwf', fun n v hv => ?_⟩
  rw [hother n ?_, hv]
  intro t ht ctor hct he
  have h0 := hnone t ht ctor hct
  rw [he, hv] at h0
  exact absurd h0 nofun

/-- **`RunFreshGate.ctors`, proved.** -/
theorem WF_run_ctors {c : Context} (mapWF : c.env.constants.WF) (np : Nat)
    (its : List InductiveType) (nn : Nat) :
    (run np its nn).WF c fun env' => ∀ t ∈ its, ∀ ind : InductiveVal,
      env'.find? t.name = some (.inductInfo ind) → ind.ctors = t.ctors.map (·.name) := by
  rcases its with _ | ⟨t0, rest⟩
  · exact fun _ _ t ht => absurd ht (by simp)
  · have hpos : 0 < (t0 :: rest).toArray.size := by simp
    have key : ∀ env' : Environment, CtorsPinned (t0 :: rest) env' →
        ∀ t ∈ t0 :: rest, ∀ ind : InductiveVal,
          env'.find? t.name = some (.inductInfo ind) → ind.ctors = t.ctors.map (·.name) := by
      intro env' hp t ht ind hf
      obtain ⟨ind', hf', hc'⟩ := hp t ht
      rw [hf'] at hf
      cases hf
      exact hc'
    rw [run]
    refine M.WF.bind_triv fun _ => M.WF.bind_triv fun _ => M.WF.bind_triv fun _ => ?_
    refine WF_checkInductiveTypes_ni (c := c) hpos (fun stats c₁ hsz h₁ hl₁ => ?_)
    refine M.WF.bind (Q := fun e₁ => e₁.constants.WF ∧ CtorsPinned (t0 :: rest) e₁) ?_
      fun e₁ h₁' => ?_
    · intro e₁ he
      have h := AddInductive.M.WF.declareInductiveTypes (c := c₁) (by rw [h₁]; exact mapWF)
        stats np (t0 :: rest).toArray nn _ e₁ he
      refine ⟨h.1, fun t ht => ?_⟩
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ht
      obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.1 hj
      have hj' : (t0 :: rest).toArray[j]? = some t := by rw [List.getElem?_toArray]; exact hj
      have hjlt' : j < stats.nindices.size := by rw [hsz]; simpa using hjlt
      exact ⟨_, (h.2 j t _ hj' (Array.getElem?_eq_getElem hjlt')).2, rfl⟩
    · refine M.WF.withReader ?_
      refine M.WF.bind_triv fun _ => ?_
      refine M.WF.bind (Q := fun e₂ => e₂.constants.WF ∧ CtorsPinned (t0 :: rest) e₂) ?_
        fun e₂ h₂' => ?_
      · intro e₂ he
        have h := WF_declareConstructors_pres (c := { c₁ with env := e₁ }) h₁'.1
          stats (t0 :: rest).toArray _ e₂ he
        exact ⟨h.1, h₁'.2.mono h.2⟩
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
          (Inv := fun env => env.constants.WF ∧ CtorsPinned (t0 :: rest) env) ?_
          (he ▸ h₃ ▸ h₂')) fun env' hI => SM.WF.pure (key _ hI.2)
        intro dIdx hmem env hInv
        try dsimp only
        refine SM.WF.bind (Q := fun _ => True) (fun _ _ _ _ => trivial) fun _ _ => ?_
        refine SM.WF.bind (SM_checkName hInv.1 _ _) fun _ hfr => ?_
        exact SM.WF.pure ⟨_, rfl, r113e_constants_wf_add hInv.1 hfr,
          hInv.2.add hInv.1 rfl hfr⟩

end AddInductive

end Lean4Lean
