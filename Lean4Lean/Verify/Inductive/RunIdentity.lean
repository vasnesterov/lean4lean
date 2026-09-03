import Lean4Lean.Verify.Inductive.NestedRunInvariant

/-!
# `ElimNestedInductive.run` is the identity on `types` — and the premise that costs

`Verify/Inductive/AddInductiveStep.lean` §6 leaves the residue `AddInductiveRunRealises`, which
still mentions `ElimNestedInductive`: `AddInductive.run` is applied to `res.types`, while
`TrIndDecl` speaks of the input `types`, and the file records `res.types = types` as "looks
provable" and the way to remove `ElimNestedInductive` from the residue entirely.

**It is provable, and it is proved here** (`ElimNestedInductive.run_types_eq`,
`run_run'_types`), from two premises:

| premise | supplied by |
| --- | --- |
| `∀ n v, env.find? n ≠ some (.inductInfo v)` | `VEnvs.WF.find?_ne_inductInfo`, i.e. by `ves.WF env` |
| `BlockNoFVar types` — no fvars/mvars in a constructor type | **`Environment.addInductive`'s own guard loop** (§6, `guardLoop_blockNoFVar`) |
| `BlockClosed types` — no *loose bound variables* in a constructor type | **the same guard loop, since 2026-09-01** (§6, `checkNoLooseBVars`) |
| `BlockClosedMembers types` — nor in a *member's own* type | ditto (§6) |

§4 turns that into `AddInductiveRunRealisesClosed`: the residue with no `res`, no run-success
equation and no `ElimNestedInductive`, and §7 chains it to `AddInductiveStepWFClosed`.

## The finding: the missing premise is not a proof artefact

`AddInductiveStepWF` and `AddInductiveRunRealises` — as `AddInductiveStep.lean` states them, with
no closedness premise — are **false**.  §5 is the refutation and it is a witness, not an
obstruction argument:

* `LooseBVarWitness.fooBad` is `inductive Foo (α : Type) | mk : ∀ (α : Type) (x : #1), Foo #1`,
  whose constructor type has `looseBVarRange = 1`.
* `withParams` lowers that `#1` to `#0`; `LocalContext.mkForall` restores the binder with the
  real `Expr.abstract`, which **leaves bound variables untouched** — so the loose variable is
  **captured** by the parameter binder and the output is `∀ (α : Type), α → Foo α`, closed and
  perfectly ordinary.
* `Environment.addInductive` therefore **accepts** the block and stores a constructor type that
  is not the one it was given (machine-observed by §5.1's second `#eval`, at
  `Kernel.Environment.empty`, where `ves.WF env` is inhabited by `Bridge.hasEmptyModel`).
* But `TrIndDecl`/`TrIndDeclN` require `TrExprS venv Us [] c.type _`, which forces
  `c.type.looseBVarRange' = 0` (`trExprS_looseBVarRange_nil`).  So no `D` translates the *input*
  block, and `AddInductPost env env' ves [] 1 [fooBad]` is false for **every** `ves'` and
  `numNested` (`not_addInductPost_of_looseBVar`).

Hence `not_addInductiveStepWF` and `not_addInductiveRunRealises`.  Consequences:

1. The closedness premise is needed for **truth**, not merely for provability — so of the three
   options "(a) add it as a premise / (b) recover it from `AddInductive.run`'s success / (c)
   neither works", the answer is **(a), and (a) is forced**.
2. **(b) is refuted, not merely doubtful.**  The only thing the output side can give is
   closedness of `res.types`, and at this witness `res.types` **is** closed
   (`LooseBVarWitness.fooGood_closed`) while `types` is not (`fooBad_not_closed`).  So no
   strengthening of what `checkConstructors` establishes recovers the premise.
3. Whoever installs the premise must carry it up through `AddDeclPost`/`addDecl.WF`, or the
   implementation must reject such blocks.

**Resolved, 2026-09-01, by the second route.**  `Verify/ClosednessPropagation.lean` measured the
first: as a premise the condition reaches `Lean4Lean.kernel_sound`'s **frozen** statement and
narrows it.  The guard changes no statement anywhere, because `Except.WF` holds vacuously of a
rejection.  So `Environment.addInductive`'s pre-`run` guard loop now calls `checkNoLooseBVars` on
each member's own type and each constructor's, §6 exposes that as `addInductive_WF_blockClosed`,
and `ClosednessPropagation`'s `addInductiveStepWF_of_closed` recovers the **unrestricted**
`AddInductiveStepWF` from `AddInductiveStepWFClosed`.

What that does *not* do: prove anything.  §5's refutation theorems stay, as true implications
whose acceptance hypothesis is now unsatisfiable; `AddInductiveStepWFClosed` and
`AddInductiveRunRealisesClosed` are open exactly as before.  The gain is confined to *not* having
to narrow a frozen statement.  It is also a **restrictive divergence from the C++ kernel**, which
accepts these blocks and silently reinterprets them — see `divergences.md`.

## Two corrections to the received account

* "at a block whose constructor type carries a loose bvar, `run` is not the identity …
  **and both kernels reject via the type checker**" — the first half is right, the second is
  **false in exactly the interesting sub-case**.  When the loose index is small enough to be
  captured by one of the `np` parameter binders, the output is closed and *accepted*; that is
  `fooBad`.  The rejecting case is `fooFar` (index beyond `np`), also checked by the `#eval`.
  This distinction is what makes the refutation above possible.
* The *capture* is still **not a C++ divergence**: `kernel/abstract.cpp`'s `abstract` rewrites
  only `fvar`/`mvar` nodes (and returns `e` unchanged when `!has_fvar(e)`), and
  `kernel/inductive.cpp`'s `elim_nested_inductive_fn::operator()` performs the same
  unconditional `get_params` / `replace_all_nested` / `lctx.mk_pi(As, ·)` round trip on every
  constructor of every block, with `check_no_metavar_no_fvar` as the only pre-pass.  So C++
  captures identically.  The *guard* of §6 is a divergence — in the restrictive direction, since
  C++ accepts what lean4lean now rejects — and belongs in `divergences.md`.

## Frozen axioms

Measured by `#print axioms`, not by grep.  **No declaration here carries `sorryAx`.**  Two
disjoint frozen sets are reached:

* the identity chain (`mkForall_push_mkLocalDecl`, `MWF.withParams_id`, `run_loop_id`,
  `run_types_eq`, `run_run'_types`, `addInductiveRunRealises_of_closed`,
  `mkForall_push_degenerate`) reaches `Lean.Expr.abstract_eq`, `Lean.Expr.abstractRange_eq`,
  `Lean.Expr.hasLooseBVar_eq`, `Lean.Expr.instantiate1_eq`, `Lean.Expr.lowerLooseBVars_eq` —
  through `Lean4Lean.LocalContext.mkForall_list` → `mkBinding_eq`, exactly as
  `withParams_mkForall_eq` and `QuotConsts.lean` already do;
* the guard-loop lemmas that mention fvars (`guardLoop_ctors`, `guardLoop_blockNoFVar`,
  `addInductive_WF_blockClosedFull`, `addInductive_WF_of_run'`) reach
  `Lean.Expr.mkAppData_eq`, `Lean.Expr.mkData_eq`, `Lean.Level.hasMVar_eq` — through
  `checkNoMVarNoFVar.WF`'s `hasFVar`/`hasMVar` bridging, exactly as before the guard was added;
* the **closedness half reaches nothing**: `looseBVarRange'_le_of_noLooseBVars`,
  `checkNoLooseBVars.WF`, `guardLoop_ctors_closed`, `guardLoop_blockClosed` and
  `addInductive_WF_blockClosed` (§6.1) are all `[propext, Classical.choice, Quot.sound]`, and so
  therefore are `ClosednessPropagation`'s `rejectsNonClosed`, `rejectsNonClosedFull`,
  `addInductiveStepWF_of_closed` and `addInductiveStepWF_of_full`.  That is the whole point of
  `noLooseBVars` being a pure structural recursion rather than a read of the cached
  `Expr.looseBVarRange` header field: had it read the field, `Expr.looseBVarRange_eq`'s
  `BVarBounded` side condition — resting on the frozen `Lean.Expr.mkData_eq` — would have entered
  the *hypothesis* of `RejectsNonClosed`, where no instrument in this repo would see it, since
  they all look at conclusions;
* `addInductiveStepWFClosed_of_run` reaches all eight, and nothing else.

All eight are on `Verify/Guard.lean`'s `frozenAxioms` list and all eight already have users, so
**no axiom use is new and the list is not enlarged**.  The refutation side
(`not_addInductiveStepWF`, `not_addInductiveRunRealises`, `not_addInductPost_of_looseBVar`, …)
uses **no frozen axiom at all**: `[propext, Classical.choice, Quot.sound]`.

`abstract_eq`'s side condition `looseBVarRange' = 0` *is* the missing premise: the axiom is what
makes closedness load-bearing, and `fooBad` is precisely a point where the axiom does not apply
and the real `abstract` disagrees with the model `abstractList` (which shifts loose bvars rather
than capturing them).  That is also why the acceptance of `fooBad` can only be *executed*, never
proved by `rfl`: `Expr.abstract` is `opaque`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. The one-step `mkForall` lemma -/

open Lean4Lean.LocalContext in
theorem foldr_mkBindingList1_congr {lctx₁ lctx₂ : LocalContext} {isLambda : Bool}
    {fvs : List FVarId} (H : ∀ x ∈ fvs, lctx₁.find? x = lctx₂.find? x) (b : Expr) :
    fvs.foldr (fun a e => mkBindingList1 isLambda lctx₁ [] a (e.abstract1 a)) b =
    fvs.foldr (fun a e => mkBindingList1 isLambda lctx₂ [] a (e.abstract1 a)) b := by
  induction fvs with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun x hx => H x (List.mem_cons_of_mem _ hx)),
      mkBindingList1_congr (H a List.mem_cons_self)]

/-- **One binder of `withParams`, undone.**  `withParams` replaces
`.forallE name dom body bi` by `body.instantiate1 (.fvar fv)` and records `fv : dom` in the
local context; `mkForall` over the extended context and the pushed parameter array puts the
binder back — *provided the type is loose-bvar-free*, which is the side condition of the frozen
axiom `Expr.abstract_eq` that `mkForall`'s `Expr.abstract` call needs. -/
theorem mkForall_push_mkLocalDecl {lctx : LocalContext} {fv : FVarId}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {ps : Array Expr} {fvs : List FVarId}
    (hps : ps.toList = fvs.map .fvar) (hnd : fvs.Nodup) (hfv : fv ∉ fvs)
    (hwf : Lean4Lean.LocalContext.WF lctx)
    (hfind : lctx.find? fv = none)
    (hlc : ∀ x ∈ fvs, ∀ d, lctx.find? x = some d →
      d.type.looseBVarRange' = 0 ∧ ∀ v ∈ d.value? true, v.looseBVarRange' = 0)
    (hex : ∀ x ∈ fvs, ∃ d, lctx.find? x = some d)
    (hty : (Expr.forallE name dom body bi).looseBVarRange' = 0)
    (hbfv : FVarsIn (· ≠ fv) body) :
    (lctx.mkLocalDecl fv name dom bi).mkForall (ps.push (.fvar fv))
        (body.instantiate1 (.fvar fv))
      = lctx.mkForall ps (.forallE name dom body bi) := by
  have hdom : dom.looseBVarRange' = 0 := by
    simp only [Expr.looseBVarRange', Nat.max_eq_zero_iff] at hty; omega
  have hbody : body.looseBVarRange' ≤ 1 := by
    simp only [Expr.looseBVarRange', Nat.max_eq_zero_iff] at hty; omega
  have hbi : (body.instantiate1 (Expr.fvar fv)).looseBVarRange' = 0 := by
    rw [Expr.instantiate1_eq]
    have := Expr.instantiate1'_looseBVarRange (e := body) (a := .fvar fv) (n := 0) (k := 0)
      (by simpa using hbody) (by simp [Expr.looseBVarRange'])
    omega
  have hpsE : ps = ⟨fvs.map (.fvar ·)⟩ := by cases ps; simpa using hps
  have hpush : (ps.push (Expr.fvar fv)) = ⟨(fvs ++ [fv]).map (.fvar ·)⟩ := by
    rw [hpsE]; simp
  have hnd' : (fvs ++ [fv]).Nodup := ElimNestedInductive.nodup_append_singleton hnd hfv
  have hfind' : ∀ x, (lctx.mkLocalDecl fv name dom bi).find? x =
      if x == fv then some (.cdecl lctx.decls.size fv name dom bi .default)
      else lctx.find? x := fun _ => LocalContext.find?_mkLocalDecl hwf hfind
  have hne : ∀ x ∈ fvs, (lctx.mkLocalDecl fv name dom bi).find? x = lctx.find? x := by
    intro x hx
    rw [hfind', if_neg (by simp; rintro rfl; exact hfv hx)]
  have hlc' : ∀ x ∈ fvs ++ [fv], ∀ d, (lctx.mkLocalDecl fv name dom bi).find? x = some d →
      d.type.looseBVarRange' = 0 ∧ ∀ v ∈ d.value? true, v.looseBVarRange' = 0 := by
    intro x hx d hd
    rcases List.mem_append.1 hx with h | h
    · exact hlc x h d (by rwa [hne x h] at hd)
    · simp only [List.mem_singleton] at h; subst h
      rw [hfind', if_pos (by simp)] at hd
      cases hd; exact ⟨hdom, by simp [Lean.LocalDecl.value?]⟩
  have hex' : ∀ x ∈ fvs ++ [fv], ∃ d, (lctx.mkLocalDecl fv name dom bi).find? x = some d := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨d, hd⟩ := hex x h; exact ⟨d, by rw [hne x h, hd]⟩
    · simp only [List.mem_singleton] at h; subst h
      exact ⟨_, by rw [hfind', if_pos (by simp)]⟩
  rw [hpush, LocalContext.mkForall_list hbi hnd' hlc' hex',
    hpsE, LocalContext.mkForall_list hty hnd hlc hex,
    List.foldr_append]
  have key : List.foldr (fun a e => LocalContext.mkBindingList1 false
        (lctx.mkLocalDecl fv name dom bi) [] a (Expr.abstract1 a e))
      (body.instantiate1 (Expr.fvar fv)) [fv] = Expr.forallE name dom body bi := by
    simp only [List.foldr_cons, List.foldr_nil]
    rw [show Expr.abstract1 fv (body.instantiate1 (Expr.fvar fv)) = body from by
      rw [Expr.instantiate1_eq]; exact FVarsIn.abstract_instantiate1 hbfv]
    rw [LocalContext.mkBindingList1, hfind', if_pos (by simp)]
    rfl
  rw [key]
  exact foldr_mkBindingList1_congr hne _

/-! ## 2. `withParams` hands its continuation the inverse equation -/

namespace ElimNestedInductive

variable {α : Type} {env : Environment}

/-- **`withParams` is invertible by `mkForall`.**  Same shape as
`MWF.withParams_fvars` (`Verify/Inductive/NestedRunInvariant.lean` §7), with one extra fact for
the continuation: `lctx.mkForall ps t` is the `type` it started from.

Both side conditions are load-bearing and neither is supplied by `Environment.addInductive`'s
pre-`run` guard loop for a constructor type:

* `hcl` — loose-bvar-freeness — is the side condition of the frozen axiom `Expr.abstract_eq`,
  and it is **false** at the witnesses of §5;
* `hfv` — no free variables and no metavariables — *is* supplied, by
  `Environment.checkNoMVarNoFVar` (`checkNoMVarNoFVar.WF` returns exactly
  `e.FVarsIn fun _ => False`). -/
theorem MWF.withParams_id {k : LocalContext → Expr → Array Expr → M α} {I : State → Prop}
    {Q : α → State → Prop}
    (hng : ∀ s, I s → I { s with ngen := s.ngen.next }) (n : Nat) (type : Expr)
    (hcl : type.looseBVarRange' = 0) (hfv : FVarsIn (fun _ => False) type)
    (hk : ∀ lctx t (ps : Array Expr), ps.size = n → lctx.mkForall ps t = type →
      MWF env I (k lctx t ps) Q) :
    MWF env I (withParams type n k) Q := by
  have hempty : ({} : LocalContext).mkForall #[] type = type := by
    have h := LocalContext.mkForall_list (lctx := ({} : LocalContext)) (xs := ([] : List FVarId))
      (b := type) hcl List.nodup_nil (by simp) (by simp)
    simpa using h
  have main : ∀ i lctx t (ps : Array Expr) (fvs : List FVarId),
      ps.toList = fvs.map .fvar → fvs.length + i = n → fvs.Nodup →
      Lean4Lean.LocalContext.WF lctx → Lean4Lean.LocalContext.fvars lctx = fvs.reverse →
      (∀ x ∈ fvs, ∀ d, lctx.find? x = some d →
        d.type.looseBVarRange' = 0 ∧ ∀ v ∈ d.value? true, v.looseBVarRange' = 0) →
      t.looseBVarRange' = 0 → FVarsIn (· ∈ fvs) t →
      (∀ lctx' t' (ps' : Array Expr), ps'.size = n → lctx'.mkForall ps' t' = lctx.mkForall ps t →
        MWF env (fun s => I s ∧ ∀ fv ∈ fvs, s.ngen.Reserves fv) (k lctx' t' ps') Q) →
      MWF env (fun s => I s ∧ ∀ fv ∈ fvs, s.ngen.Reserves fv)
        (withParams.loop k lctx t ps i) Q := by
    intro i
    induction i with
    | zero =>
      intro lctx t ps fvs hps hlen hnd hwf hlist hlc hcl' hfv' hk'
      rw [withParams.loop]
      refine hk' lctx t ps ?_ rfl
      have : ps.size = fvs.length := by rw [← Array.length_toList, hps, List.length_map]
      omega
    | succ i ih =>
      intro lctx t ps fvs hps hlen hnd hwf hlist hlc hcl' hfv' hk'
      cases t with
      | forallE name dom body bi =>
        rw [withParams.loop]
        have hdom : dom.looseBVarRange' = 0 := by
          simp only [Expr.looseBVarRange', Nat.max_eq_zero_iff] at hcl'; omega
        have hbody : body.looseBVarRange' ≤ 1 := by
          simp only [Expr.looseBVarRange', Nat.max_eq_zero_iff] at hcl'; omega
        obtain ⟨hfvd, hfvb⟩ : FVarsIn (· ∈ fvs) dom ∧ FVarsIn (· ∈ fvs) body := hfv'
        refine MWF.bind' (Q := fun a s' =>
            (I s' ∧ ∀ fv ∈ fvs ++ [(⟨a⟩ : FVarId)], s'.ngen.Reserves fv)
              ∧ (⟨a⟩ : FVarId) ∉ fvs) (MWF.mkFreshId' ?_) ?_
        · intro s hs
          refine ⟨⟨hng s hs.1, ?_⟩, ?_⟩
          · intro fv hfv2
            rcases List.mem_append.1 hfv2 with h | h
            · exact (hs.2 fv h).mono NameGenerator.LE.next
            · rw [List.mem_singleton] at h; subst h
              exact NameGenerator.next_reserves_self
          · exact fun h => s.ngen.not_reserves_self (hs.2 _ h)
        · intro a
          refine MWF.of_pure_pre (A := (⟨a⟩ : FVarId) ∉ fvs) (fun s hs => hs.2) fun hmem => ?_
          have hfind : lctx.find? ⟨a⟩ = none := by
            rw [hwf.find?_eq_find?_toList, List.find?_eq_none]
            intro d hd h
            simp only [beq_iff_eq] at h
            refine hmem ?_
            have : (⟨a⟩ : FVarId) ∈ Lean4Lean.LocalContext.fvars lctx :=
              List.mem_map.2 ⟨d, hd, h.symm⟩
            rwa [hlist, List.mem_reverse] at this
          have hfind' : ∀ x, (lctx.mkLocalDecl ⟨a⟩ name dom bi).find? x =
              if x == (⟨a⟩ : FVarId) then
                some (.cdecl lctx.decls.size ⟨a⟩ name dom bi .default)
              else lctx.find? x := fun _ => LocalContext.find?_mkLocalDecl hwf hfind
          have hne : ∀ x ∈ fvs, (lctx.mkLocalDecl ⟨a⟩ name dom bi).find? x = lctx.find? x := by
            intro x hx
            rw [hfind', if_neg (by simp; rintro rfl; exact hmem hx)]
          refine MWF.weaken (ih (lctx.mkLocalDecl ⟨a⟩ name dom bi)
            (body.instantiate1 (.fvar ⟨a⟩)) (ps.push (.fvar ⟨a⟩)) (fvs ++ [⟨a⟩])
            (by simp [hps]) (by simp; omega) (nodup_append_singleton hnd hmem)
            (hwf.mkLocalDecl hfind)
            (by simp [Lean4Lean.LocalContext.fvars] at hlist ⊢; simp [hlist]; rfl)
            ?_ ?_ ?_ ?_) fun s hs => hs.1
          · intro x hx d hd
            rcases List.mem_append.1 hx with h | h
            · exact hlc x h d (by rwa [hne x h] at hd)
            · simp only [List.mem_singleton] at h; subst h
              rw [hfind', if_pos (by simp)] at hd
              cases hd; exact ⟨hdom, by simp [Lean.LocalDecl.value?]⟩
          · rw [Expr.instantiate1_eq]
            have := Expr.instantiate1'_looseBVarRange (e := body) (a := .fvar ⟨a⟩)
              (n := 0) (k := 0) (by simpa using hbody) (by simp [Expr.looseBVarRange'])
            omega
          · rw [Expr.instantiate1_eq]
            exact FVarsIn.instantiate1 (hfvb.mono fun _ h => by simp [h])
              (show FVarsIn _ (Expr.fvar ⟨a⟩) from by simp [FVarsIn])
          · intro lctx' t' ps' hsz heq
            refine (hk' lctx' t' ps' hsz (heq.trans ?_)).weaken fun s hs =>
              ⟨hs.1, fun fv hfv2 => hs.2 fv (List.mem_append.2 (.inl hfv2))⟩
            exact mkForall_push_mkLocalDecl hps hnd hmem hwf hfind hlc
              (exists_find?_of_fvars hwf hlist) hcl' (hfvb.mono fun x h e => hmem (e ▸ h))
      | _ => rw [withParams.loop] <;> first | exact MWF.throw' _ | nofun
  refine MWF.weaken (main n {} type #[] [] (by simp) (by simp) List.nodup_nil
    Lean4Lean.LocalContext.wf_empty (by simp [Lean4Lean.LocalContext.fvars])
    (by simp) hcl (hfv.mono fun _ h => h.elim)
    (fun lctx' t' ps' hsz heq => (hk lctx' t' ps' hsz (heq.trans hempty)).weaken
      fun s hs => hs.1))
    fun s hs => ⟨hs, by simp⟩

end ElimNestedInductive

/-! ## 3. The identity -/


/-- The half of the premise that `Environment.addInductive`'s guard loop **does** supply:
every constructor type is free of free variables and metavariables
(`checkNoMVarNoFVar.WF`). -/
def BlockNoFVar (types : List InductiveType) : Prop :=
  ∀ t ∈ types, ∀ c ∈ t.ctors, FVarsIn (fun _ => False) c.type

/-- The half **nothing** supplies before `run`: every constructor type is loose-bvar-free.  See
§5 for what happens when it fails, and why no guard in either kernel rules it out. -/
def BlockClosed (types : List InductiveType) : Prop :=
  ∀ t ∈ types, ∀ c ∈ t.ctors, c.type.looseBVarRange' = 0

theorem forall₂_eq {α : Type _} : ∀ {l bs : List α},
    List.Forall₂ (fun a b => b = a) l bs → bs = l
  | _, _, .nil => rfl
  | _, _, .cons h hs => by rw [h, forall₂_eq hs]

namespace ElimNestedInductive

/-- `MWF.mapM_forall₂` (`Verify/Inductive/NestedRunInvariant.lean` §1) with the body's
obligation restricted to the list's **members**.  Needed because the per-constructor
hypotheses of §3 are facts about the constructors of the block, not about every
`Constructor`. -/
theorem MWF.mapM_forall₂_mem {β : Type} {f : α → M β} {I : State → Prop} {p : α → β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, MWF env I (f a) (fun b s' => p a b ∧ I s')) →
      MWF env I (l.mapM f) (fun bs s' => List.Forall₂ p l bs ∧ I s')
  | [], _ => by rw [List.mapM_nil]; exact MWF.pure' fun _ h => ⟨.nil, h⟩
  | a :: l, hf => by
    rw [List.mapM_cons]
    refine (hf a List.mem_cons_self).bind' fun b => ?_
    refine MWF.bind' (MWF.frame (A := p a b) (MWF.mapM_forall₂_mem l
      (fun x hx => hf x (List.mem_cons_of_mem _ hx)))) fun bs => ?_
    exact MWF.pure' fun _ h => ⟨.cons h.1 h.2.1, h.2.2⟩

/-- **`run.loop` leaves `newTypes` alone**, and so reports the input block. -/
theorem run_loop_id {env : Environment} (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    {types : List InductiveType} (hcl : BlockClosed types) (hfv : BlockNoFVar types)
    (nparams : Nat) (lctx : LocalContext) (params : Array Expr) :
    ∀ (fuel i : Nat), MWF env (fun s => s.newTypes.toList = types)
      (run.loop nparams lctx params i fuel)
      (fun r s => s.newTypes.toList = types ∧ r.types = types) := by
  intro fuel
  induction fuel with
  | zero => intro i; rw [run.loop]; exact MWF.throw' _
  | succ fuel ih =>
    intro i
    rw [run.loop]
    refine MWF.bind' MWF.get' fun s0 => ?_
    split
    · rename_i hi
      dsimp only
      refine MWF.weaken (P := fun s' =>
        (types[i]? = some s0.newTypes[i]) ∧ s'.newTypes.toList = types) ?_ ?_
      · refine MWF.of_pure_pre (A := types[i]? = some s0.newTypes[i])
          (fun s hs => hs.1) fun hmemT => ?_
        have hmem : s0.newTypes[i] ∈ types := List.mem_of_getElem? hmemT
        refine MWF.bind' (MWF.frame (MWF.mapM_forall₂_mem
          (p := fun c c' => c' = c) _ (fun ctor hctor => ?_))) fun ctors => ?_
        · refine MWF.withParams_id (fun _ h' => h') nparams _
            (hcl _ hmem ctor hctor) (hfv _ hmem ctor hctor) fun lctx' t As hAs heq => ?_
          rw [hAs]
          simp only [beq_self_eq_true, if_true]
          refine MWF.bind' (Q := fun a s' => a = t ∧ s'.newTypes.toList = types) ?_ ?_
          · intro s a s' hs hr
            rw [replaceAllNested_id h] at hr; cases hr; exact ⟨rfl, hs⟩
          · intro a
            refine MWF.pure' fun s hs => ?_
            rw [hs.1, heq]
            exact ⟨rfl, hs.2⟩
        · refine MWF.bind' (MWF.modify' (Q := fun _ s => s.newTypes.toList = types)
            fun s hs => ?_) fun _ => ih (i+1)
          show (Array.set! _ i _).toList = types
          rw [Array.toList_set!, hs.2.2, forall₂_eq hs.2.1]
          have he : ({ s0.newTypes[i] with ctors := s0.newTypes[i].ctors } : InductiveType)
            = s0.newTypes[i] := rfl
          rw [he]
          exact List.set_eq_self_of_getElem? hs.1
      · intro s' hs'
        obtain ⟨h1, rfl⟩ := hs'
        refine ⟨?_, h1⟩
        rw [← h1]
        exact List.getElem?_eq_getElem (by simpa using hi)
    · refine MWF.pure' fun s' h' => ?_
      obtain ⟨h1, rfl⟩ := h'
      exact ⟨h1, h1⟩

/-- **`ElimNestedInductive.run` is the identity on `types`.**  Two premises: no `.inductInfo` in
the environment (which `ves.WF env` forces -- `VEnvs.WF.find?_ne_inductInfo`), and the block's
constructor types closed and free of free variables. -/
theorem run_types_eq {env : Environment} (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    {types : List InductiveType} (hcl : BlockClosed types) (hfv : BlockNoFVar types)
    (fuel nparams : Nat) :
    MWF env (fun s => s.newTypes.toList = types) (run fuel nparams types)
      (fun r s => s.newTypes.toList = types ∧ r.types = types) := by
  cases types with
  | nil => unfold run; exact MWF.throw' _
  | cons I rest =>
    unfold run
    refine MWF.bind' (MWF.modify' (Q := fun _ s => s.newTypes.toList = I :: rest)
      fun s hs => hs) fun _ => ?_
    exact MWF.withParams' (fun _ h' => h') nparams
      (fun lctx t ps _ => run_loop_id h hcl hfv nparams lctx ps fuel 0) _

/-- The `run'` form, as `Environment.addInductive` calls it -- the shape
`run_run'_aux2nested` (`Verify/Inductive/AddInductiveStep.lean` §4) has. -/
theorem run_run'_types {env : Environment} (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    {types : List InductiveType} (hcl : BlockClosed types) (hfv : BlockNoFVar types)
    (fuel nparams : Nat) (s : State) (hs : s.newTypes.toList = types)
    (r : Result) (hr : (run fuel nparams types env).run' s = .ok r) : r.types = types :=
  let ⟨_, hr⟩ := run'_ok hr; (run_types_eq h hcl hfv fuel nparams s r _ hs hr).2

end ElimNestedInductive

/-! ## 4. The residue, with `ElimNestedInductive` removed -/

/-- **`AddInductiveRunRealises` with `ElimNestedInductive` gone.**  No `res`, no
`ElimNestedInductive.run` success equation, no `aux2nested`: `AddInductive.run` is applied to the
*input* block, which is the direction `Verify/Inductive/AddInductiveStep.lean` §6 asks for.

The price is the premise `BlockClosed types`, and §5 shows it is not a proof artefact: without
it the statement below is false.

**Corrected 2026-09-02, and the correction is about this very sentence.** It used to add "**and
`AddInductiveRunRealises` itself**", which §5 does **not** show: §5 refutes
`AddInductiveRunRealises`, which is applied to `res.types`, whereas the residue below applies
`AddInductive.run` to `types`. Measured: `AddInductive.run 1 [fooBad] 0 ctx` **rejects**, with
*"type checker does not support loose bound variables"*. So `fooBad` does **not** refute a
premise-free `AddInductiveRunRealisesClosed`, and nothing in the tree does. `BlockClosed` is
load-bearing for the **chain** — it is what makes `run_types_eq` true — not for the residue's
truth. An unproved negative asserted as established is ledger blindness kind 4. -/
def AddInductiveRunRealisesClosed : Prop :=
  ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
    ∀ (lp : List Name) (np : Nat) (types : List InductiveType) (ap : Bool) (fuel : FuelConfig),
      BlockClosed types →
      (AddInductive.run np types 0
          { env, allowPrimitive := ap, lparams := lp, safety := .safe, fuel }).WF fun env' =>
        ∃ ves' : VEnvs, ∀ safety, ∃ D : VInductDecl',
          TrIndDecl (ves.venv safety) lp np types false D ∧
          D.WF (ves.venv safety) ∧
          AddInductStages env.constants (ves.venv safety) D env'.constants (ves'.venv safety)

/-- **The identity's payoff.**  `AddInductiveRunRealisesClosed` discharges the body of
`AddInductiveRunRealises` at every block whose constructor types are closed and fvar-free — with
the `res` of the run-success equation *identified with `types`*, so `ElimNestedInductive` no
longer appears in what has to be proved. -/
theorem addInductiveRunRealises_of_closed (H : AddInductiveRunRealisesClosed)
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lp : List Name) (np : Nat) (types : List InductiveType) (ap : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result)
    (hcl : BlockClosed types) (hfv : BlockNoFVar types)
    (hres : (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
        { lvls := lp.map .param, newTypes := types.toArray } = .ok res)
    (_hz : res.aux2nested = []) :
    (AddInductive.run np res.types 0
        { env, allowPrimitive := ap, lparams := lp, safety := .safe, fuel }).WF fun env' =>
      ∃ ves' : VEnvs, ∀ safety, ∃ D : VInductDecl',
        TrIndDecl (ves.venv safety) lp np types false D ∧
        D.WF (ves.venv safety) ∧
        AddInductStages env.constants (ves.venv safety) D env'.constants (ves'.venv safety) := by
  rw [ElimNestedInductive.run_run'_types (fun _ _ => wf.find?_ne_inductInfo) hcl hfv
    _ _ _ (by simp) _ hres]
  exact H wf lp np types ap fuel hcl

/-! ## 5. The premise is not a proof artefact -/

-- `trExprS_looseBVarRange_nil` (`Verify/PrimitiveWF.lean`) is the `Closed`-of-`TrExprS` step;
-- it is already in the tree and is reused verbatim below.

/-- A constructor type with a loose bound variable has **no translation**, so the conjunction
`AddInductiveRunRealises` asserts is unreachable at such a block. -/
theorem not_trIndDecl_step_of_looseBVar {venv venv' : VEnv} {m m' : ConstMap}
    {lp : List Name} {np : Nat} {types : List InductiveType}
    {j : Nat} {t : InductiveType} (ht : types[j]? = some t)
    {q : Nat} {c : Constructor} (hcq : t.ctors[q]? = some c)
    (hc : c.type.looseBVarRange' ≠ 0) :
    ¬ ∃ D : VInductDecl', TrIndDecl venv lp np types false D ∧
        D.WF venv ∧ AddInductStages m venv D m' venv' := by
  rintro ⟨D, htr, -, hadd⟩
  obtain ⟨et, het⟩ := hadd.addIndTypes
  have hj : j < D.types.length := by
    rw [← htr.length]; exact (List.getElem?_eq_some_iff.1 ht).1
  obtain ⟨T, hT⟩ : ∃ T, D.types[j]? = some T := ⟨_, List.getElem?_eq_getElem hj⟩
  have hq : q < T.ctors.length := by
    rw [← htr.trCtorsLen j t T ht hT]; exact (List.getElem?_eq_some_iff.1 hcq).1
  obtain ⟨C, hC⟩ : ∃ C, T.ctors[q]? = some C := ⟨_, List.getElem?_eq_getElem hq⟩
  exact hc (trExprS_looseBVarRange_nil (htr.trCtors et het j t T ht hT q c C hcq hC).2)

/-- The same for the nested relation, i.e. for `AddInductPost`'s own conjunct. -/
theorem not_inductStepNested_of_looseBVar {m m' : ConstMap} {venv venv' : VEnv}
    {lp : List Name} {np : Nat} {types : List InductiveType} {numNested : Nat}
    {j : Nat} {t : InductiveType} (ht : types[j]? = some t)
    {q : Nat} {c : Constructor} (hcq : t.ctors[q]? = some c)
    (hc : c.type.looseBVarRange' ≠ 0) :
    ¬ InductStepNested m m' venv venv' lp np types numNested := by
  rintro ⟨D, K, R, htr, -, -, hadd⟩
  obtain ⟨et, het⟩ := hadd.addIndTypesC
  have hj : j < D.types.length := by
    rw [htr.length]
    exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 ht).1 (Nat.le_add_right ..)
  obtain ⟨T, hT⟩ : ∃ T, D.types[j]? = some T := ⟨_, List.getElem?_eq_getElem hj⟩
  have hq : q < T.ctors.length := by
    rw [← htr.trCtorsLen j t T ht hT]; exact (List.getElem?_eq_some_iff.1 hcq).1
  obtain ⟨C, hC⟩ : ∃ C, T.ctors[q]? = some C := ⟨_, List.getElem?_eq_getElem hq⟩
  exact hc (trExprS_looseBVarRange_nil (htr.trCtors et het j t T ht hT q c C hcq hC).2)

/-- **`AddInductPost` is false at a block with a loose bvar in a constructor type**, for every
`numNested` — so no choice of witness rescues it. -/
theorem not_addInductPost_of_looseBVar {env env' : Environment} {ves : VEnvs}
    {lp : List Name} {np : Nat} {types : List InductiveType}
    {j : Nat} {t : InductiveType} (ht : types[j]? = some t)
    {q : Nat} {c : Constructor} (hcq : t.ctors[q]? = some c)
    (hc : c.type.looseBVarRange' ≠ 0) :
    ¬ AddInductPost env env' ves lp np types := by
  rintro ⟨ves', numNested, hstep⟩
  exact not_inductStepNested_of_looseBVar ht hcq hc (hstep .safe)

namespace LooseBVarWitness

/-- The constructor of the witness block, declared at `∀ (α : Type) (x : #1), Foo #1`.  The `#1`
in `x`'s domain is **loose**: at that position only `α` is bound. -/
def fooBadCtor : Constructor :=
  { name := `Lean4Lean.LooseBVarWitness.Foo.mk,
    type := .forallE `α (.sort (.succ .zero))
      (.forallE `x (.bvar 1)
        (.app (.const `Lean4Lean.LooseBVarWitness.Foo []) (.bvar 1)) .default) .default }

/-- What `ElimNestedInductive.run` turns `fooBadCtor` into: `∀ (α : Type), α → Foo α`.

`withParams` strips the `α` binder, lowering the loose `#1` to `#0`; `LocalContext.mkForall`
then puts the binder back using the real `Expr.abstract`, which **leaves bound variables
alone** (`kernel/abstract.cpp`: its `replace` rewrites only `fvar`/`mvar` nodes, and it returns
`e` unchanged when `!has_fvar(e)`).  So the loose `#0` is *captured* by the restored `α`. -/
def fooGoodCtor : Constructor :=
  { name := `Lean4Lean.LooseBVarWitness.Foo.mk,
    type := .forallE `α (.sort (.succ .zero))
      (.forallE `x (.bvar 0)
        (.app (.const `Lean4Lean.LooseBVarWitness.Foo []) (.bvar 1)) .default) .default }

/-- A constructor whose loose bvar is **too far out to be captured** — `∀ (α : Type) (x : #9),
Foo α`.  `run` is not the identity here either, but the output is still open, so the type
checker rejects: this is the sub-case the received account covers. -/
def fooFarCtor : Constructor :=
  { name := `Lean4Lean.LooseBVarWitness.Foo.mk,
    type := .forallE `α (.sort (.succ .zero))
      (.forallE `x (.bvar 9)
        (.app (.const `Lean4Lean.LooseBVarWitness.Foo []) (.bvar 1)) .default) .default }

/-- `Foo : Type → Type`, `np = 1`, with the loose-bvar constructor. -/
def fooBad : InductiveType :=
  { name := `Lean4Lean.LooseBVarWitness.Foo
    type := .forallE `α (.sort (.succ .zero)) (.sort (.succ .zero)) .default
    ctors := [fooBadCtor] }

/-- `run`'s output at `fooBad`: an ordinary `Foo.mk : ∀ (α : Type), α → Foo α`. -/
def fooGood : InductiveType := { fooBad with ctors := [fooGoodCtor] }

def fooFar : InductiveType := { fooBad with ctors := [fooFarCtor] }

theorem fooBadCtor_looseBVar : fooBadCtor.type.looseBVarRange' ≠ 0 := by decide

theorem fooBad_ctor_zero : fooBad.ctors[0]? = some fooBadCtor := rfl

theorem fooBad_zero : ([fooBad] : List InductiveType)[0]? = some fooBad := rfl

/-- The output block *is* closed — so the premise cannot be recovered from the success of
`AddInductive.run`, which only ever sees `res.types`.  This is route (b) of the brief, refuted. -/
theorem fooGood_closed : BlockClosed [fooGood] := by
  intro t ht
  rw [List.mem_singleton] at ht; subst ht
  decide

/-- And the input block is not. -/
theorem fooBad_not_closed : ¬ BlockClosed [fooBad] :=
  fun h => fooBadCtor_looseBVar (h fooBad List.mem_cons_self fooBadCtor List.mem_cons_self)

/-- **`AddInductPost` — hence `AddInductiveStepWF`, hence `addDecl.WF_honest`'s inductive
branch — is false**, at any environment carrying an abstract model at which the checker accepts
`fooBad`.

**Status since 2026-09-01: still a true implication, but its `hok` is now unsatisfiable.**  The
two `checkNoLooseBVars` calls added to `Environment.addInductive`'s pre-`run` guard loop reject
`fooBad`, so no `env'` satisfies the hypothesis — machine-observed by §5.1's second `#eval`, and
proved in general by `Verify/ClosednessPropagation.lean`'s `rejectsNonClosed`, which contraposes
§6's `addInductive_WF_blockClosed`.  The theorem is deliberately **not** deleted: it is what
records *why* the guard is there, and it would come back to life the moment the guard were
removed — which is exactly what the flipped `#eval` watches for.

**Be precise about what that buys.**  "Un-refuted at this witness" is not "proved".
`AddInductiveStepWF` now follows from `AddInductiveStepWFClosed` **plus** `rejectsNonClosed`
(`Verify/ClosednessPropagation.lean`'s `addInductiveStepWF_of_closed`), and
`AddInductiveStepWFClosed` is itself still **open** — §7 reduces it to
`AddInductiveRunRealisesClosed` and stops there.  Worse, `AddInductiveStepWFClosed`'s premise is
`BlockClosed` only, while `TrIndDeclN.trType` also needs the *member's* own type closed; the
guard supplies that too, so the statement to aim at is
`Verify/ClosednessPropagation.lean`'s `AddInductiveStepWFFull`.

Before the guard, `hok` was an *executable* observation that provably could not be turned into a
kernel proof: the capture is performed by `Expr.abstract`, which is `opaque` in this repo (its
only equation is the frozen axiom `Expr.abstract_eq`, whose side condition `looseBVarRange' = 0`
is exactly what fails here), so `rfl`/`decide` could not evaluate it.  The *rejection* is not in
that position — it is a theorem (`rejectsNonClosed`), because the guard is a pure recursion and
never calls `Expr.abstract`. -/
theorem not_addInductiveStepWF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (fuel : FuelConfig) (env' : Environment)
    (hok : Environment.addInductive env [] 1 [fooBad] false false fuel = .ok env') :
    ¬ AddInductiveStepWF := fun H =>
  not_addInductPost_of_looseBVar fooBad_zero fooBad_ctor_zero fooBadCtor_looseBVar
    (H wf [] 1 [fooBad] false fuel env' hok)

/-- **`AddInductiveRunRealises` is false too**, at the same witness — so the residue
`Verify/Inductive/AddInductiveStep.lean` §6 names is not merely open.

Same status note as `not_addInductiveStepWF`: still a true implication, but its `hok` — here
acceptance by `AddInductive.run` of `run`'s *output* — is no longer reachable through
`Environment.addInductive`, because the guard rejects the input before `run` is called.  Note the
asymmetry, which §5.1's `#eval` still checks: `run` itself is unchanged and still captures the
loose `#1`, and `AddInductive.run` still accepts the captured output.  So this hypothesis is
satisfiable *in isolation* — what is gone is the path to it from a submitted declaration.  The
repaired statement `AddInductiveRunRealisesClosed` (§4) remains open. -/
theorem not_addInductiveRunRealises {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result) (env' : Environment)
    (hres : (ElimNestedInductive.run fuel.inductiveFuel 1 [fooBad] env).run'
        { lvls := [], newTypes := #[fooBad] } = .ok res)
    (hz : res.aux2nested = [])
    (hok : AddInductive.run 1 res.types 0
        { env, allowPrimitive := false, lparams := [], safety := .safe, fuel } = .ok env') :
    ¬ AddInductiveRunRealises := fun H => by
  obtain ⟨ves', hves⟩ := H wf [] 1 [fooBad] false fuel res hres hz env' hok
  exact not_trIndDecl_step_of_looseBVar fooBad_zero fooBad_ctor_zero fooBadCtor_looseBVar
    (hves .safe)

/-- …while `AddInductiveRunRealisesClosed` (§4) is **not** refuted by this witness: its premise
excludes it — and, since 2026-09-01, so does the implementation.  Not refuted is not proved. -/
theorem fooBad_excluded_by_closed : ¬ BlockClosed [fooBad] := fooBad_not_closed

end LooseBVarWitness

/-! ### 5.1 The instruments

Two `#eval` checks.  Both `throwError` when the fact they assert stops holding, so they are
self-guarding; neither is a kernel proof (see `not_addInductiveStepWF`'s docstring for why the
second one cannot be). -/

open LooseBVarWitness in
/- **Firing.**  At the four blocks the soundness theorem actually needs — `R10.Wit.uIndType`
(`np = 0`) and the toolchain's own `Eq` (2), `Iff` (2), `Nonempty` (1), read out of the running
environment rather than re-spelled — `ElimNestedInductive.run` from the *empty* kernel
environment (the only kind `ves.WF env` admits) returns `aux2nested = []` and `types` **equal to
its input**, and `BlockClosed` holds at each.  So §3's identity has firing instances and §4's
premise is satisfied at every one of them. -/
#eval show Lean.CoreM Unit from do
  let kenv := Kernel.Environment.empty `main
  let mkBlock (n : Name) : Lean.CoreM (Nat × List Level × InductiveType) := do
    let some (.inductInfo v) := (← getEnv).find? n | throwError "firing: no inductive {n}"
    let ctors ← v.ctors.mapM fun c => do
      let some ci := (← getEnv).find? c | throwError "firing: no constructor {c}"
      return ({ name := c, type := ci.type } : Constructor)
    return (v.numParams, v.levelParams.map .param, { name := v.name, type := v.type, ctors })
  let blocks := (0, [], R10.Wit.uIndType) :: (← ([``Eq, ``Iff, ``Nonempty] : List Name).mapM mkBlock)
  for (np, lvls, t) in blocks do
    unless t.ctors.all (·.type.looseBVarRange == 0) do
      throwError "firing: BlockClosed fails at {t.name} -- §4's premise is not satisfied there"
    let .ok r := (ElimNestedInductive.run 1000 np [t] kenv).run' { lvls, newTypes := #[t] }
      | throwError "firing: run rejected {t.name}"
    unless r.aux2nested == [] do throwError "firing: aux2nested nonempty at {t.name}"
    unless r.types == [t] do
      throwError "firing: run is NOT the identity at {t.name}: {r.types.map (·.ctors.map (·.type))}"
  logInfo "firing: run is the identity at uIndType, Eq, Iff, Nonempty, all BlockClosed ✓"

open LooseBVarWitness in
/- **The witness, and the guard that now excludes it.**  `fooBad` has `looseBVarRange = 1` in its
constructor type, and

* `run` maps it to `fooGood`, which is **closed** — the loose bvar is captured by the parameter
  binder — so no fact about `res.types` can recover `BlockClosed types` (route (b), refuted, and
  this half is unaffected by the guard: `run` itself is unchanged);
* `AddInductive.run` **accepts** `run`'s output, so the capture really does reach the store;
* the pre-`run` guard `checkNoMVarNoFVar` accepts `fooBad`, so *that* guard supplies nothing about
  loose bvars — which is why a second one was needed;
* **`checkNoLooseBVars` rejects it**, and therefore so does the whole of
  `Environment.addInductive`.

**Historical record.**  Until 2026-09-01 the last bullet read the other way: `addInductive`
*accepted* `fooBad` and stored `fooGood`'s constructor type, and this `#eval` asserted exactly
that, supplying the `hok` of `not_addInductiveStepWF`/`not_addInductiveRunRealises` by execution.
That acceptance was the refutation of `AddInductiveStepWF`.  The two `checkNoLooseBVars` calls in
`Environment.addInductive`'s guard loop were then added — see §6 and
`Verify/ClosednessPropagation.lean` §4 for why the guard rather than a premise — and this
instrument was flipped to assert the rejection.  It fired correctly at the moment of the change,
printing *"addInductive REJECTED fooBad … the refutation of AddInductiveStepWF is void and must be
withdrawn"*: that message was the designed behaviour of a self-guarding instrument, not a bug.
The refutation theorems are **not** withdrawn — they remain true implications whose acceptance
hypothesis is now unsatisfiable; see their docstrings.

`fooFar`, whose loose bvar is too far out to be captured, was rejected before the change too, by
the type checker rather than the guard — that is the sub-case in which "both kernels reject via
the type checker" was already true, and `fooBad` is the one in which it was not. -/
#eval show Lean.CoreM Unit from do
  let kenv := Kernel.Environment.empty `main
  unless fooBadCtor.type.looseBVarRange == 1 do throwError "witness: fooBad is closed after all"
  unless fooGoodCtor.type.looseBVarRange == 0 do throwError "witness: fooGood is not closed"
  match kenv.checkNoMVarNoFVar fooBadCtor.name fooBadCtor.type with
  | .error _ =>
    throwError "witness: checkNoMVarNoFVar rejects fooBad -- then the SECOND guard is redundant \
      and §6's account of which guard supplies what is wrong"
  | .ok _ => pure ()
  -- the guard that does the work, in isolation
  match checkNoLooseBVars fooBadCtor.name fooBadCtor.type with
  | .ok _ =>
    throwError "witness: checkNoLooseBVars ACCEPTS fooBad's constructor type -- \
      guardLoop_blockNoFVar's BlockClosed conjunct is vacuous and RejectsNonClosed is false"
  | .error _ => pure ()
  -- …and it accepts a closed type, so it is not rejecting everything
  match checkNoLooseBVars fooGoodCtor.name fooGoodCtor.type with
  | .error e =>
    throwError "witness: checkNoLooseBVars REJECTS the closed fooGood ({e.toMessageData {}}) -- \
      the guard is not the intended one"
  | .ok _ => pure ()
  let fuel : FuelConfig := {}
  let .ok r := (ElimNestedInductive.run fuel.inductiveFuel 1 [fooBad] kenv).run'
      { lvls := ([] : List Name).map .param, newTypes := #[fooBad] }
    | throwError "witness: run rejected fooBad"
  unless r.aux2nested == [] do throwError "witness: aux2nested nonempty"
  unless r.types == [fooGood] do
    throwError "witness: run's output is not fooGood: {r.types.map (·.ctors.map (·.type))}"
  -- the capture would still reach the store if the guard were removed: `run`'s output is accepted
  match AddInductive.run 1 r.types 0
      { env := kenv, allowPrimitive := false, lparams := [], safety := .safe, fuel } with
  | .error e => throwError "witness: AddInductive.run rejected run's output ({e.toMessageData {}})"
  | .ok _ => pure ()
  -- the flipped assertion: `addInductive` now REJECTS, and with the guard's own message
  match Environment.addInductive kenv [] 1 [fooBad] false false with
  | .ok env' =>
    throwError "witness: addInductive ACCEPTS fooBad again (stored ctor type \
      {repr ((env'.find? fooGoodCtor.name).map (·.type))}) -- the guard is gone and \
      RejectsNonClosed is FALSE, so addInductiveStepWF_of_reject no longer fires"
  | .error e =>
    let msg := (← (e.toMessageData {}).toString)
    unless (msg.splitOn "loose bound variable").length ≥ 2 do
      throwError "witness: addInductive rejects fooBad, but not for loose bvars ({msg}) -- \
        RejectsNonClosed is not what is doing the work here"
  match Environment.addInductive kenv [] 1 [fooFar] false false with
  | .ok _ => throwError "witness: addInductive accepted fooFar too -- the sub-case split is wrong"
  | .error _ => pure ()
  logInfo "witness: checkNoLooseBVars REJECTS fooBad's constructor type and accepts fooGood's; \
    addInductive rejects both fooBad and fooFar with a loose-bound-variable error, while `run` \
    still captures #1 into the parameter binder -- so the capture is real and the guard, not the \
    type checker, is what excludes it ✓"

/-! ## 6. What the guard loop supplies

Since 2026-09-01 `Environment.addInductive`'s pre-`run` guard loop calls `checkNoLooseBVars` on
each member's own type and on each constructor's, beside the existing `checkNoMVarNoFVar` and
`checkNoNestedAux`.  So the loop now supplies **all three** of `BlockNoFVar`,
`BlockClosedMembers` and `BlockClosed`, and §5's witness is rejected rather than accepted.
-/

/-- The member-type half of the closedness condition: `TrIndDeclN.trType` forces
`TrExprS env Us [] t.type T.type`, hence `t.type` closed, exactly as `TrIndDeclN.trCtors` forces
each constructor type closed.  `Verify/ClosednessPropagation.lean`'s `BlockClosedFull` is this
conjoined with `BlockClosed`. -/
def BlockClosedMembers (types : List InductiveType) : Prop :=
  ∀ t ∈ types, t.type.looseBVarRange' = 0

/-- **The implementation's pure closedness check, in the model's vocabulary.**

`Lean4Lean.noLooseBVars` (`Lean4Lean/Inductive/Add.lean`) is a depth-tracking structural
recursion, deliberately *not* routed through the cached 20-bit `Expr.looseBVarRange` header
field, and this bridge is correspondingly a plain induction that uses **no axiom at all**.

That matters more than it looks.  Reading the header field would have needed
`Expr.looseBVarRange_eq`, whose side condition is `BVarBounded` and whose proof rests on the
frozen `Lean.Expr.mkData_eq`; that side condition would then have had to travel into
`RejectsNonClosed` and hence into `AddInductiveStepWF` — i.e. a hole moved from a conclusion
into a hypothesis, where no instrument in this repo would see it. -/
theorem looseBVarRange'_le_of_noLooseBVars {e : Expr} :
    ∀ {d : Nat}, noLooseBVars d e = true → e.looseBVarRange' ≤ d := by
  induction e with
  | bvar i =>
    intro d h
    simp only [noLooseBVars, decide_eq_true_eq] at h
    simp only [Expr.looseBVarRange']
    omega
  | sort => intro d _; simp [Expr.looseBVarRange']
  | const => intro d _; simp [Expr.looseBVarRange']
  | fvar => intro d _; simp [Expr.looseBVarRange']
  | mvar => intro d _; simp [Expr.looseBVarRange']
  | lit => intro d _; simp [Expr.looseBVarRange']
  | mdata _ e ih =>
    intro d h
    simp only [noLooseBVars] at h
    simpa [Expr.looseBVarRange'] using ih h
  | proj _ _ e ih =>
    intro d h
    simp only [noLooseBVars] at h
    simpa [Expr.looseBVarRange'] using ih h
  | app f a ihf iha =>
    intro d h
    simp only [noLooseBVars, Bool.and_eq_true] at h
    simp only [Expr.looseBVarRange', Nat.max_le]
    exact ⟨ihf h.1, iha h.2⟩
  | lam _ t b _ iht ihb =>
    intro d h
    simp only [noLooseBVars, Bool.and_eq_true] at h
    have h1 := iht h.1
    have h2 := ihb h.2
    simp only [Expr.looseBVarRange', Nat.max_le]
    omega
  | forallE _ t b _ iht ihb =>
    intro d h
    simp only [noLooseBVars, Bool.and_eq_true] at h
    have h1 := iht h.1
    have h2 := ihb h.2
    simp only [Expr.looseBVarRange', Nat.max_le]
    omega
  | letE _ t v b _ iht ihv ihb =>
    intro d h
    simp only [noLooseBVars, Bool.and_eq_true] at h
    have h1 := iht h.1.1
    have h2 := ihv h.1.2
    have h3 := ihb h.2
    simp only [Expr.looseBVarRange', Nat.max_le]
    omega

/-- **The converse: the guard rejects nothing that is closed.**  Together with
`looseBVarRange'_le_of_noLooseBVars` this says `noLooseBVars d e = true ↔ e.looseBVarRange' ≤ d`,
i.e. the implementation's check *is* the model's closedness condition and not something stricter.

This is the direction that matters for "the guard refuses nothing legitimate": without it, the
`#eval` scans in `Verify/ClosednessPropagation.lean` §5 would be the only evidence that the check
is not over-eager, and an `#eval` over one environment is not a proof.  With it, the only remaining
question is whether `looseBVarRange'` is the right notion, which is settled elsewhere — every
`TrExprS` at the empty context forces `looseBVarRange' = 0`
(`trExprS_looseBVarRange_nil`). -/
theorem noLooseBVars_of_looseBVarRange'_le {e : Expr} :
    ∀ {d : Nat}, e.looseBVarRange' ≤ d → noLooseBVars d e = true := by
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.looseBVarRange'] at h
    simp only [noLooseBVars, decide_eq_true_eq]
    omega
  | sort => intro d _; simp [noLooseBVars]
  | const => intro d _; simp [noLooseBVars]
  | fvar => intro d _; simp [noLooseBVars]
  | mvar => intro d _; simp [noLooseBVars]
  | lit => intro d _; simp [noLooseBVars]
  | mdata _ e ih =>
    intro d h
    simp only [Expr.looseBVarRange'] at h
    simpa [noLooseBVars] using ih h
  | proj _ _ e ih =>
    intro d h
    simp only [Expr.looseBVarRange'] at h
    simpa [noLooseBVars] using ih h
  | app f a ihf iha =>
    intro d h
    simp only [Expr.looseBVarRange', Nat.max_le] at h
    simp only [noLooseBVars, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam _ t b _ iht ihb =>
    intro d h
    simp only [Expr.looseBVarRange', Nat.max_le] at h
    simp only [noLooseBVars, Bool.and_eq_true]
    exact ⟨iht h.1, ihb (by omega)⟩
  | forallE _ t b _ iht ihb =>
    intro d h
    simp only [Expr.looseBVarRange', Nat.max_le] at h
    simp only [noLooseBVars, Bool.and_eq_true]
    exact ⟨iht h.1, ihb (by omega)⟩
  | letE _ t v b _ iht ihv ihb =>
    intro d h
    simp only [Expr.looseBVarRange', Nat.max_le] at h
    simp only [noLooseBVars, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb (by omega)⟩

/-- The two directions as one iff: `noLooseBVars` decides `looseBVarRange' ≤ d`. -/
theorem noLooseBVars_iff {e : Expr} {d : Nat} :
    noLooseBVars d e = true ↔ e.looseBVarRange' ≤ d :=
  ⟨looseBVarRange'_le_of_noLooseBVars, noLooseBVars_of_looseBVarRange'_le⟩

/-- **The guard accepts every closed declaration.**  The exact counterpart of
`checkNoLooseBVars.WF`, and the statement that "no legitimate declaration is refused" reduces to. -/
theorem checkNoLooseBVars_isOk_of_closed {n : Name} {e : Expr} (h : e.looseBVarRange' = 0) :
    checkNoLooseBVars n e = .ok () := by
  simp [checkNoLooseBVars, noLooseBVars_of_looseBVarRange'_le (d := 0) (Nat.le_of_eq h), pure,
    Except.pure]

/-- The postcondition of the new guard: `checkNoLooseBVars n e` succeeds only when `e` is closed.
No axiom (see `looseBVarRange'_le_of_noLooseBVars`). -/
theorem checkNoLooseBVars.WF (n : Name) (e : Expr) :
    (checkNoLooseBVars n e).WF fun _ => e.looseBVarRange' = 0 := by
  intro _ h
  cases hb : noLooseBVars 0 e with
  | false => simp [checkNoLooseBVars, hb] at h
  | true => exact Nat.le_zero.1 (looseBVarRange'_le_of_noLooseBVars hb)

/-! ### The fourth check: `checkUniformIndOccs`

Since 2026-09-02 the guard loop's **inner** (per-constructor) body has a fourth line,
`checkUniformIndOccs (types.map (·.name)) lparams nparams ctor.name ctor.type` — C++'s
`check_uniform_ind_occs`, run exactly where C++ runs it, immediately before nested elimination.
Unlike the other three it is parameterised by data the loop does **not** recurse on: the block's
member names, its level parameters and its `nparams`.  So the guard-loop lemmas below take
`names`, `lps`, `np` as *fixed* arguments, and only the list being iterated varies — that is why
the inner list (`cs`) and the outer list (`types`) can be recursed on independently while `names`
stays the whole block's name list.

`BlockUniformOccs` is the fact the loop yields.  It is stated with the **implementation**'s
`Lean4Lean.noNonUniformOcc` rather than with `Verify/Inductive/UniformOccMeasure.lean`'s
specification `uioOk`, for the boring reason that that file sits *downstream* of this one (it
imports `Experimental/ConeJoin.lean`, which imports this).  The two are the same function —
`UniformOccMeasure.lean`'s `uio_impl_eq` proves it pointwise — so via `uioOk_iff` this conjunct
is `UIOCond`, C++'s condition in `Prop`, at every constructor type of the block. -/

/-- **The fourth thing `Environment.addInductive`'s guard loop establishes**: every constructor
type of the block passes the syntactic uniform-occurrence pre-pass, at binder depth 0, for the
block's own member names `names`, level parameters `lps` and parameter count `np`.

`names`/`lps`/`np` are explicit rather than read off `types` because the loop's fourth check is
applied with the *whole* block's data while the loop recurses on a suffix; the call site
instantiates `names := types.map (·.name)`.  Via `UniformOccMeasure.lean`'s `uio_impl_eq` and
`uioOk_iff` this says: `UIOCond names lps np 0 c.type` for every constructor `c` of every
member — C++'s `check_uniform_ind_occs`, in `Prop`. -/
def BlockUniformOccs (names lps : List Name) (np : Nat) (types : List InductiveType) : Prop :=
  ∀ t ∈ types, ∀ c ∈ t.ctors, noNonUniformOcc names lps np 0 c.type = true

/-- The postcondition of the fourth guard, in the shape of `checkNoLooseBVars.WF`.  Like it, and
deliberately, this reaches **no axiom at all**: `noNonUniformOcc` is a pure structural recursion
that reads no cached `Expr` header field, and `ownLevels` pattern-matches `.param` instead of
using `Lean.Level.beq`, whose lawfulness is the frozen axiom
`Lean.Level.instLawfulBEqLevel`. -/
theorem checkUniformIndOccs.WF (names lps : List Name) (np : Nat) (n : Name) (e : Expr) :
    (checkUniformIndOccs names lps np n e).WF fun _ => noNonUniformOcc names lps np 0 e = true := by
  intro _ h
  cases hb : noNonUniformOcc names lps np 0 e with
  | false => simp [checkUniformIndOccs, hb] at h
  | true => rfl

/-- The inner loop of `Environment.addInductive`'s guard: each constructor type is checked by
`checkNoMVarNoFVar`, whose postcondition (`checkNoMVarNoFVar.WF`) is exactly
`FVarsIn fun _ => False`, and by `checkNoLooseBVars`, whose postcondition
(`checkNoLooseBVars.WF`) is exactly `looseBVarRange' = 0`. -/
theorem guardLoop_ctors (env : Environment) (names lps : List Name) (np : Nat) :
    ∀ (cs : List Constructor),
    (forIn cs PUnit.unit (fun ctor _ => do
        env.checkNoMVarNoFVar ctor.name ctor.type
        checkNoNestedAux ctor.name ctor.type
        checkNoNestedAuxName ctor.name
        checkNoLooseBVars ctor.name ctor.type
        checkUniformIndOccs names lps np ctor.name ctor.type
        pure (ForInStep.yield PUnit.unit)) : Except Exception PUnit).WF
      (fun _ => ∀ c ∈ cs, FVarsIn (fun _ => False) c.type ∧ c.type.looseBVarRange' = 0 ∧
        noNonUniformOcc names lps np 0 c.type = true)
  | [] => Except.WF.pure (fun _ h => absurd h nofun)
  | c :: cs => by
    rw [List.forIn_cons]
    refine Except.WF.bind (Q := fun r =>
      r = ForInStep.yield PUnit.unit ∧
        FVarsIn (fun _ => False) c.type ∧ c.type.looseBVarRange' = 0 ∧
        noNonUniformOcc names lps np 0 c.type = true) ?_ ?_
    · refine Except.WF.bind (checkNoMVarNoFVar.WF env c.name c.type) fun _ hfv => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (checkNoLooseBVars.WF c.name c.type) fun _ hcl => ?_
      refine Except.WF.bind (checkUniformIndOccs.WF names lps np c.name c.type) fun _ hu => ?_
      exact Except.WF.pure ⟨rfl, hfv, hcl, hu⟩
    · rintro r ⟨rfl, hfv⟩
      refine (guardLoop_ctors env names lps np cs).mono fun _ h x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hfv
      · exact h x hx

/-- **The exposing lemma.**  `Environment.addInductive`'s own pre-`run` guard loop supplies
`BlockNoFVar` (from `checkNoMVarNoFVar`), `BlockClosedMembers` and `BlockClosed` (from the two
`checkNoLooseBVars` calls added on 2026-09-01, one on the member's own type and one on each
constructor's), **and** `BlockUniformOccs` (from the `checkUniformIndOccs` call added on
2026-09-02 to the inner loop only, which is where C++ puts it).  The name is kept from the
version that could only deliver `BlockNoFVar`.

`names`/`lps`/`np` are fixed while the loop recurses on `types`: the fourth check is applied with
the *whole* block's data.  The call site takes `names := types.map (·.name)`, `lps := lparams`,
`np := nparams`. -/
theorem guardLoop_blockNoFVar (env : Environment) (names lps : List Name) (np : Nat) :
    ∀ (types : List InductiveType),
    (forIn types PUnit.unit (fun indType _ => do
        env.checkNoMVarNoFVar indType.name indType.type
        checkNoNestedAux indType.name indType.type
        checkNoNestedAuxName indType.name
        checkNoLooseBVars indType.name indType.type
        for ctor in indType.ctors do
          env.checkNoMVarNoFVar ctor.name ctor.type
          checkNoNestedAux ctor.name ctor.type
          checkNoNestedAuxName ctor.name
          checkNoLooseBVars ctor.name ctor.type
          checkUniformIndOccs names lps np ctor.name ctor.type
        pure (ForInStep.yield PUnit.unit)) : Except Exception PUnit).WF
      (fun _ => BlockNoFVar types ∧ BlockClosedMembers types ∧ BlockClosed types ∧
        BlockUniformOccs names lps np types)
  | [] => Except.WF.pure ⟨fun _ h => absurd h nofun, fun _ h => absurd h nofun,
      fun _ h => absurd h nofun, fun _ h => absurd h nofun⟩
  | t :: l => by
    rw [List.forIn_cons]
    refine Except.WF.bind (Q := fun r =>
      r = ForInStep.yield PUnit.unit ∧ t.type.looseBVarRange' = 0 ∧
        ∀ c ∈ t.ctors, FVarsIn (fun _ => False) c.type ∧ c.type.looseBVarRange' = 0 ∧
          noNonUniformOcc names lps np 0 c.type = true) ?_ ?_
    · refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (checkNoLooseBVars.WF t.name t.type) fun _ hm => ?_
      refine Except.WF.bind (guardLoop_ctors env names lps np t.ctors) fun _ hc => ?_
      exact Except.WF.pure ⟨rfl, hm, hc⟩
    · rintro r ⟨rfl, hm, hc⟩
      refine (guardLoop_blockNoFVar env names lps np l).mono fun _ h => ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact fun c hcm => (hc c hcm).1
        · exact h.1 x hx
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hm
        · exact h.2.1 x hx
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact fun c hcm => (hc c hcm).2.1
        · exact h.2.2.1 x hx
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact fun c hcm => (hc c hcm).2.2
        · exact h.2.2.2 x hx

/-- **The guard, as a fact about the whole of `Environment.addInductive`.**  `Except.WF` with a
postcondition that does not mention the result is exactly "if it succeeds, its input had this
property" — i.e. `Verify/ClosednessPropagation.lean`'s `RejectsNonClosed`, contraposed, plus the
member-type half.

No `∀ n v, env.find? n ≠ some (.inductInfo v)` premise and no `ves.WF env`: the guard loop is the
first thing `addInductive` runs, so `Except.WF.bind` needs nothing about what follows. -/
theorem addInductive_WF_blockClosedFull {env : Environment} {lparams : List Name} {np : Nat}
    {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig} :
    (Environment.addInductive env lparams np types iu ap fuel).WF
      fun _ => BlockNoFVar types ∧ BlockClosedMembers types ∧ BlockClosed types ∧
        BlockUniformOccs (types.map (·.name)) lparams np types := by
  unfold Environment.addInductive
  exact Except.WF.bind (guardLoop_blockNoFVar env _ lparams np types) fun _ hg _ _ => hg

/-! ### 6.1 The closedness half alone, with no frozen axiom

`guardLoop_blockNoFVar` reaches `Lean.Expr.mkAppData_eq`, `Lean.Expr.mkData_eq` and
`Lean.Level.hasMVar_eq` — *not* from the new check but from `checkNoMVarNoFVar.WF`, which bridges
the cached `hasFVar`/`hasMVar` header bits.  The closedness half needs none of that, and it is the
half that `Verify/ClosednessPropagation.lean`'s `RejectsNonClosed` — and hence the reduction of
`AddInductiveStepWF` to `AddInductiveStepWFClosed` — actually consumes.  So it is worth having
separately: the two lemmas below re-run the loop with `Q := fun _ => True` on every
`checkNoMVarNoFVar`, and their axiom set is `[propext, Classical.choice, Quot.sound]`.

That is the point of `noLooseBVars` being a pure recursion rather than a read of the
`Expr.looseBVarRange` header field, made measurable. -/

/-- `guardLoop_ctors` keeping only what `checkNoLooseBVars` and `checkUniformIndOccs` give — the
two checks that are pure structural recursions.  No frozen axiom. -/
theorem guardLoop_ctors_closed (env : Environment) (names lps : List Name) (np : Nat) :
    ∀ (cs : List Constructor),
    (forIn cs PUnit.unit (fun ctor _ => do
        env.checkNoMVarNoFVar ctor.name ctor.type
        checkNoNestedAux ctor.name ctor.type
        checkNoNestedAuxName ctor.name
        checkNoLooseBVars ctor.name ctor.type
        checkUniformIndOccs names lps np ctor.name ctor.type
        pure (ForInStep.yield PUnit.unit)) : Except Exception PUnit).WF
      (fun _ => ∀ c ∈ cs, c.type.looseBVarRange' = 0 ∧
        noNonUniformOcc names lps np 0 c.type = true)
  | [] => Except.WF.pure (fun _ h => absurd h nofun)
  | c :: cs => by
    rw [List.forIn_cons]
    refine Except.WF.bind (Q := fun r =>
      r = ForInStep.yield PUnit.unit ∧ c.type.looseBVarRange' = 0 ∧
        noNonUniformOcc names lps np 0 c.type = true) ?_ ?_
    · refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (checkNoLooseBVars.WF c.name c.type) fun _ hcl => ?_
      refine Except.WF.bind (checkUniformIndOccs.WF names lps np c.name c.type) fun _ hu => ?_
      exact Except.WF.pure ⟨rfl, hcl, hu⟩
    · rintro r ⟨rfl, hcl⟩
      refine (guardLoop_ctors_closed env names lps np cs).mono fun _ h x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hcl
      · exact h x hx

/-- `guardLoop_blockNoFVar` keeping only its two closedness conjuncts **and** the uniformity one —
i.e. dropping exactly the `checkNoMVarNoFVar` half, which is the only source of a frozen axiom
here.  No frozen axiom. -/
theorem guardLoop_blockClosed (env : Environment) (names lps : List Name) (np : Nat) :
    ∀ (types : List InductiveType),
    (forIn types PUnit.unit (fun indType _ => do
        env.checkNoMVarNoFVar indType.name indType.type
        checkNoNestedAux indType.name indType.type
        checkNoNestedAuxName indType.name
        checkNoLooseBVars indType.name indType.type
        for ctor in indType.ctors do
          env.checkNoMVarNoFVar ctor.name ctor.type
          checkNoNestedAux ctor.name ctor.type
          checkNoNestedAuxName ctor.name
          checkNoLooseBVars ctor.name ctor.type
          checkUniformIndOccs names lps np ctor.name ctor.type
        pure (ForInStep.yield PUnit.unit)) : Except Exception PUnit).WF
      (fun _ => BlockClosedMembers types ∧ BlockClosed types ∧
        BlockUniformOccs names lps np types)
  | [] => Except.WF.pure ⟨fun _ h => absurd h nofun, fun _ h => absurd h nofun,
      fun _ h => absurd h nofun⟩
  | t :: l => by
    rw [List.forIn_cons]
    refine Except.WF.bind (Q := fun r =>
      r = ForInStep.yield PUnit.unit ∧ t.type.looseBVarRange' = 0 ∧
        ∀ c ∈ t.ctors, c.type.looseBVarRange' = 0 ∧
          noNonUniformOcc names lps np 0 c.type = true) ?_ ?_
    · refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) fun _ _ => ?_
      refine Except.WF.bind (checkNoLooseBVars.WF t.name t.type) fun _ hm => ?_
      refine Except.WF.bind (guardLoop_ctors_closed env names lps np t.ctors) fun _ hc => ?_
      exact Except.WF.pure ⟨rfl, hm, hc⟩
    · rintro r ⟨rfl, hm, hc⟩
      refine (guardLoop_blockClosed env names lps np l).mono fun _ h => ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hm
        · exact h.1 x hx
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact fun c hcm => (hc c hcm).1
        · exact h.2.1 x hx
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact fun c hcm => (hc c hcm).2
        · exact h.2.2 x hx

/-- **The axiom-free form of the guard**, with all three of its pure-recursion conjuncts. -/
theorem addInductive_WF_blockClosedUniform {env : Environment} {lparams : List Name} {np : Nat}
    {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig} :
    (Environment.addInductive env lparams np types iu ap fuel).WF
      fun _ => BlockClosedMembers types ∧ BlockClosed types ∧
        BlockUniformOccs (types.map (·.name)) lparams np types := by
  unfold Environment.addInductive
  exact Except.WF.bind (guardLoop_blockClosed env _ lparams np types) fun _ hg _ _ => hg

/-- **The axiom-free form of the guard**, and the one `RejectsNonClosed` is proved from.  Its
statement is deliberately unchanged by the 2026-09-02 fourth check: `Verify/ClosednessPropagation`
consumes it verbatim (`rejectsNonClosed` takes its `.2`), so the new conjunct is exposed by
`addInductive_WF_blockClosedUniform` beside it rather than spliced into it. -/
theorem addInductive_WF_blockClosed {env : Environment} {lparams : List Name} {np : Nat}
    {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig} :
    (Environment.addInductive env lparams np types iu ap fuel).WF
      fun _ => BlockClosedMembers types ∧ BlockClosed types :=
  addInductive_WF_blockClosedUniform.mono fun _ h => ⟨h.1, h.2.1⟩

/-! ### 6.2 `RejectsNonUniform`

The analogue of `Verify/ClosednessPropagation.lean`'s `RejectsNonClosed`, and it is free for the
same reason the loose-bvar one was: `Except.WF x Q` unfolds to `∀ a, x = .ok a → Q a`, so an
`Except.WF` whose postcondition does not mention the result **is** the contrapositive
"if it succeeded, the input had this property".  Nothing about `ElimNestedInductive.run`,
`AddInductive.run`, `ves.WF env` or `env.find?` enters: the guard loop is the first thing
`Environment.addInductive` does.

Stated here rather than in `Verify/ClosednessPropagation.lean` because that file is not this
stream's to edit, and because `BlockUniformOccs` lives here.

**What this is and is not.**  It is a fact about the *implementation*: lean4lean now refuses what
C++'s `check_uniform_ind_occs` refuses.  It is **not** a soundness lemma, and unlike
`rejectsNonClosed` it discharges no premise of any open statement — `AddInductiveStepWFClosed`
does not ask for uniformity.  Its value is convergence with C++ plus the proof-side dividend
`UniformOccMeasure.lean`'s `uio_restore_none_forces_reject` records: on an accepted constructor
type, `VIndRestore.restore`'s non-uniform fallthrough is unreachable. -/

/-- **`Environment.addInductive` rejects a block with a non-uniform occurrence.**  The uniformity
analogue of `RejectsNonClosed`.

Note where the difficulty could hide: the hypothesis is a *negation*, so an implementation whose
check was identically `true` would make it vacuous, and no instrument in this repo inspects
hypotheses.  The hypothesis is exhibited as inhabited in `UniformOccMeasure.lean`
(`uio_rejectsNonUniform_fires`, at the arena's `nested-nonuniform-param` block), and the check is
exhibited as *not* identically `false` by the same file's `uio/scanA` (0 violations in 7013
submitted constructors) and `uio_ok_of_occ`. -/
def RejectsNonUniform : Prop :=
  ∀ (env : Environment) (lp : List Name) (np : Nat) (types : List InductiveType)
    (ap : Bool) (fuel : FuelConfig), ¬ BlockUniformOccs (types.map (·.name)) lp np types →
    ∀ env', Environment.addInductive env lp np types false ap fuel ≠ .ok env'

/-- **`RejectsNonUniform`, proved**, straight from `addInductive_WF_blockClosedUniform`.

Axioms: `[propext, Classical.choice, Quot.sound]` — **no frozen axiom**.  That is not an accident
of the proof but of the port: `noNonUniformOcc` reads no cached `Expr` header bit (so no
`Lean.Expr.mkData_eq`/`mkAppData_eq`) and `ownLevels` pattern-matches `.param` rather than calling
`Lean.Level.beq`, whose `LawfulBEq` instance is the frozen `Lean.Level.instLawfulBEqLevel`.  Had
it used `us == lps.map .param`, that axiom's side condition would have landed inside *this
statement's hypothesis*, where instrument 7 — which reads conclusions — would not have seen it. -/
theorem rejectsNonUniform : RejectsNonUniform :=
  fun _env _lp _np _types _ap _fuel hu env' hok =>
    hu (addInductive_WF_blockClosedUniform env' hok).2.2

/-- The `isUnsafe = true` case as well, since the guard loop runs before the safety flag is
consulted: the same rejection holds at either safety. -/
theorem rejectsNonUniform' (env : Environment) (lp : List Name) (np : Nat)
    (types : List InductiveType) (iu ap : Bool) (fuel : FuelConfig)
    (hu : ¬ BlockUniformOccs (types.map (·.name)) lp np types) (env' : Environment) :
    Environment.addInductive env lp np types iu ap fuel ≠ .ok env' :=
  fun hok => hu (addInductive_WF_blockClosedUniform env' hok).2.2

/-- `addInductive_WF_of_run` (`Verify/Inductive/AddInductiveStep.lean` §5) with everything the
guard loop establishes additionally handed to the continuation, read off the loop the collapse
lemma discarded as `Q := fun _ => True`. -/
theorem addInductive_WF_of_run' {env : Environment} {lparams : List Name} {np : Nat}
    {types : List InductiveType} {iu ap : Bool} {fuel : FuelConfig} {Q : Environment → Prop}
    (h : ∀ n v, env.find? n ≠ some (.inductInfo v))
    (H : BlockNoFVar types → BlockClosedMembers types → BlockClosed types →
        BlockUniformOccs (types.map (·.name)) lparams np types →
        ∀ res : ElimNestedInductive.Result,
        (ElimNestedInductive.run fuel.inductiveFuel np types env).run'
            { lvls := lparams.map .param, newTypes := types.toArray } = .ok res →
        res.aux2nested = [] →
        (AddInductive.run np res.types 0
          { env, allowPrimitive := ap, lparams,
            safety := if iu then .unsafe else .safe, fuel }).WF Q) :
    (Environment.addInductive env lparams np types iu ap fuel).WF Q := by
  unfold Environment.addInductive
  refine Except.WF.bind (guardLoop_blockNoFVar env _ lparams np types) fun _ hg => ?_
  refine Except.WF.bind_self fun res hres => ?_
  have hz : res.aux2nested = [] :=
    ElimNestedInductive.run_run'_aux2nested h _ _ _ _ rfl _ hres
  simp only [hz, List.length_nil]
  refine Except.WF.bind (H hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 res hres hz) fun env' hq => ?_
  simp only [if_true]
  exact Except.WF.pure hq

/-! ## 7. End to end -/

/-- `AddInductiveStepWF` restricted to blocks whose constructor types are loose-bvar-free.  §5
shows the restriction cannot be dropped: the unrestricted statement is false. -/
def AddInductiveStepWFClosed : Prop :=
  ∀ {env : Environment} {ves : VEnvs}, ves.WF env →
    ∀ lp np types ap fuel, BlockClosed types →
      (Environment.addInductive env lp np types false ap fuel).WF fun env' =>
        AddInductPost env env' ves lp np types

/-- **The payoff.**  `AddInductiveStepWFClosed` follows from `AddInductiveRunRealisesClosed`,
which mentions neither `ElimNestedInductive` nor a `res`: the residue is now a statement purely
about `AddInductive.run np types`. -/
theorem addInductiveStepWFClosed_of_run (H : AddInductiveRunRealisesClosed) :
    AddInductiveStepWFClosed := by
  intro env ves wf lp np types ap fuel hcl
  refine addInductive_WF_of_run' (fun _ _ => wf.find?_ne_inductInfo)
    fun hnf _ _ _ res hres hz => ?_
  refine (addInductiveRunRealises_of_closed H wf lp np types ap fuel res hcl hnf hres hz).mono
    fun env' h' => ?_
  obtain ⟨ves', hves⟩ := h'
  refine ⟨ves', 0, fun safety => ?_⟩
  obtain ⟨D, htr, hwf, hadd⟩ := hves safety
  exact ⟨D, [], D.idRestore, htr.toN hadd.addIndTypes, hadd.addIndTypes, hwf, hadd.toR⟩

/-! ## 8. Instrument 7: every new statement at its degenerate instance

`docs/vacuity-ledger.md` §0's seventh blindness: a statement can be green because its
hypotheses are unsatisfiable at the degenerate instance.  Each new statement is instantiated
there below, and what is *not* tested is said explicitly.

* **`mkForall_push_mkLocalDecl` at `fvs = []`** — the first binder `withParams` consumes.  All
  eight hypotheses hold with no assumptions at all, so the conclusion is a genuine equation
  (`mkForall_push_degenerate`).
* **`MWF.withParams_id` at `n = 0`** — `withParams type 0 k = k {} type #[]`, and `hcl` is still
  load-bearing there because `{}.mkForall #[] type` still calls `Expr.abstract`.  It **fires**:
  `R10.Wit.uIndType` has `np = 0` and is one of the four blocks §5.1's first `#eval` checks.
* **`run_loop_id` / `run_types_eq` at `types = []`** — `BlockClosed []` and `BlockNoFVar []` hold
  vacuously, but `ElimNestedInductive.run` *throws* on an empty block, so the statement is
  **empty at `types = []`** and is discharged there by `MWF.throw'`.  Its firing instances are
  the four blocks of §5.1, none of which is degenerate in the list.
* **`AddInductiveRunRealisesClosed` / `AddInductiveStepWFClosed`** — premises satisfiable:
  `BlockClosed [R10.Wit.uIndType]` holds (`blockClosed_uIndType`), and `ves.WF env` is inhabited
  at `Kernel.Environment.empty` by `Bridge.hasEmptyModel` (hole-free; `docs/vacuity-ledger.md`
  row 104a).  **What they do not test:** being premised on `ves.WF env` they cannot exercise a
  nested block at all — row 104b, `isNestedInductiveApp?` needs an `.inductInfo` that
  `VEnvs.WF.no_inductInfo` forbids — so `numNested` is always `0` here and nothing below is
  evidence about nesting.

  **CORRECTION 2026-09-02 (`docs/vacuity-ledger.md` row 113a), and it is about the *conclusion*,
  not the premises.**  Satisfiable premises are all this bullet ever claimed, and that reading
  was too kind to what follows from it: at the very instance where the premises hold —
  `[R10.Wit.uIndType]` from the empty environment — the `D` that witnesses the conclusion
  **cannot be `R10.Wit.decl`**.  `AddInductStages` pins each stored recursor's
  `levelParams.length` to `D.recUvars` (`r113a_addInductStages_recUvars`,
  `Verify/Inductive/StagesFiring.lean`), which is `0` at `R10.Wit.decl`, and the run stores
  `R10.Wit.U.rec` with `levelParams = [u]` (check R1, same file — `U : Type` makes
  `isLargeEliminator` true, so `getElimLevel` returns a fresh `.param`).  The conclusion is
  witnessed at `R113a.declLE = { R10.Wit.decl with isLE := true }`
  (`R113a.addInductStages_firing`), and that is the tree's **first** instance of
  `AddInductStages` whose output map is the one the executable builds.  So this bullet's
  "premises satisfiable" is not evidence that the statement's `∃ D` can be met by the witness
  bundle as it stood; `isLE = true` is forced.
* **`not_addInductiveStepWF` / `not_addInductiveRunRealises`** — **now vacuous, deliberately.**
  Until 2026-09-01 §5.1's second `#eval` exhibited `hok` at the empty environment.  The guard
  removed that: `hok` is unsatisfiable (`Verify/ClosednessPropagation.lean`'s `rejectsNonClosed`
  proves it, not merely observes it), so these are true-but-vacuous implications kept as the
  record of why the guard exists, and the flipped `#eval` is what will notice if the guard goes.
  `not_trIndDecl_step_of_looseBVar`, `not_inductStepNested_of_looseBVar` and
  `not_addInductPost_of_looseBVar` are *not* vacuous — their hypotheses are facts about a block,
  not about the checker, and `fooBadCtor_looseBVar` supplies one.
* **`looseBVarRange'_le_of_noLooseBVars` / `checkNoLooseBVars.WF`** — both directions checked
  below: `noLooseBVars_fooGood` fires the lemma at a closed type (so the conclusion is not
  vacuous), and `noLooseBVars_fooBad` shows the check is not identically `true` (so the guard
  rejects something and `guardLoop_blockClosed`'s conjuncts are not free).
* **`noLooseBVars_of_looseBVarRange'_le` / `noLooseBVars_iff` /
  `checkNoLooseBVars_isOk_of_closed`** — the *converse*, and instrument 7's dual for the guard as a
  whole.  A guard that rejected everything would satisfy `RejectsNonClosed` trivially and pass
  every instrument here; `noLooseBVars_iff` rules that out by proving the check is exactly
  `looseBVarRange' ≤ d`, so nothing closed is refused.  This upgrades §5's third `#eval` ("0 of
  10902 stored types carry a loose bvar") from evidence to a corollary for any environment whose
  declarations are closed.
* **`guardLoop_ctors_closed` / `guardLoop_blockClosed` / `addInductive_WF_blockClosed` /
  `addInductive_WF_blockClosedFull`** — these are `Except.WF` statements, so **a rejecting input
  satisfies them for free**.  Their content is entirely in the *succeeding* case, and the firing
  instances are §5.1's first `#eval`'s four blocks, where `BlockClosed` and `BlockClosedMembers`
  both hold (`blockClosed_uIndType`, `blockClosedMembers_uIndType`).  Consumed in the direction
  that matters — contraposed, as `rejectsNonClosed` — the *rejecting* case is the content instead,
  and `addInductive_rejects_fooBad` (`Verify/ClosednessPropagation.lean` §4.1) is a firing
  instance of that, proved rather than executed.
* **The trap, named.**  `addInductiveStepWF_of_closed` and `addInductiveStepWF_of_full` have a
  *pristine* axiom set — `[propext, Classical.choice, Quot.sound]`, no frozen axiom, no `sorryAx`
  — and that is worse news than it looks, not better: every remaining difficulty has moved into
  their hypotheses `AddInductiveStepWFClosed` / `AddInductiveStepWFFull`, which are open `Prop`s
  with no known inhabitant.  No instrument in this repo sees an uninhabited hypothesis, because
  they all look at conclusions.  Said here so that the green measurement cannot be misread. -/

/-- Instrument 7 for `mkForall_push_mkLocalDecl`: the degenerate instance, with no hypotheses
left over. -/
theorem mkForall_push_degenerate (fv : FVarId) :
    (({} : LocalContext).mkLocalDecl fv `α (.sort .zero) .default).mkForall
        ((#[] : Array Expr).push (.fvar fv)) ((Expr.bvar 0).instantiate1 (.fvar fv))
      = ({} : LocalContext).mkForall #[] (.forallE `α (.sort .zero) (.bvar 0) .default) :=
  mkForall_push_mkLocalDecl (fvs := []) (by simp) List.nodup_nil (by simp)
    LocalContext.wf_empty LocalContext.find?_empty (by simp) (by simp) (by decide) trivial

/-- Instrument 7 for `AddInductiveRunRealisesClosed`: its `BlockClosed` premise is satisfiable,
at the very block `AddDeclWF.lean` §4 uses as its witness. -/
theorem blockClosed_uIndType : BlockClosed [R10.Wit.uIndType] := by
  intro t ht
  rw [List.mem_singleton] at ht; subst ht
  decide

theorem blockNoFVar_nil : BlockNoFVar [] := fun _ h => absurd h nofun

theorem blockClosed_nil : BlockClosed [] := fun _ h => absurd h nofun

theorem blockClosedMembers_nil : BlockClosedMembers [] := fun _ h => absurd h nofun

/-- Instrument 7 for the member-type half of the guard: satisfiable at the same witness. -/
theorem blockClosedMembers_uIndType : BlockClosedMembers [R10.Wit.uIndType] := by
  intro t ht
  rw [List.mem_singleton] at ht; subst ht
  decide

/-- Instrument 7 for `looseBVarRange'_le_of_noLooseBVars`, **firing**: the check accepts
`fooGood`'s constructor type, so the conclusion `looseBVarRange' = 0` is really derived and not
vacuously guarded. -/
theorem noLooseBVars_fooGood :
    noLooseBVars 0 LooseBVarWitness.fooGoodCtor.type = true := by decide

/-- Instrument 7's **dual** for the same lemma: the check is not identically `true`, so
`guardLoop_blockClosed`'s conjuncts cost something and `rejectsNonClosed` is not vacuous.  This is
the fact `Verify/ClosednessPropagation.lean`'s `addInductive_rejects_fooBad` turns into a
rejection theorem. -/
theorem noLooseBVars_fooBad :
    noLooseBVars 0 LooseBVarWitness.fooBadCtor.type = false := by decide

/-- …and the guard therefore throws on it, by `decide` rather than by execution: the check is
pure, so unlike the acceptance it used to replace, this *is* a kernel proof. -/
theorem checkNoLooseBVars_fooBad_isError :
    (checkNoLooseBVars LooseBVarWitness.fooBadCtor.name
      LooseBVarWitness.fooBadCtor.type).isOk = false := by decide

/-! ### 8.1 Instrument 7 for the fourth check (2026-09-02)

* **`checkUniformIndOccs.WF` / `guardLoop_ctors` / `guardLoop_blockNoFVar` /
  `guardLoop_blockClosed` / `addInductive_WF_blockClosedFull` /
  `addInductive_WF_blockClosedUniform`** — `Except.WF` statements again, so **a rejecting input
  satisfies them for free**, and `BlockUniformOccs names lps np []` holds vacuously
  (`blockUniformOccs_nil`).  The degenerate instance therefore proves nothing, and is recorded as
  such.  The firing instances are the whole running environment:
  `Verify/Inductive/UniformOccMeasure.lean`'s `uio/scanA` runs the **installed**
  `noNonUniformOcc` over 7013 submitted safe constructor types and 11 unsafe ones with 0
  violations, and `uio/scanB` over 7215 post-elimination ones with 0 — so the succeeding case,
  where all the content is, is the normal case rather than a curiosity.
* **`RejectsNonUniform` / `rejectsNonUniform`** — the *rejecting* case is the content, and the
  hypothesis is a negation.  Two things must hold for it to say anything, and neither is visible
  to any instrument that reads conclusions:
  1. `¬ BlockUniformOccs …` must be **inhabited** — otherwise the theorem is a true implication
     with an empty antecedent.  `UniformOccMeasure.lean`'s `uio_not_blockUniformOccs_uioE` and
     `uio_rejectsNonUniform_fires` supply an inhabitant, the arena's `nested-nonuniform-param`
     block, which lean4lean accepted until 2026-09-02;
  2. the check must **not** be identically `false` — otherwise the guard rejects every block and
     the arena breaks.  `uio_ok_of_occ` (no uniform occurrence is refused) and the two scans are
     the dual, and `uio_naive_too_strong` is why: the pruning-free reading of C++'s condition *is*
     identically `false` at every `np ≥ 1`, so this failure mode was a live possibility rather
     than a hypothetical.
* **The trap, again.**  `rejectsNonUniform`'s axiom set is
  `[propext, Classical.choice, Quot.sound]` — clean — and that says nothing about whether it is
  vacuous; the two facts above are what does.  Conversely, the way to make this statement *look*
  stronger while making it weaker would have been to phrase the fourth conjunct with
  `Lean.Level.beq`: the axiom print would still have been clean at the top level, with
  `Lean.Level.instLawfulBEqLevel` reachable only from a hypothesis.  The port avoids that by
  construction (`Lean4Lean.ownLevels`), and `Verify/Guard.lean` check 1 is what would catch a
  regression. -/

/-- Instrument 7 for the fourth conjunct at the degenerate instance: **vacuous**, and recorded as
vacuous. -/
theorem blockUniformOccs_nil (names lps : List Name) (np : Nat) :
    BlockUniformOccs names lps np [] := fun _ h => absurd h nofun

/-- Instrument 7, **firing**, for the fourth conjunct at the same witness §8 uses for the other
three: `R10.Wit.uIndType` passes the installed uniform-occurrence check.  So the new conjunct is
not free-because-empty on the block that every other statement in this file is instantiated at.

`lps := []` is **forced**, not chosen for convenience, and that is itself a measurement of the
check: `uIndType`'s only constructor type is the bare `.const R10.Wit.U []`, a block member at
`np = 0`, so the check demands the block's own levels there (§3.3's T7/T8 in
`UniformOccMeasure.lean`).  At any other `lps` the statement is **false**, which is what
`blockUniformOccs_uIndType_forces_lps` records: the fourth conjunct constrains levels, not merely
argument shapes. -/
theorem blockUniformOccs_uIndType :
    BlockUniformOccs (List.map (·.name) [R10.Wit.uIndType]) [] 0 [R10.Wit.uIndType] := by
  intro t ht
  rw [List.mem_singleton] at ht; subst ht
  decide

/-- Instrument 7's dual for the level half: at a *nonempty* `lps` the same block **fails** the
check.  So `blockUniformOccs_uIndType` is not an artefact of a `lps` that never mattered, and
`RejectsNonUniform`'s hypothesis is inhabited already at this file's own witness — no need to
reach for the arena block. -/
theorem not_blockUniformOccs_uIndType_param :
    ¬ BlockUniformOccs (List.map (·.name) [R10.Wit.uIndType]) [`u] 0 [R10.Wit.uIndType] := by
  intro h
  exact absurd (h _ (List.mem_singleton.2 rfl) _ (List.mem_singleton.2 rfl)) (by decide)

/-- …and hence `Environment.addInductive` **rejects** `[uIndType]` when it is submitted at level
parameters `[u]`: a firing instance of `rejectsNonUniform`, proved rather than executed. -/
theorem addInductive_rejects_uIndType_at_param (env : Environment) (ap : Bool) (fuel : FuelConfig)
    (env' : Environment) :
    Environment.addInductive env [`u] 0 [R10.Wit.uIndType] false ap fuel ≠ .ok env' :=
  rejectsNonUniform env [`u] 0 _ ap fuel not_blockUniformOccs_uIndType_param env'

/-! ## 9. Axiom guards for the fourth check

`#print axioms`, not the absence of a local `sorry`.  Every one of these must print
`[propext, Classical.choice, Quot.sound]` (or a subset): **no frozen axiom from
`Verify/Axioms.lean`**, and in particular neither `Lean.Level.instLawfulBEqLevel` nor
`Lean.Expr.mkData_eq`.

`guardLoop_blockNoFVar`, `addInductive_WF_blockClosedFull` and `addInductive_WF_of_run'` are
*not* in this list, and deliberately: they still reach `Lean.Expr.mkAppData_eq`,
`Lean.Expr.mkData_eq` and `Lean.Level.hasMVar_eq` through `checkNoMVarNoFVar.WF`, exactly as
before this round — that is why the `_closed` chain exists. -/

#print axioms Lean4Lean.checkUniformIndOccs.WF
#print axioms Lean4Lean.guardLoop_ctors_closed
#print axioms Lean4Lean.guardLoop_blockClosed
#print axioms Lean4Lean.addInductive_WF_blockClosedUniform
#print axioms Lean4Lean.addInductive_WF_blockClosed
#print axioms Lean4Lean.rejectsNonUniform
#print axioms Lean4Lean.rejectsNonUniform'
#print axioms Lean4Lean.blockUniformOccs_uIndType
#print axioms Lean4Lean.not_blockUniformOccs_uIndType_param
#print axioms Lean4Lean.addInductive_rejects_uIndType_at_param
