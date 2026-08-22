import Lean4Lean.Theory.Inductive.Decl
import Lean4Lean.Theory.Typing.Meta

/-!
# Metatheory groundwork for `addInduct_WF`

Three groups, in dependency order.

1. **Level re-indexing** (`§ atRec`).  `IsDefEq.instL` already exists
   (`Theory/Typing/Lemmas.lean:595`); what is missing is its specialisation to
   `VInductDecl'.atRec`, together with the syntactic algebra saying that `atRec` commutes
   with the telescope operations and turns `tyApp` into `tyApp'`.  This is what lets a
   `WF` fact stated at the block's own universe numbering type the recursor at the
   recursor's numbering.

2. **Staging** (`§ addConstList`, `§ staging`).  `addIndTypes`/`addIndCtors`/`addIndRecs`
   are all `addConstList`, so the bookkeeping is proved once: monotonicity, what the
   resulting `constants` map is, which names were added, `Ordered` preservation, and
   `addInduct' env D = some _ ↔ D.allNames` fresh and duplicate-free.

3. **Well-formedness of the generated types** (`§ telescopes`, `§ generated types`).
   The telescope typing library (`OnCtx.append_right`, `IsType.mkPi`, `HasType.mkApp'`,
   `HasType.appBVars`), then the inductive types' and constructors' constants, then the
   pieces of the recursor case that are within reach.

`addInduct_WF` itself lives in `Theory/Typing/InductiveLemmas.lean` and is deliberately
not here.
-/

namespace Lean4Lean

/-!
## Notes for anyone continuing this file

**0. Abstract the offsets; prove the widening once about the abstracted shape.**  This is the
technique this file rewards, and it has now paid three times.  Every term the recursor
construction builds is *one formula in a handful of de Bruijn offsets*, reused at several
depths.  Do not prove a fact about the instance you happen to need: name the shape with its
offsets as parameters, prove the moves between offsets once about that shape, and instantiate
at each caller.

* `tyApp'_instAll` / `tyApp'_instAll'` -- the block-type application with the parameter offset
  free; the second was needed because the recursor's major-premise domain puts the parameters
  at `ni + nmin + nm`, not at `ni + j`.
* `recApp_hasType` -- the recursor's five-block spine with the depth `lo` and the block `Ξ`
  above the minors as parameters.  Used at `lo = nf` for the ι-rule's left-hand side and at
  `lo = nxi + nf` for each induction-hypothesis *value*.  Writing it monolithically first and
  then abstracting is fine; abstracting it is what made the second use assembly.
* `ihShape` -- an induction-hypothesis type with `off`/`d` and the two variable positions
  free.  The two moves the ι-rule needs (`off` from `nm + q` to `nm + nmin`, `d` past the `s`
  earlier ihs) are then one lemma each, and `ihType_shift` is five lines instead of a second
  traversal of `ihType`'s definition.

The dual move, for *duplication* rather than traversal, is `recField_facts`: when two callers
need the same bundle of facts, quantify over what they disagree about rather than writing the
bundle twice.  D4 splits the index telescope at `u := r.idx`, the ι-rule at `u := 0`, so `u`
and `L` are universally quantified inside the conclusion.  Re-verify the original caller after
extracting -- that is what makes the refactor safe.

**0b. When a statement is indexed by a length or a depth, carry the index as a *variable
plus an equation*, not as the expression.**  Write `(n : Nat) (as : List _) (h : as.length = n)`
and induct on `n`, not `∀ as, P as.length`.

The reason is specific and it is not "dependent types are fiddly": `(as ++ [a]).length` does
not *reduce* to `as.length + 1`.  So if a dependent type is indexed by `as.length` — a
`Pattern.varN q n`'s `Path`, a `Fin`, a vector — a snoc induction on the list cannot rewrite
the index.  `rw` fails with "motive is not type correct", and constructors of the dependent
type will not even typecheck against the un-normalised index.  Inducting on `n` and
decomposing the list inside keeps every `varN q (n+1)` definitionally a `.var`.

The same move handles truncated subtraction: state `k + as.length = B + 1 + t` rather than
`B = k + as.length - 1 - t`, so callers meet an `omega` goal instead of a `Nat`-subtraction
normal form.  `VExpr.instAll_bvar_get` and
`Pattern.matches_varN_mkApp` (`Theory/Typing/PatternDecode.lean`) are the two instances.

*The sharper form, when the dependent type is the element type of a list.*  If you build a
`List T` where `T` itself reduces — `(varN q (n+1)).Path`, which unfolds to
`Option (varN q n).Path` — then `++`, `List.map` and friends elaborate their **instances** at
the un-reduced type, and `rw [List.length_append]` fails to match even though the two types
are definitionally equal: `rw` is syntactic and the instance is not.  Neither a type
ascription on the body nor `show` on the goal is enough, because the *function* being mapped
carries the un-reduced domain too.  What works is to name the recursion step as a separate
definition at the reduced type and ascribe the mapped function's domain:
`Pattern.argPaths.argPathsSucc` (`Theory/Typing/PatternDecode.lean`) is the worked example,
and its docstring says why.

This has now been the source of the surprise three times, always in the indexing rather than
in the mathematics.  Cost when unprepared: two failed attempts and ~30 lines.  Cost with the
rule in hand: zero.

**1. Check `Theory/Inductive/Telescope.lean` before estimating.**  Twice in this
development a step was priced by its *shape* and turned out to be two applications of a
lemma that was already there with exactly the right side conditions.  `ih_telescope_eq`
was expected to need a closedness argument and collapses by `liftTele_liftTele`;
`indices_closed` was landed for it and then turned out not to be needed at all.  Grep the
telescope algebra first.

**2. Read the current `VEnv.Params` class, not `docs/design-inductive.md` §7.6.**  The
design describes four fields -- `pat_major_not_pi`, `pat_major_prop`, `pat_small`,
`pat_major_canonical` -- that **do not exist** in the class as it stands.  Their absence
retires M1, M2, M3, `VEnv.Sig`, and `IsDefEqU.const_forallE_inv`, i.e. both of the items the
design could see no route to.

An earlier version of this note also said the three `pat_app_*` fields have no consumer.
That was wrong: `pat_app_l_uniq` and `pat_app_uniq` are used at
`Typing/HeadReduction.lean:158` and `:160`.  Only `pat_app_l` was dead, and it has been
deleted.  `pat_wf` has since gained an `OnCtx Γ` hypothesis -- see its docstring for why.

**3. Plumbing habits that have each cost a round.**

Two of the entries below are the same phenomenon: **a `@[simp]` lemma that has already
fired changes what `rw` can see.**  If a rewrite "obviously" applies and does not, check
whether the goal is already displaying the normalised form.

* Prefer standalone `have`s with fully spelled-out statements over `conv_lhs => rw [...]`
  nested inside a `have := by`.  Where a rewrite needs an index lined up, take the length
  as an *equation* and `subst` it -- see `VExpr.map_instAll_bvars'`.
* Isolate arithmetic into named `omega` lemmas (`ih_param_offset`, `rec_tele_offset`,
  `rec_dom_offset`) so the assembly never reasons about offsets inline.
* Do not carry a redundant variable alongside the term it abbreviates.  Dropping `ni` in
  favour of `T.indices.length` in `motiveApp_hasType` removed a whole class of rewriting.
* `rw [VExpr.liftN]` unfolds only the outer constructor; use
  `simp only [VExpr.liftN, ...]` when a `liftN` is buried under one.
* `length_atRecTele` lives in `VInductDecl'`, not `VExpr`, and takes `D` explicitly.
* A lemma stated at cut `i + j` will not `rw` against a term at cut `i`, even when you
  instantiate `j := 0` and the two are definitionally equal -- `rw` is syntactic.  Instantiate
  the lemma into a `have`, `rw [Nat.add_zero]` inside it, and rewrite with that.  This bit
  `liftTele_liftTele_eq_shiftTele` in `onCtxXi`.
* `++` on lists is **left**-associative (`infixl:65`), but `List.append_assoc` is a `simp`
  lemma that normalises to the *right*.  So `a ++ b ++ c` elaborates as `(a ++ b) ++ c` --
  `Ctx.LiftN.zero` applies to it with no `rw` at all -- while anything you prove by `simpa`
  comes out re-associated as `a ++ (b ++ c)`.  Expect `simpa using h` rather than `exact h`
  whenever a context crosses that boundary, and do not "fix" a `rw [← List.append_assoc]`
  that fails: it fails because the term was already left-associated.
-/

open VExpr (mkPi mkLams mkApp bvars liftTele instTele shift shiftTele instAll)

/-! ## Generic list/telescope helpers -/

theorem List.foldlM_option_append {f : α → β → Option α} :
    ∀ {l₁ : List β} {l₂ : List β} {a : α},
      (l₁ ++ l₂).foldlM f a = (l₁.foldlM f a).bind (l₂.foldlM f ·)
  | [], _, a => rfl
  | b :: l₁, l₂, a => by
    simp only [List.cons_append, List.foldlM_cons]
    cases f a b with
    | none => simp
    | some a' => simp

/-! ## `OnCtx` over telescopes -/

theorem OnCtx.append_right : ∀ {Δ Γ}, OnCtx (Δ ++ Γ) P → OnCtx Γ P
  | [], _, h => h
  | _ :: _, _, h => OnCtx.append_right h.1

theorem OnCtx.head_of_append {Δ Γ : List VExpr} (h : OnCtx (Δ ++ A :: Γ) P) : P Γ A :=
  (OnCtx.append_right h).2

/-- Reassociate a declaration-order telescope's context: `(A :: As).reverse ++ Γ` is
`As.reverse ++ (A :: Γ)`. -/
theorem VExpr.tele_ctx_cons (A : VExpr) (As Γ : List VExpr) :
    (A :: As).reverse ++ Γ = As.reverse ++ (A :: Γ) := by simp

/-! ## `atRec`: re-indexing from the block's universes to the recursor's -/

namespace VInductDecl'
variable (D : VInductDecl')

@[simp] theorem length_selfLvls : D.selfLvls.length = D.uvars := by simp [selfLvls]

@[simp] theorem length_ownLvls : D.ownLvls.length = D.uvars := by simp [ownLvls]

/-- The recursor's copy of the block's universe parameters is well-formed at
`recUvars`. -/
theorem selfLvls_wf : ∀ l ∈ D.selfLvls, l.WF D.recUvars := by
  simp only [selfLvls, recUvars, List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩
  by_cases h : D.isLE <;> simp [h, VLevel.WF] <;> omega

/-- Instantiating the block's own parameters `ownLvls` by `selfLvls` gives `selfLvls`:
this is what turns `tyApp` into `tyApp'`. -/
@[simp] theorem ownLvls_inst_selfLvls :
    D.ownLvls.map (VLevel.inst D.selfLvls) = D.selfLvls :=
  VLevel.inst_map_id (by simp)

@[simp] theorem atRecTele_nil : D.atRecTele [] = [] := rfl
@[simp] theorem atRecTele_cons :
    D.atRecTele (A :: As) = D.atRec A :: D.atRecTele As := rfl
@[simp] theorem length_atRecTele : (D.atRecTele As).length = As.length := by simp [atRecTele]
@[simp] theorem atRecTele_append :
    D.atRecTele (As ++ Bs) = D.atRecTele As ++ D.atRecTele Bs := by simp [atRecTele]
@[simp] theorem atRecTele_reverse :
    D.atRecTele As.reverse = (D.atRecTele As).reverse := by simp [atRecTele]
theorem atRecTele_map (f : α → VExpr) (l : List α) :
    D.atRecTele (l.map f) = l.map (fun a => D.atRec (f a)) := by simp [atRecTele, atRec]

/-! ### `atRec` commutes with the telescope algebra -/

@[simp] theorem atRec_sort : D.atRec (.sort u) = .sort (u.inst D.selfLvls) := rfl
@[simp] theorem atRec_bvar : D.atRec (.bvar i) = .bvar i := rfl
@[simp] theorem atRec_app : D.atRec (.app f a) = .app (D.atRec f) (D.atRec a) := rfl
@[simp] theorem atRec_lam : D.atRec (.lam A b) = .lam (D.atRec A) (D.atRec b) := rfl
@[simp] theorem atRec_forallE :
    D.atRec (.forallE A b) = .forallE (D.atRec A) (D.atRec b) := rfl
@[simp] theorem atRec_const :
    D.atRec (.const c ls) = .const c (ls.map (VLevel.inst D.selfLvls)) := rfl

@[simp] theorem atRec_mkPi : D.atRec (mkPi As B) = mkPi (D.atRecTele As) (D.atRec B) := by
  simp [atRec, atRecTele]
@[simp] theorem atRec_mkLams :
    D.atRec (mkLams As b) = mkLams (D.atRecTele As) (D.atRec b) := by simp [atRec, atRecTele]
@[simp] theorem atRec_mkApp :
    D.atRec (f.mkApp as) = (D.atRec f).mkApp (as.map D.atRec) := by
  simp only [atRec, VExpr.instL_mkApp]; rfl
@[simp] theorem atRec_bvars : (bvars lo n).map D.atRec = bvars lo n :=
  VExpr.map_instL_bvars
@[simp] theorem atRec_liftN : D.atRec (e.liftN n k) = (D.atRec e).liftN n k :=
  VExpr.instL_liftN
@[simp] theorem atRec_liftTele :
    D.atRecTele (liftTele n As k) = liftTele n (D.atRecTele As) k := by
  simp [atRecTele, VExpr.instL_liftTele]
@[simp] theorem atRec_shift : D.atRec (shift off d i e j) = shift off d i (D.atRec e) j := by
  simp [VExpr.shift, atRec]
@[simp] theorem atRec_shiftTele :
    D.atRecTele (shiftTele off d i As j) = shiftTele off d i (D.atRecTele As) j := by
  simp [atRecTele, VExpr.instL_shiftTele]

/-- The point of `atRec`: it carries `tyApp` (block numbering) to `tyApp'` (recursor
numbering). -/
@[simp] theorem atRec_tyApp :
    D.atRec (D.tyApp j k args) = D.tyApp' j k (args.map D.atRec) := by
  simp [tyApp, tyApp']

@[simp] theorem atRec_canonType (T : VIndType) :
    D.atRec (T.canonType D) =
      mkPi (D.atRecTele D.params ++ D.atRecTele T.indices) (.sort (D.lvl.inst D.selfLvls)) := by
  simp [VIndType.canonType]

/-! ### The typing transport -/

variable {env : VEnv} {Γ : List VExpr}

/-- The context of a judgment transported by `atRec`. -/
abbrev atRecCtx (Γ : List VExpr) : List VExpr := Γ.map (VExpr.instL D.selfLvls)

theorem atRecCtx_eq_atRecTele : D.atRecCtx Γ = D.atRecTele Γ := rfl

theorem atRec_isDefEq (H : env.IsDefEq D.uvars Γ e₁ e₂ A) :
    env.IsDefEq D.recUvars (D.atRecCtx Γ) (D.atRec e₁) (D.atRec e₂) (D.atRec A) :=
  H.instL D.selfLvls_wf

theorem atRec_hasType (H : env.HasType D.uvars Γ e A) :
    env.HasType D.recUvars (D.atRecCtx Γ) (D.atRec e) (D.atRec A) :=
  H.instL D.selfLvls_wf

theorem atRec_isType (H : env.IsType D.uvars Γ A) :
    env.IsType D.recUvars (D.atRecCtx Γ) (D.atRec A) :=
  H.instL D.selfLvls_wf

theorem atRec_isDefEqU (H : env.IsDefEqU D.uvars Γ e₁ e₂) :
    env.IsDefEqU D.recUvars (D.atRecCtx Γ) (D.atRec e₁) (D.atRec e₂) :=
  H.instL D.selfLvls_wf

theorem atRec_onCtx (H : OnCtx Γ (env.IsType D.uvars)) :
    OnCtx (D.atRecCtx Γ) (env.IsType D.recUvars) :=
  OnCtx.instL D.selfLvls_wf H

end VInductDecl'

/-! ## `addConstList` -/

namespace VEnv

theorem addConst_constants_ne {env env' : VEnv} {name ci n}
    (h : env.addConst name ci = some env') (hn : name ≠ n) :
    env'.constants n = env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; simp [hn]

theorem addConst_constants_none {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') : env.constants name = none := by
  unfold VEnv.addConst at h; split at h <;> simp_all

theorem addConst_eq_none' {env : VEnv} {name ci}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst; rw [h]; exact ⟨_, rfl⟩

@[simp] theorem addConstList_nil {env : VEnv} : env.addConstList [] = some env := rfl

theorem addConstList_cons {env : VEnv} {c cs} :
    env.addConstList (c :: cs) = (env.addConst c.1 c.2).bind (·.addConstList cs) := by
  cases h : env.addConst c.1 c.2 <;> simp [addConstList, List.foldlM, h]

theorem addConstList_append {env : VEnv} {cs ds} :
    env.addConstList (cs ++ ds) = (env.addConstList cs).bind (·.addConstList ds) :=
  List.foldlM_option_append

theorem addConstList_le : ∀ {cs} {env env' : VEnv}, env.addConstList cs = some env' → env ≤ env'
  | [], _, _, h => by cases h; exact .rfl
  | _ :: _, _, _, h => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConst_le h1).trans (addConstList_le h2)

/-- A name not in the list is untouched. -/
theorem addConstList_constants_of_not_mem : ∀ {cs} {env env' : VEnv} {n},
    env.addConstList cs = some env' → n ∉ cs.map (·.1) → env'.constants n = env.constants n
  | [], _, _, _, h, _ => by cases h; rfl
  | c :: cs, env, env', n, h, hn => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    rw [List.map_cons, List.mem_cons, not_or] at hn
    rw [addConstList_constants_of_not_mem h2 hn.2,
      addConst_constants_ne h1 (fun e => hn.1 e.symm)]

/-- Every constant in the list ends up in the environment. -/
theorem addConstList_constants : ∀ {cs} {env env' : VEnv},
    env.addConstList cs = some env' → ∀ c ∈ cs, env'.constants c.1 = some c.2
  | [], _, _, _, _, hc => nomatch hc
  | c :: cs, env, env', h, d, hd => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    cases hd with
    | head => exact (addConstList_le h2).constants (addConst_self h1)
    | tail _ hd => exact addConstList_constants h2 d hd

/-- Success means every name was fresh *and* the list had no duplicate names. -/
theorem addConstList_fresh : ∀ {cs} {env env' : VEnv},
    env.addConstList cs = some env' →
    (∀ n ∈ cs.map (·.1), env.constants n = none) ∧ (cs.map (·.1)).Nodup
  | [], _, _, _ => ⟨by simp, by simp⟩
  | c :: cs, env, env', h => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    have hc : env.constants c.1 = none := addConst_constants_none h1
    obtain ⟨hfresh, hnd⟩ := addConstList_fresh h2
    have hne : c.1 ∉ cs.map (·.1) := fun hm => by
      have h3 := hfresh _ hm; rw [addConst_self h1] at h3; simp at h3
    refine ⟨?_, by rw [List.map_cons]; exact List.nodup_cons.2 ⟨hne, hnd⟩⟩
    rw [List.map_cons]
    rintro n hn
    rcases List.mem_cons.1 hn with rfl | hm
    · exact hc
    · rw [← addConst_constants_ne h1 (fun e => hne (e ▸ hm))]
      exact hfresh _ hm

theorem exists_addConstList : ∀ {cs : List (Name × VConstant)} {env : VEnv},
    (∀ n ∈ cs.map (·.1), env.constants n = none) → (cs.map (·.1)).Nodup →
    ∃ env', env.addConstList cs = some env'
  | [], _, _, _ => ⟨_, rfl⟩
  | c :: cs, env, hfresh, hnd => by
    rw [List.map_cons] at hfresh hnd
    obtain ⟨env₁, h1⟩ := addConst_eq_none' (ci := c.2) (hfresh _ (.head _))
    rw [List.nodup_cons] at hnd
    have key : ∀ n ∈ cs.map (·.1), env₁.constants n = none := fun n hn => by
      rw [addConst_constants_ne h1 (fun e => hnd.1 (e ▸ hn))]
      exact hfresh _ (.tail _ hn)
    obtain ⟨env₂, h2⟩ := exists_addConstList (env := env₁) (cs := cs) key hnd.2
    exact ⟨env₂, by rw [addConstList_cons, h1]; exact h2⟩

theorem addConstList_eq_some_iff {env : VEnv} {cs : List (Name × VConstant)} :
    (∃ env', env.addConstList cs = some env') ↔
      (∀ n ∈ cs.map (·.1), env.constants n = none) ∧ (cs.map (·.1)).Nodup :=
  ⟨fun ⟨_, h⟩ => addConstList_fresh h, fun ⟨h1, h2⟩ => exists_addConstList h1 h2⟩

theorem addConstList_ordered : ∀ {cs} {env env' : VEnv}, Ordered env →
    (∀ c ∈ cs, c.2.WF env) → env.addConstList cs = some env' → Ordered env'
  | [], _, _, h, _, e => by cases e; exact h
  | _ :: _, _, _, h, hw, e => by
    rw [addConstList_cons, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine addConstList_ordered (.const h (hw _ (.head _)) h1) (fun c hc => ?_) h2
    exact (hw c (.tail _ hc)).mono (addConst_le h1)

end VEnv

/-! ## Staging: `addIndTypes` / `addIndCtors` / `addIndRecs` / `addIndRules` -/

namespace VInductDecl'
variable (D : VInductDecl')

@[simp] theorem typeConsts_names : D.typeConsts.map (·.1) = D.blockNames := by
  simp [typeConsts, blockNames]

@[simp] theorem length_typeConsts : D.typeConsts.length = D.nm := by simp [typeConsts]
@[simp] theorem length_ctorConsts : D.ctorConsts.length = D.nmin := by simp [ctorConsts]
@[simp] theorem length_recConsts : D.recConsts.length = D.nm := by simp [recConsts]

theorem allConsts_names :
    D.allNames = D.blockNames ++ D.ctorConsts.map (·.1) ++ D.recConsts.map (·.1) := by
  simp [allNames, allConsts]

end VInductDecl'

namespace VEnv
variable {env env' : VEnv} {D : VInductDecl'}

theorem addIndTypes_le (h : env.addIndTypes D = some env') : env ≤ env' := addConstList_le h
theorem addIndCtors_le (h : env.addIndCtors D = some env') : env ≤ env' := addConstList_le h
theorem addIndRecs_le (h : env.addIndRecs D = some env') : env ≤ env' := addConstList_le h

/-! ### `addIndRules` -/

theorem addDefEqList_le : ∀ (dfs : List VDefEq) (env : VEnv), env ≤ dfs.foldl VEnv.addDefEq env
  | [], _ => .rfl
  | d :: dfs, env => addDefEq_le.trans (addDefEqList_le dfs (env.addDefEq d))

theorem addDefEqList_constants :
    ∀ (dfs : List VDefEq) (env : VEnv), (dfs.foldl VEnv.addDefEq env).constants = env.constants
  | [], _ => rfl
  | d :: dfs, env => addDefEqList_constants dfs (env.addDefEq d)

theorem addDefEqList_defeqs : ∀ (dfs : List VDefEq) (env : VEnv),
    ∀ df ∈ dfs, (dfs.foldl VEnv.addDefEq env).defeqs df
  | [], _, _, h => nomatch h
  | d :: dfs, env, df, hdf => by
    cases hdf with
    | head => exact (addDefEqList_le dfs (env.addDefEq d)).defeqs addDefEq_self
    | tail _ h => exact addDefEqList_defeqs dfs (env.addDefEq d) df h

theorem addDefEqList_ordered : ∀ (dfs : List VDefEq) (env : VEnv), Ordered env →
    (∀ df ∈ dfs, df.WF env) → Ordered (dfs.foldl VEnv.addDefEq env)
  | [], _, h, _ => h
  | d :: dfs, env, h, hw =>
    addDefEqList_ordered dfs (env.addDefEq d) (.defeq h (hw _ (.head _)))
      fun df hdf => (hw df (.tail _ hdf)).mono addDefEq_le

theorem addIndRules_le {env : VEnv} {D : VInductDecl'} : env ≤ env.addIndRules D :=
  addDefEqList_le ..

theorem addIndRules_constants {env : VEnv} {D : VInductDecl'} :
    (env.addIndRules D).constants = env.constants := addDefEqList_constants ..

theorem addIndRules_defeqs {env : VEnv} {D : VInductDecl'} :
    ∀ df ∈ D.iotaRules, (env.addIndRules D).defeqs df :=
  fun df h => addDefEqList_defeqs _ _ df h

theorem addIndRules_ordered {env : VEnv} {D : VInductDecl'} (h : Ordered env)
    (hw : ∀ df ∈ D.iotaRules, df.WF env) : Ordered (env.addIndRules D) :=
  addDefEqList_ordered _ _ h hw

/-- The three constant-adding stages, composed. -/
theorem addInduct'_eq (env : VEnv) (D : VInductDecl') :
    env.addInduct' D = (env.addConstList D.allConsts).map (·.addIndRules D) := by
  show (do
      let env ← env.addIndTypes D
      let env ← env.addIndCtors D
      let env ← env.addIndRecs D
      pure (env.addIndRules D)) = _
  simp only [addIndTypes, addIndCtors, addIndRecs, VInductDecl'.allConsts,
    addConstList_append]
  cases env.addConstList D.typeConsts <;> simp
  rename_i env₁; cases env₁.addConstList D.ctorConsts <;> simp
  rename_i env₂; cases env₂.addConstList D.recConsts <;> simp [Option.map]

theorem addInduct'_le (h : env.addInduct' D = some env') : env ≤ env' := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  exact (addConstList_le h1).trans addIndRules_le

/-- `addInduct'` succeeds exactly when every name it would introduce is fresh and the
names are pairwise distinct. -/
theorem addInduct'_eq_some_iff :
    (∃ env', env.addInduct' D = some env') ↔
      (∀ n ∈ D.allNames, env.constants n = none) ∧ D.allNames.Nodup := by
  show _ ↔ (∀ n ∈ D.allConsts.map (·.1), env.constants n = none) ∧ (D.allConsts.map (·.1)).Nodup
  rw [← addConstList_eq_some_iff (cs := D.allConsts)]
  constructor
  · rintro ⟨env', h⟩
    rw [addInduct'_eq, Option.map_eq_some_iff] at h
    exact ⟨_, h.choose_spec.1⟩
  · rintro ⟨env₁, h⟩
    exact ⟨_, by rw [addInduct'_eq, h]; rfl⟩

theorem addInduct'_constants (h : env.addInduct' D = some env') :
    ∀ c ∈ D.allConsts, env'.constants c.1 = some c.2 := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  intro c hc
  rw [addIndRules_constants]
  exact addConstList_constants h1 c hc

theorem addInduct'_defeqs (h : env.addInduct' D = some env') :
    ∀ df ∈ D.iotaRules, env'.defeqs df := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, _, rfl⟩ := h
  exact addIndRules_defeqs

theorem addInduct'_constants_of_not_mem (h : env.addInduct' D = some env')
    (hn : n ∉ D.allNames) : env'.constants n = env.constants n := by
  rw [addInduct'_eq, Option.map_eq_some_iff] at h
  obtain ⟨env₁, h1, rfl⟩ := h
  rw [addIndRules_constants]
  exact addConstList_constants_of_not_mem h1 hn

/-- The block's type constants are present, with their stored types. -/
theorem addInduct'_types (h : env.addInduct' D = some env')
    (hT : T ∈ D.types) : env'.constants T.name = some ⟨D.uvars, T.type⟩ :=
  addInduct'_constants h _ <| by
    simp only [VInductDecl'.allConsts, List.mem_append]
    exact .inl (.inl (List.mem_map_of_mem hT))

/-- The block's constructors are present, at their derived types. -/
theorem addInduct'_ctors (h : env.addInduct' D = some env')
    (hC : (j, C) ∈ D.ctorsAll) : env'.constants C.name = some ⟨D.uvars, C.type D j⟩ :=
  addInduct'_constants h _ <| by
    simp only [VInductDecl'.allConsts, List.mem_append]
    exact .inl (.inr (List.mem_map_of_mem hC))

/-- The block's recursors are present, at `recType`. -/
theorem addInduct'_recs (h : env.addInduct' D = some env')
    (hT : (T, j) ∈ D.types.zipIdx) :
    env'.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩ :=
  addInduct'_constants h _ <| by
    simp only [VInductDecl'.allConsts, List.mem_append]
    exact .inr (List.mem_map_of_mem hT)

end VEnv

/-! ## Telescope typing -/

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- Introduce a whole declaration-order telescope of `∀`-binders. -/
theorem IsType.mkPi : ∀ {As : List VExpr} {Γ B},
    OnCtx (As.reverse ++ Γ) (env.IsType U) → env.IsType U (As.reverse ++ Γ) B →
    env.IsType U Γ (mkPi As B)
  | [], _, _, _, hB => hB
  | A :: As, Γ, B, hAs, hB => by
    rw [VExpr.tele_ctx_cons] at hAs hB
    exact IsType.forallE (OnCtx.head_of_append hAs) (IsType.mkPi hAs hB)

/-- Introduce a whole declaration-order telescope of `λ`-binders. -/
theorem HasType.mkLams : ∀ {As : List VExpr} {Γ b B},
    OnCtx (As.reverse ++ Γ) (env.IsType U) → env.HasType U (As.reverse ++ Γ) b B →
    env.HasType U Γ (mkLams As b) (mkPi As B)
  | [], _, _, _, _, hb => hb
  | A :: As, Γ, b, B, hAs, hb => by
    rw [VExpr.tele_ctx_cons] at hAs hb
    obtain ⟨_, hA⟩ := OnCtx.head_of_append hAs
    exact .lam hA (HasType.mkLams hAs hb)

variable (henv : Ordered env)
include henv

/-- **The workhorse.**  A function of type `mkPi As B`, weakened into the context of `As`
and applied to `As`' own variables, has type `B`.

This is the typing counterpart of `VExpr.instAll_liftN_bvars`. -/
theorem HasType.appBVars : ∀ {As : List VExpr} {Γ f B},
    OnCtx (As.reverse ++ Γ) (env.IsType U) → env.HasType U Γ f (mkPi As B) →
    env.HasType U (As.reverse ++ Γ) ((f.liftN As.length).mkApp (bvars 0 As.length)) B
  | [], _, f, B, _, hf => by simpa using hf
  | A :: As, Γ, f, B, hAs, hf => by
    rw [VExpr.tele_ctx_cons] at hAs ⊢
    obtain ⟨_, hA⟩ := OnCtx.head_of_append hAs
    -- one step: weaken `f` past `A` and apply it to `.bvar 0`
    have hf1 : env.HasType U (A :: Γ) (f.liftN 1) (.forallE (A.liftN 1) ((mkPi As B).liftN 1 1)) :=
      hf.weakN henv (.one (A := A))
    have hb : env.HasType U (A :: Γ) (.bvar 0) (A.liftN 1) := .bvar .zero
    have happ := hf1.app hb
    rw [VExpr.instN_bvar0] at happ
    have := HasType.appBVars (As := As) (Γ := A :: Γ) hAs happ
    rw [show ((VExpr.app (f.liftN 1) (.bvar 0)).liftN As.length).mkApp (bvars 0 As.length)
          = ((f.liftN (As.length + 1)).mkApp (bvars 0 (As.length + 1))) from by
        rw [VExpr.bvars_succ, VExpr.mkApp_cons]
        simp only [VExpr.liftN, liftVar, Nat.zero_add, Nat.add_zero,
          VExpr.liftN_liftN, Nat.add_comm 1 As.length, if_neg (Nat.lt_irrefl 0)]] at this
    simpa using this

end VEnv

/-! ## Well-formedness of the generated constants -/

variable {env env₁ : VEnv} {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {j : Nat}

/-- The stored type of an inductive type of the block is a well-formed constant. -/
theorem VIndType.WF.constant_wf (h : VIndType.WF env D T) :
    VConstant.WF env ⟨D.uvars, T.type⟩ := h.isType

/-- Stage 1: adding the block's type constants preserves `Ordered`. -/
theorem VInductDecl'.addIndTypes_ordered (henv : VEnv.Ordered env) (h : D.WF env)
    (he : env.addIndTypes D = some env₁) : VEnv.Ordered env₁ := by
  refine VEnv.addConstList_ordered henv (fun c hc => ?_) he
  simp only [VInductDecl'.typeConsts, List.mem_map] at hc
  obtain ⟨T, hT, rfl⟩ := hc
  exact (h.types T hT).constant_wf

/-- The context of a constructor's fields, transported from the block's parameter
telescope to the constructor's own (definitionally equal) copy of it. -/
theorem VIndCtor.WF.defeqCtx (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    ∀ {Δ : List VExpr}, OnCtx (Δ ++ D.params.reverse) (env₁.IsType D.uvars) →
      VEnv.IsDefEqCtx env₁ D.uvars [] (Δ ++ D.params.reverse) (Δ ++ C.params.reverse)
  | [], _ => h.params_eq.symm henv
  | _ :: _, hΔ => .succ (VIndCtor.WF.defeqCtx henv h hΔ.1) hΔ.2.choose_spec

/-! ## Saturated application

`HasArgs env U Γ As as` says that `as` instantiates the declaration-order telescope `As`:
each `aᵢ` is typed at `Aᵢ` with the earlier arguments already substituted.  This is the
hypothesis shape that makes `HasType.mkApp'` -- "apply a function of `mkPi` type to a whole
spine" -- statable, and `VExpr.instAll` (the β-normal form of a saturated `mkLams`) is
exactly the resulting type. -/

namespace VEnv

theorem HasArgs.length_eq {env : VEnv} :
    ∀ {As as}, HasArgs env U Γ As as → As.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simpa using h.length_eq

/-- **Saturated application.**  Applying `f : mkPi As B` to a spine `as` instantiating `As`
gives `instAll B as`. -/
theorem HasType.mkApp' {env : VEnv} :
    ∀ {As as Γ f B}, env.HasArgs U Γ As as → env.HasType U Γ f (mkPi As B) →
      env.HasType U Γ (f.mkApp as) (instAll B as)
  | _, _, _, _, _, .nil, hf => hf
  | A :: As, a :: as, Γ, f, B, .cons ha has, hf => by
    have h1 := hf.app ha
    rw [VExpr.inst_mkPi_zero] at h1
    have hlen : as.length = As.length := has.length_eq.symm.trans VExpr.length_instTele
    rw [VExpr.mkApp_cons, VExpr.instAll_cons, Nat.zero_add, hlen]
    exact HasType.mkApp' has h1

end VEnv

/-! ## The constructor constants -/

variable {env₁ : VEnv} {D : VInductDecl'} {T : VIndType} {C : VIndCtor} {j : Nat}

/-- The parameter context is well-formed, in the block's own copy of it. -/
theorem VIndCtor.WF.onCtxParams (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    OnCtx D.params.reverse (env₁.IsType D.uvars) := (h.params_eq.symm henv).isType

/-- Every prefix of the field telescope is a well-formed context over the block's
parameters. -/
theorem VIndCtor.WF.onCtxFields (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    ∀ i, OnCtx ((((C.fields.take i).map (·.type)).reverse) ++ D.params.reverse)
      (env₁.IsType D.uvars)
  | 0 => h.onCtxParams henv
  | i+1 => by
    rw [List.take_add_one, List.map_append, List.reverse_append, List.append_assoc]
    cases hF : C.fields[i]? with
    | none => simpa using h.onCtxFields henv i
    | some F =>
      refine ⟨h.onCtxFields henv i, F.lvl, ?_⟩
      simpa using (h.fields i F hF).hasType

theorem VIndCtor.WF.onCtxAllFields (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    OnCtx (((C.fields.map (·.type)).reverse) ++ D.params.reverse) (env₁.IsType D.uvars) := by
  simpa using h.onCtxFields henv C.fields.length

/-- **The constructor's stored type is well-formed.**  The content beyond `IsType.mkPi` is
the transport from the block's parameter telescope to the constructor's own copy of it
(F3): `VIndCtor.WF` states the fields and the result over `D.params`, while the stored type
binds `C.params`. -/
theorem VIndCtor.WF.isType (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    env₁.IsType D.uvars [] (C.type D j) := by
  have W := h.defeqCtx henv (Δ := (C.fields.map (·.type)).reverse) (h.onCtxAllFields henv)
  refine (VEnv.IsType.mkPi (As := C.params ++ C.fields.map (·.type)) ?_ ?_)
  · simpa using (W.symm henv).isType
  · simpa using VEnv.IsType.defeqDFC henv W ⟨_, h.result⟩

theorem VIndCtor.WF.constant_wf (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    VConstant.WF env₁ ⟨D.uvars, C.type D j⟩ := h.isType henv

/-! ### `ctorsAll` membership -/

theorem VInductDecl'.mem_ctorsAll (h : (j, C) ∈ D.ctorsAll) :
    ∃ T, D.types[j]? = some T ∧ C ∈ T.ctors := by
  simp only [VInductDecl'.ctorsAll, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨⟨T, j'⟩, hT, C', hC, rfl, rfl⟩ := h
  exact ⟨T, List.mk_mem_zipIdx_iff_getElem?.1 hT, hC⟩

/-- Stage 2: adding the block's constructors preserves `Ordered`. -/
theorem VInductDecl'.addIndCtors_ordered {env env₁ env₂ : VEnv} {D : VInductDecl'}
    (henv₁ : VEnv.Ordered env₁) (h : D.WF env) (he : env.addIndTypes D = some env₁)
    (he2 : env₁.addIndCtors D = some env₂) : VEnv.Ordered env₂ := by
  refine VEnv.addConstList_ordered henv₁ (fun c hc => ?_) he2
  simp only [VInductDecl'.ctorConsts, List.mem_map] at hc
  obtain ⟨⟨j, C⟩, hjC, rfl⟩ := hc
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hjC
  exact (h.ctors env₁ he j T hT C hC).constant_wf henv₁

/-! ## Level slack: `D.lvl` vs. the first type's result level

Design open question 7 asked whether `VLevel.LE` needs an `≈`-congruence in `VLevel.lean`.
It does not, on both counts below. -/

/-- `≤` on `VLevel` respects `≈` on both sides.  Nothing in `VLevel.lean` is needed beyond
`equiv_def`, so this can live downstream. -/
theorem VLevel.LE.congr {a a' b b' : VLevel} (h1 : a ≈ a') (h2 : b ≈ b') (h : a ≤ b) :
    a' ≤ b' := fun ls => by
  rw [← VLevel.equiv_def.1 h1 ls, ← VLevel.equiv_def.1 h2 ls]; exact h ls

/-- Consequently the field level condition transports along `≈` of the block's level: if
the spec's `D.lvl` and the kernel's `stats.resultLevel` differ, they differ only by `≈`,
and the condition is insensitive to that. -/
theorem VIndField.level_congr {l l' m : VLevel} (h : VLevel.imax m l ≤ l) (he : l ≈ l') :
    VLevel.imax m l' ≤ l' :=
  VLevel.LE.congr (VLevel.imax_congr (VLevel.equiv_def.2 fun _ => rfl) he) he h

/-! ## `IsDefEqType` -/

namespace VEnv
variable {env : VEnv}

theorem IsDefEqType.toU (h : env.IsDefEqType U Γ A B) : env.IsDefEqU U Γ A B :=
  let ⟨_, h⟩ := h; ⟨_, h⟩

theorem IsDefEqType.isType_l (h : env.IsDefEqType U Γ A B) : env.IsType U Γ A :=
  let ⟨_, h⟩ := h; ⟨_, h.hasType.1⟩

theorem IsDefEqType.isType_r (h : env.IsDefEqType U Γ A B) : env.IsType U Γ B :=
  let ⟨_, h⟩ := h; ⟨_, h.hasType.2⟩

theorem IsDefEqType.symm (h : env.IsDefEqType U Γ A B) : env.IsDefEqType U Γ B A :=
  let ⟨_, h⟩ := h; ⟨_, h.symm⟩

theorem IsDefEqType.instL (hls : ∀ l ∈ ls, l.WF U') (h : env.IsDefEqType U Γ A B) :
    env.IsDefEqType U' (Γ.map (VExpr.instL ls)) (A.instL ls) (B.instL ls) :=
  let ⟨_, h⟩ := h; ⟨_, h.instL hls⟩

theorem IsDefEqType.weak0 (henv : Ordered env) (h : env.IsDefEqType U [] A B) :
    env.IsDefEqType U Γ A B := let ⟨_, h⟩ := h; ⟨_, h.weak0 henv⟩

theorem IsDefEqType.mono (hle : env ≤ env') (h : env.IsDefEqType U Γ A B) :
    env'.IsDefEqType U Γ A B := let ⟨_, h⟩ := h; ⟨_, h.mono hle⟩

/-- Transport a typing judgment along a type-level definitional equality. -/
theorem IsDefEqType.defeq (h : env.IsDefEqType U Γ A B) (he : env.HasType U Γ e A) :
    env.HasType U Γ e B := let ⟨_, h⟩ := h; h.defeq he

end VEnv

/-! ## Entry points for the recursor case (D1)

These are exactly the two places where the level-instantiation lemma of item 1 does its
work: the block's type constants are declared at `D.uvars`, and the recursor is built at
`D.recUvars`. -/

variable {env : VEnv} {D : VInductDecl'} {T : VIndType}

/-- `atRec` of the canonical type of a block type, in the recursor's numbering. -/
theorem VIndType.WF.atRec_canon (h : VIndType.WF env D T) :
    env.IsDefEqType D.recUvars [] (D.atRec T.type) (D.atRec (T.canonType D)) := by
  have := h.canon.instL D.selfLvls_wf (ls := D.selfLvls)
  simpa [VInductDecl'.atRec] using this

/-- **D1, the constant half.**  `I_j.{selfLvls}` has the canonical pi-type at the
recursor's universe numbering.  This is where `IsDefEq.instL` is consumed: `WF.canon` is
stated at `D.uvars`, the recursor lives at `D.recUvars`. -/
theorem VIndType.WF.tyConst_hasType (henv : VEnv.Ordered env) (h : VIndType.WF env D T)
    (hc : env.constants T.name = some ⟨D.uvars, T.type⟩) {Γ : List VExpr} :
    env.HasType D.recUvars Γ (.const T.name D.selfLvls)
      (mkPi (D.atRecTele D.params ++ D.atRecTele T.indices)
        (.sort (D.lvl.inst D.selfLvls))) := by
  have h1 : env.HasType D.recUvars Γ (.const T.name D.selfLvls) (D.atRec T.type) :=
    VEnv.HasType.const hc D.selfLvls_wf (by simp)
  have h2 := (h.atRec_canon.weak0 henv).defeq h1
  rwa [VInductDecl'.atRec_canonType] at h2

/-- The block's parameter and index telescopes form a well-formed context at the
recursor's numbering. -/
theorem VIndType.WF.onCtxIndicesAtRec (h : VIndType.WF env D T) :
    OnCtx ((D.atRecTele T.indices).reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars) := by
  have := D.atRec_onCtx h.indices
  rwa [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse] at this

/-- The block's parameter telescope alone. -/
theorem VInductDecl'.WF.onCtxParamsAtRec (h : D.WF env) :
    OnCtx (D.atRecTele D.params).reverse (env.IsType D.recUvars) := by
  have := D.atRec_onCtx h.params
  rwa [VInductDecl'.atRecCtx, List.map_reverse] at this

/-! ## B6: telescope weakening

Weakening a context by `n` binders at cut `k` weakens a declaration-order telescope over it
into `liftTele n · k`, and moves the cut past the telescope's own length. -/

/-- **B6.** -/
theorem Ctx.LiftN.tele : ∀ {As : List VExpr} {n k} {Γ Γ' : List VExpr},
    Ctx.LiftN n k Γ Γ' →
    Ctx.LiftN n (k + As.length) (As.reverse ++ Γ) ((liftTele n As k).reverse ++ Γ')
  | [], _, _, _, _, W => by simpa using W
  | A :: As, n, k, Γ, Γ', W => by
    rw [VExpr.tele_ctx_cons, VExpr.liftTele_cons, VExpr.tele_ctx_cons, List.length_cons,
      show k + (As.length + 1) = (k + 1) + As.length from by omega]
    exact Ctx.LiftN.tele (As := As) W.succ

namespace VEnv

/-- The `OnCtx` counterpart of B6: a well-formed telescope stays well-formed after the
context under it is weakened. -/
theorem OnCtx.weakTele {env : VEnv} {U n k} {Γ Γ' : List VExpr} (henv : Ordered env)
    (W : Ctx.LiftN n k Γ Γ') (hΓ' : OnCtx Γ' (env.IsType U)) :
    ∀ {As : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      OnCtx ((liftTele n As k).reverse ++ Γ') (env.IsType U)
  | [], _ => by simpa using hΓ'
  | A :: As, hAs => by
    rw [VExpr.tele_ctx_cons] at hAs
    have hA : env.IsType U Γ A := OnCtx.head_of_append hAs
    rw [VExpr.liftTele_cons, VExpr.tele_ctx_cons]
    exact OnCtx.weakTele henv W.succ ⟨hΓ', hA.weakN henv W⟩ hAs

/-- **Two-block saturated application.**  Apply a *closed* `f : mkPi (As ++ Bs) R` to the
variables of `As` and of `Bs`, where `m` further binders were inserted between the two
blocks.  This is the shape every application in the recursor construction has: the
parameters sit at one offset and the indices/fields at another, with the motives and minors
in between. -/
theorem HasType.appBVars₂ {env : VEnv} {U m} {As Bs Γ₀ Γ₁ : List VExpr} {f R : VExpr}
    (henv : Ordered env) (hfc : VExpr.ClosedN f 0)
    (hf : env.HasType U Γ₀ f (mkPi (As ++ Bs) R))
    (hAs : OnCtx (As.reverse ++ Γ₀) (env.IsType U))
    (hBs : OnCtx (Bs.reverse ++ As.reverse ++ Γ₀) (env.IsType U))
    (W : Ctx.LiftN m 0 (As.reverse ++ Γ₀) Γ₁)
    (hΓ₁ : OnCtx Γ₁ (env.IsType U)) :
    env.HasType U ((liftTele m Bs).reverse ++ Γ₁)
      (f.mkApp (bvars (Bs.length + m) As.length ++ bvars 0 Bs.length))
      (R.liftN m Bs.length) := by
  -- step 1: apply to the `As` block
  rw [VExpr.mkPi_append] at hf
  have h1 := HasType.appBVars henv hAs hf
  rw [hfc.liftN_eq (Nat.zero_le _)] at h1
  -- step 2: weaken past the `m` inserted binders
  have h2 := h1.weakN henv W
  rw [VExpr.liftN_mkApp_bvars_lo (Nat.le_refl 0), hfc.liftN_eq (Nat.zero_le _),
    VExpr.liftN_mkPi, Nat.zero_add] at h2
  -- step 3: apply to the `Bs` block
  have hBs' : OnCtx ((liftTele m Bs).reverse ++ Γ₁) (env.IsType U) :=
    OnCtx.weakTele henv W hΓ₁ (by rw [← List.append_assoc]; exact hBs)
  have h3 := HasType.appBVars henv hBs' h2
  rw [VExpr.liftN_mkApp_bvars_lo (Nat.zero_le _), hfc.liftN_eq (Nat.zero_le _),
    ← VExpr.mkApp_append] at h3
  simpa using h3

end VEnv

/-! ## `HasArgs` for a `bvars` spine

The recursor's ι-rules and induction-hypothesis *values* apply a constant to a mixture of
variable blocks and genuine terms, so `appBVars₂` is not enough there and a real `HasArgs`
for a variable block is needed.  A telescope `As` sitting contiguously in the context, `k`
binders down, is instantiated by its own variables `bvars k |As|` -- against the telescope
re-indexed as `liftTele (k + |As|) As`, which is exactly what `Lookup` assigns. -/

namespace VExpr

/-- Instantiating a freshly-inserted variable one cut below where it was inserted. -/
theorem inst_bvar_liftN : ∀ (e : VExpr) (m j : Nat),
    (e.liftN (m+1) (j+1)).inst (.bvar m) j = e.liftN m j
  | .bvar i, m, j => by
    show instVar (liftVar (m+1) i (j+1)) (VExpr.bvar m) j = VExpr.bvar (liftVar m i j)
    rcases Nat.lt_or_ge i j with h | h
    · rw [liftVar_lt (show i < j+1 by omega), liftVar_lt h]
      simp only [instVar, if_pos h]
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · rw [liftVar_lt (Nat.lt_succ_self _), liftVar_le (Nat.le_refl _)]
        simp only [instVar, if_neg (Nat.lt_irrefl _)]
        show VExpr.liftN j (VExpr.bvar m) 0 = _
        rw [VExpr.liftN, liftVar_base']
      · rw [liftVar_le (show j+1 ≤ i by omega), liftVar_le (show j ≤ i by omega)]
        simp only [instVar, if_neg (show ¬ (m+1+i < j) by omega),
          if_neg (show ¬ (m+1+i = j) by omega)]
        congr 1; omega
  | .sort _, _, _ | .const .., _, _ => rfl
  | .app f a, m, j => by simp only [liftN, inst, inst_bvar_liftN]
  | .lam A b, m, j => by
    simp only [liftN, inst, inst_bvar_liftN A m j, inst_bvar_liftN b m (j+1)]
  | .forallE A b, m, j => by
    simp only [liftN, inst, inst_bvar_liftN A m j, inst_bvar_liftN b m (j+1)]

theorem instTele_bvar_liftTele : ∀ {As : List VExpr} {m j : Nat},
    instTele (.bvar m) (liftTele (m+1) As (j+1)) j = liftTele m As j
  | [], _, _ => rfl
  | A :: As, m, j => by
    rw [liftTele_cons, instTele_cons, inst_bvar_liftN, liftTele_cons,
      instTele_bvar_liftTele (As := As) (m := m) (j := j+1)]

end VExpr

theorem Lookup.append : ∀ (Ξ : List VExpr) {A Γ},
    Lookup (Ξ ++ A :: Γ) Ξ.length (A.liftN (Ξ.length + 1))
  | [], _, _ => .zero
  | B :: Ξ, A, Γ => by
    have := (Lookup.append Ξ (A := A) (Γ := Γ)).succ (A := B)
    rw [show (A.liftN (Ξ.length + 1)).lift = A.liftN (Ξ.length + 1 + 1) from
      VExpr.liftN_liftN ..] at this
    simpa using this

namespace VEnv

/-- **The variable spine of a telescope.**  If `As` sits in the context `k` binders down,
its own variables instantiate it. -/
theorem HasArgs.bvars {env : VEnv} {U : Nat} {Δ : List VExpr} :
    ∀ {As Γ₀ : List VExpr},
      env.HasArgs U (Δ ++ As.reverse ++ Γ₀) (liftTele (Δ.length + As.length) As)
        (bvars Δ.length As.length)
  | [], _ => by simpa using HasArgs.nil
  | A :: As, Γ₀ => by
    rw [List.append_assoc, VExpr.tele_ctx_cons, ← List.append_assoc, List.length_cons,
      show Δ.length + (As.length + 1) = (Δ.length + As.length) + 1 from by omega,
      VExpr.liftTele_cons, VExpr.bvars_succ]
    refine HasArgs.cons (.bvar ?_) ?_
    · simpa using Lookup.append (Ξ := Δ ++ As.reverse) (A := A) (Γ := Γ₀)
    · rw [VExpr.instTele_bvar_liftTele]
      exact HasArgs.bvars (Δ := Δ) (As := As) (Γ₀ := A :: Γ₀)

/-! ### Monotonicity of the well-formedness data -/

theorem HasArgs.mono {env env' : VEnv} (hle : env ≤ env') :
    ∀ {As as}, env.HasArgs U Γ As as → env'.HasArgs U Γ As as
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h1.mono hle) (h2.mono hle)

theorem IsDefEqCtx.mono {env env' : VEnv} (hle : env ≤ env') :
    ∀ {Γ₀ Γ₁ Γ₂}, VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂ → VEnv.IsDefEqCtx env' U Γ₀ Γ₁ Γ₂
  | _, _, _, .zero => .zero
  | _, _, _, .succ h1 h2 => .succ (h1.mono hle) (h2.mono hle)

end VEnv

theorem VIndField.WF.mono {env env' : VEnv} {D : VInductDecl'} {Γ : List VExpr} {i F}
    (hle : env ≤ env') (h : VIndField.WF env D Γ i F) : VIndField.WF env' D Γ i F where
  hasType := h.hasType.mono hle
  level := h.level
  pos := by
    have hp := h.pos
    revert hp; cases F.recArg with
    | none => exact fun ⟨A, h1, h2⟩ => ⟨A, h1, h2.mono hle⟩
    | some r =>
      exact fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        ⟨h1, h2, h3, h4, OnCtx.mono (fun hh => hh.mono hle) h5, h6.mono hle,
          fun T' hT' => (h7 T' hT').mono hle, h8.mono hle⟩

theorem VIndCtor.WF.mono {env env' : VEnv} {D : VInductDecl'} {j T C}
    (hle : env ≤ env') (h : VIndCtor.WF env D j T C) : VIndCtor.WF env' D j T C where
  params_len := h.params_len
  params_eq := h.params_eq.mono hle
  fields i F hF := (h.fields i F hF).mono hle
  args_len := h.args_len
  args_fresh := h.args_fresh
  args_ty := h.args_ty.mono hle
  result := h.result.mono hle

/-! ## The recursor's working environment -/

theorem VIndType.WF.mono {env env' : VEnv} {D : VInductDecl'} {T : VIndType}
    (hle : env ≤ env') (h : VIndType.WF env D T) : VIndType.WF env' D T where
  indices := OnCtx.mono (fun hh => hh.mono hle) h.indices
  isType := h.isType.mono hle
  canon := h.canon.mono hle

/-- The situation in which the recursor is built: an ordered environment containing the
block's type constants at their stored types, in which every type of the block is
well-formed.  `addIndTypes` followed by `addIndCtors` produces exactly this. -/
structure VInductDecl'.RecCtx (env : VEnv) (D : VInductDecl') : Prop where
  ordered : env.Ordered
  params : OnCtx D.params.reverse (env.IsType D.uvars)
  types : ∀ T ∈ D.types, VIndType.WF env D T
  consts : ∀ T ∈ D.types, env.constants T.name = some ⟨D.uvars, T.type⟩
  ctors : ∀ j (T : VIndType), D.types[j]? = some T →
    ∀ (C : VIndCtor), C ∈ T.ctors → VIndCtor.WF env D j T C
  ctorConsts : ∀ j (C : VIndCtor), (j, C) ∈ D.ctorsAll →
    env.constants C.name = some ⟨D.uvars, C.type D j⟩

/-- `RecCtx` from the declaration's well-formedness and any environment above the one the
block's types were added to. -/
theorem VInductDecl'.WF.recCtx {env env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
    (h : D.WF env) (he : env.addIndTypes D = some env₁)
    (he₂ : env₁.addIndCtors D = some env₂) (hle : env₂ ≤ env₃)
    (henv₃ : env₃.Ordered) : D.RecCtx env₃ where
  ordered := henv₃
  params := OnCtx.mono (fun hh => hh.mono (le₁₃ he he₂ hle)) h.params
  types T hT := (h.types T hT).mono (le₁₃ he he₂ hle)
  consts T hT := (le₂₃ he₂ hle).constants <|
    VEnv.addConstList_constants he (T.name, ⟨D.uvars, T.type⟩) (List.mem_map_of_mem hT)
  ctors j T hT C hC := (h.ctors env₁ he j T hT C hC).mono (le₂₃ he₂ hle)
  ctorConsts j C hC := hle.constants <|
    VEnv.addConstList_constants he₂ (C.name, ⟨D.uvars, C.type D j⟩)
      (List.mem_map_of_mem hC)
where
  /-- `env ≤ env₃` -/
  le₁₃ {env env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
      (he : env.addIndTypes D = some env₁) (he₂ : env₁.addIndCtors D = some env₂)
      (hle : env₂ ≤ env₃) : env ≤ env₃ :=
    (VEnv.addIndTypes_le he).trans ((VEnv.addIndCtors_le he₂).trans hle)
  /-- `env₁ ≤ env₃` -/
  le₂₃ {env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
      (he₂ : env₁.addIndCtors D = some env₂) (hle : env₂ ≤ env₃) : env₁ ≤ env₃ :=
    (VEnv.addIndCtors_le he₂).trans hle

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

theorem elimLvl_wf : D.elimLvl.WF D.recUvars := by
  simp only [elimLvl, recUvars]
  by_cases h : D.isLE <;> simp [h, VLevel.WF]

theorem RecCtx.onCtxParams (hR : D.RecCtx env) :
    OnCtx (D.atRecTele D.params).reverse (env.IsType D.recUvars) := by
  have := D.atRec_onCtx hR.params
  rwa [VInductDecl'.atRecCtx, List.map_reverse] at this

theorem RecCtx.onCtxIndices (hR : D.RecCtx env) {T : VIndType} (hT : T ∈ D.types) :
    OnCtx ((D.atRecTele T.indices).reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars) := (hR.types T hT).onCtxIndicesAtRec

theorem getD_types (hT : D.types[t]? = some T) : D.types.getD t default = T := by
  rw [List.getD_eq_getElem?_getD, hT]; rfl

/-! ### D1: an inductive type of the block, saturated -/

/-- **D1.**  `I_t.{selfLvls}` applied to the parameters -- which sit `T.indices.length + m`
binders away -- and to its own index variables is a type, at the recursor's universe
numbering.  `m` is the number of binders (motives, minors) inserted between the parameter
block and the index block. -/
theorem tyApp'_hasType (hR : D.RecCtx env) {t : Nat} {T : VIndType}
    (hT : D.types[t]? = some T) {m : Nat} {Γ₁ : List VExpr}
    (W : Ctx.LiftN m 0 (D.atRecTele D.params).reverse Γ₁)
    (hΓ₁ : OnCtx Γ₁ (env.IsType D.recUvars)) :
    env.HasType D.recUvars ((liftTele m (D.atRecTele T.indices)).reverse ++ Γ₁)
      (D.tyApp' t (T.indices.length + m) (bvars 0 T.indices.length))
      (.sort (D.lvl.inst D.selfLvls)) := by
  have hmem : T ∈ D.types := List.mem_of_getElem? hT
  have hf := (hR.types T hmem).tyConst_hasType hR.ordered (hR.consts T hmem) (Γ := [])
  have h := VEnv.HasType.appBVars₂ (As := D.atRecTele D.params) (Bs := D.atRecTele T.indices)
    (Γ₀ := []) (m := m) hR.ordered (f := .const T.name D.selfLvls) trivial
    (by simpa using hf) (by simpa using hR.onCtxParams)
    (by simpa using hR.onCtxIndices hmem) (by simpa using W) hΓ₁
  simpa [VInductDecl'.tyApp', VInductDecl'.np, hT, VExpr.liftN] using h

/-! ### D3: the motives -/

/-- **D3.**  Motive `t` is a type in the context `params ++ motives<t`. -/
theorem motiveType_isType (hR : D.RecCtx env) {t : Nat} {T : VIndType}
    (hT : D.types[t]? = some T) {M : List VExpr} (hMlen : M.length = t)
    (hM : OnCtx (M ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars)) :
    env.IsType D.recUvars (M ++ (D.atRecTele D.params).reverse) (D.motiveType t) := by
  have hmem : T ∈ D.types := List.mem_of_getElem? hT
  have W : Ctx.LiftN t 0 (D.atRecTele D.params).reverse (M ++ (D.atRecTele D.params).reverse) :=
    .zero M hMlen
  have hI : OnCtx ((liftTele t (D.atRecTele T.indices)).reverse ++
      (M ++ (D.atRecTele D.params).reverse)) (env.IsType D.recUvars) :=
    VEnv.OnCtx.weakTele hR.ordered W hM (hR.onCtxIndices hmem)
  rw [VInductDecl'.motiveType, getD_types hT]
  exact VEnv.IsType.mkPi hI (VEnv.IsType.forallE ⟨_, tyApp'_hasType hR hT W hM⟩
    ⟨_, VEnv.HasType.sort (Γ := _) elimLvl_wf⟩)

/-- The motive telescope is a well-formed context over the parameters. -/
theorem onCtxMotivesTake (hR : D.RecCtx env) : ∀ t, t ≤ D.nm →
    OnCtx (((List.range t).map D.motiveType).reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars)
  | 0, _ => by simpa using hR.onCtxParams
  | t+1, ht => by
    obtain ⟨T, hT⟩ : ∃ T, D.types[t]? = some T :=
      ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht)⟩
    rw [List.range_succ, List.map_append, List.reverse_append, List.append_assoc]
    exact ⟨onCtxMotivesTake hR t (by omega),
      motiveType_isType hR hT (by simp) (onCtxMotivesTake hR t (by omega))⟩

theorem onCtxMotives (hR : D.RecCtx env) :
    OnCtx (D.motives.reverse ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars) :=
  onCtxMotivesTake hR D.nm (Nat.le_refl _)

end VInductDecl'


/-! ## Closedness of a well-formed telescope

D4 has to identify two re-indexings of the same index telescope, which is only possible
because the telescope's entries are closed at the parameter count. -/

theorem OnCtx.ctxClosed {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Γ}, OnCtx Γ (env.IsType U) → CtxClosed Γ
  | [], _ => trivial
  | _ :: _, ⟨h1, _, h2⟩ => ⟨h1.ctxClosed henv, h2.closedN henv (h1.ctxClosed henv)⟩

theorem VExpr.ClosedTele.of_onCtx {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {As Γ : List VExpr}, OnCtx (As.reverse ++ Γ) (env.IsType U) →
      VExpr.ClosedTele As Γ.length
  | [], _, _ => trivial
  | A :: As, Γ, h => by
    rw [VExpr.tele_ctx_cons] at h
    have hΓ : OnCtx (A :: Γ) (env.IsType U) := OnCtx.append_right h
    refine ⟨hΓ.2.choose_spec.closedN henv (hΓ.1.ctxClosed henv), ?_⟩
    simpa using VExpr.ClosedTele.of_onCtx (As := As) (Γ := A :: Γ) henv h

/-- The index telescope of a block type is closed at the parameter count. -/
theorem VIndType.WF.indices_closed {env : VEnv} {D : VInductDecl'} {T : VIndType}
    (henv : env.Ordered) (h : VIndType.WF env D T) :
    VExpr.ClosedTele T.indices D.np := by
  have := VExpr.ClosedTele.of_onCtx henv h.indices
  simpa using this

/-! ## Weakening a `HasArgs` -/

namespace VExpr

theorem liftTele_instTele : ∀ {As : List VExpr} {a n k j},
    liftTele n (instTele a As j) (k + j)
      = instTele (a.liftN n k) (liftTele n As (k + j + 1)) j
  | [], _, _, _, _ => rfl
  | A :: As, a, n, k, j => by
    rw [instTele_cons, liftTele_cons, liftTele_cons, instTele_cons, liftN_instN_hi]
    refine congrArg _ ?_
    rw [show k + j + 1 = k + (j + 1) from by omega,
      liftTele_instTele (As := As) (a := a) (n := n) (k := k) (j := j + 1),
      show k + (j + 1) + 1 = k + j + 1 + 1 from by omega]

end VExpr

namespace VEnv

theorem HasArgs.instL {env : VEnv} {U U' : Nat} {Γ : List VExpr} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {As as}, env.HasArgs U Γ As as →
      env.HasArgs U' (Γ.map (VExpr.instL ls)) (As.map (VExpr.instL ls))
        (as.map (VExpr.instL ls))
  | _, _, .nil => .nil
  | _, _, .cons ha h => by
    refine .cons (ha.instL hls) ?_
    have ih := HasArgs.instL hls h
    rwa [VExpr.instL_instTele] at ih

theorem HasArgs.weakN {env : VEnv} {U n k} {Γ Γ' : List VExpr} (henv : Ordered env)
    (W : Ctx.LiftN n k Γ Γ') :
    ∀ {As as}, env.HasArgs U Γ As as →
      env.HasArgs U Γ' (liftTele n As k) (as.map (·.liftN n k))
  | _, _, .nil => .nil
  | _, _, .cons ha h => by
    refine .cons (ha.weakN henv W) ?_
    have ih := HasArgs.weakN henv W h
    rwa [show k = k + 0 from rfl, VExpr.liftTele_instTele, Nat.add_zero] at ih

end VEnv

/-- **The offset the two routes into D4 must agree on.**

`args_ty` places the block's parameters at `nxi + i` in the recursive field's own
`ξ`-context; the two weakenings that carry it into minor `q`'s `s`-th induction hypothesis
add `off = nm + q` (between the fields and the parameters) and `d = nf - i + s` (below the
fields).  Independently, `ihTypes` reads motive `r.idx` at
`nxi + s + nf + q + (nm - 1 - r.idx)`, which puts the `nm` motives immediately below the
parameters -- i.e. the parameters at `nxi + s + nf + q + nm`.  The two agree, which is what
lets D4 identify the telescope `args_ty` supplies with the one the motive's type demands. -/
theorem VInductDecl'.ih_param_offset {nxi i s nf q nm : Nat} (h : i ≤ nf) :
    nxi + i + (nm + q) + (nf - i + s) = nxi + s + nf + q + nm := by omega

/-! ## The telescope identification D4 needs

Two routes reach the same telescope inside an induction hypothesis:

* `args_ty` supplies `liftTele (nxi+i) X` in the recursive field's own `ξ`-context, which
  the two weakenings turn into `liftTele d (liftTele off (liftTele (nxi+i) X) (nxi+i)) nxi`;
* the motive's type supplies `liftTele L (liftTele u X)`, where `L` is the lift `Lookup`
  assigns to motive `u`.

They agree, and -- pleasantly -- with no closedness hypothesis at all: each side collapses
by `liftTele_liftTele`, and `ih_param_offset` supplies the arithmetic. -/

theorem VExpr.liftTele_collapse₃ {X : List VExpr} {a off d nxi : Nat} (h : nxi ≤ a + off) :
    liftTele d (liftTele off (liftTele a X 0) a) nxi = liftTele (a + off + d) X 0 := by
  rw [liftTele_liftTele (Nat.zero_le _) (by omega),
    liftTele_liftTele (Nat.zero_le _) (by omega)]

theorem VExpr.liftTele_collapse₂ {X : List VExpr} {u L : Nat} :
    liftTele L (liftTele u X 0) 0 = liftTele (u + L) X 0 :=
  liftTele_liftTele (Nat.le_refl _) (by omega)

/-- **The telescope identification.**  `harith` is `ih_param_offset` plus
`u + (nm - 1 - u) + 1 = nm` (valid for `u < nm`). -/
theorem VInductDecl'.ih_telescope_eq {X : List VExpr} {a off d nxi u L : Nat}
    (h : nxi ≤ a + off) (harith : a + off + d = u + L) :
    liftTele d (liftTele off (liftTele a X 0) a) nxi = liftTele L (liftTele u X 0) 0 := by
  rw [VExpr.liftTele_collapse₃ h, VExpr.liftTele_collapse₂, harith]

/-! ## `instAll` on a `bvars` spine

Applying a function to a spine `bvars L np ++ bvars 0 ni` and then instantiating the `ni`
index arguments by genuine terms `π` leaves the parameter block shifted down by `ni` and
replaces the index block by `π` itself. -/

namespace VExpr

theorem instAll_bvar_ge : ∀ {as : List VExpr} {j k}, k + as.length ≤ j →
    instAll (.bvar j) as k = .bvar (j - as.length)
  | [], _, _, _ => by simp
  | a :: as, j, k, h => by
    simp only [List.length_cons] at h
    rw [instAll_cons,
      show (VExpr.bvar j).inst a (k + as.length) = .bvar (j - 1) from by
        simp only [inst, instVar, if_neg (show ¬ (j < k + as.length) by omega),
          if_neg (show ¬ (j = k + as.length) by omega)],
      instAll_bvar_ge (show k + as.length ≤ j - 1 by omega)]
    simp only [List.length_cons]
    congr 1
    omega

theorem map_instAll_bvars_ge {as : List VExpr} {lo n : Nat} (h : as.length ≤ lo) :
    (bvars lo n).map (instAll · as 0) = bvars (lo - as.length) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bvars_succ, List.map_cons, ih, bvars_succ,
      instAll_bvar_ge (show 0 + as.length ≤ lo + n by omega)]
    congr 2
    omega

/-- The identity spine, instantiated by `as`, returns `as`. -/
theorem map_instAll_bvars : ∀ (as : List VExpr),
    (bvars 0 as.length).map (instAll · as 0) = as
  | [] => rfl
  | a :: as => by
    have h1 : instAll (VExpr.bvar (0 + as.length)) (a :: as) 0 = a := by
      rw [instAll_cons,
        show (VExpr.bvar (0 + as.length)).inst a (0 + as.length) = a.liftN as.length 0 from by
          simp [inst, instVar],
        instAll_liftN]
    have h2 : (bvars 0 as.length).map (instAll · (a :: as) 0) = as := by
      have hc : (bvars 0 as.length).map (instAll · (a :: as) 0)
          = (bvars 0 as.length).map (instAll · as 0) := by
        refine List.map_congr_left fun e he => ?_
        obtain ⟨v, hv, rfl⟩ := mem_bvars.1 he
        rw [instAll_cons,
          show (VExpr.bvar (0 + v)).inst a (0 + as.length) = .bvar (0 + v) from by
            simp only [inst, instVar, Nat.zero_add, if_pos hv]]
      rw [hc, map_instAll_bvars]
    rw [List.length_cons, bvars_succ, List.map_cons, h1, h2]

end VExpr

/-! ## The `addInduct'` assembly

`addInduct'` is four stages; three of them are now discharged.  Stating the composition
with the remaining two as hypotheses fixes exactly what D6 and E5 must deliver, and lets
everything else be reviewed independently of them. -/

namespace VEnv

theorem addInduct'_stages {env env' : VEnv} {D : VInductDecl'}
    (h : env.addInduct' D = some env') :
    ∃ env₁ env₂ env₃, env.addIndTypes D = some env₁ ∧ env₁.addIndCtors D = some env₂ ∧
      env₂.addIndRecs D = some env₃ ∧ env' = env₃.addIndRules D := by
  rw [show env.addInduct' D
      = (env.addIndTypes D).bind (fun e₁ => (e₁.addIndCtors D).bind
          (fun e₂ => (e₂.addIndRecs D).bind (fun e₃ => some (e₃.addIndRules D)))) from rfl,
    Option.bind_eq_some_iff] at h
  obtain ⟨env₁, h1, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨env₂, h2, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨env₃, h3, h4⟩ := h
  exact ⟨env₁, env₂, env₃, h1, h2, h3, (Option.some_inj.1 h4).symm⟩

end VEnv

/-- **`addInduct'` preserves `Ordered`**, modulo the two obligations that remain.

* `hrec` is D6 (`recType_isType`): each recursor's type is a well-formed constant in the
  environment that already has the block's types and constructors.
* `hrules` is E5 (`iotaRule_WF`): each ι-rule is a well-formed `VDefEq` in the environment
  the recursors have just been added to.  It is stated over the *staged* environments, like
  `hrec`: `env ≤ env₃` alone says nothing about `env₃` containing the block's types,
  constructors or recursors, while every ι-rule's lhs is `I_j.rec` applied to a constructor
  application, so the weaker form is not provable.

Everything else -- the three `addConstList` stages, the type constants (`VIndType.WF`), the
constructor constants (`VIndCtor.WF.isType`, which carries the F3 parameter transport), and
the `addDefEq` fold -- is proved. -/
theorem VInductDecl'.addInduct'_ordered {env env' : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) (h : D.WF env)
    (hrec : ∀ {env₁ env₂ : VEnv}, env.addIndTypes D = some env₁ →
      env₁.addIndCtors D = some env₂ → ∀ c ∈ D.recConsts, VConstant.WF env₂ c.2)
    (hrules : ∀ {env₁ env₂ env₃ : VEnv}, env.addIndTypes D = some env₁ →
      env₁.addIndCtors D = some env₂ → env₂.addIndRecs D = some env₃ →
      ∀ df ∈ D.iotaRules, df.WF env₃)
    (he : env.addInduct' D = some env') : env'.Ordered := by
  obtain ⟨env₁, env₂, env₃, h1, h2, h3, rfl⟩ := VEnv.addInduct'_stages he
  have o1 := VInductDecl'.addIndTypes_ordered henv h h1
  have o2 := VInductDecl'.addIndCtors_ordered o1 h h1 h2
  have o3 := VEnv.addConstList_ordered o2 (hrec h1 h2) h3
  exact VEnv.addIndRules_ordered o3 (hrules h1 h2 h3)

/-! ## Arities of a constructor's stored type

These are what a `ParamsExtra.ctor_ty`-style obligation needs: the pi-arity of the stored
constructor type, and the head-arity of its result. -/

theorem VExpr.piArity_mkApp {f : VExpr} (h : f.piArity = 0) :
    ∀ {as}, (VExpr.mkApp f as).piArity = 0
  | [] => h
  | _ :: _ => VExpr.piArity_mkApp (f := .app _ _) rfl

/-- The result of a constructor is an application, never a `∀`. -/
@[simp] theorem VIndCtor.canonResult_piArity (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (C.canonResult D j).piArity = 0 := VExpr.piArity_mkApp rfl

/-- **The constructor's arity.**  The stored type binds exactly the parameters and the
fields; nothing further, because the result is an application. -/
theorem VIndCtor.type_piArity (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (C.type D j).piArity = C.params.length + C.fields.length := by
  rw [VIndCtor.type, VExpr.piArity_mkPi, VIndCtor.canonResult_piArity, Nat.add_zero,
    List.length_append, List.length_map]

/-- **The head-arity of the constructor's result.**  `I_j` is applied to the parameters and
to `C.args`; by `VIndCtor.WF.args_len` that count is `D.np + T.indices.length`, the same for
every constructor of `T` -- which is what makes a per-name head-arity well defined. -/
theorem VIndCtor.canonResult_appArity (C : VIndCtor) (D : VInductDecl') (j : Nat) :
    (C.canonResult D j).appArity = D.np + C.args.length := by
  rw [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.appArity_mkApp]
  simp [VExpr.appArity]

theorem VIndCtor.WF.canonResult_appArity {env : VEnv} {D : VInductDecl'} {j T C}
    (h : VIndCtor.WF env D j T C) :
    (C.canonResult D j).appArity = D.np + T.indices.length := by
  rw [VIndCtor.canonResult_appArity, h.args_len]

/-- `VIndCtor.WF.result`, transported to the constructor's **own** copy of the parameter
telescope -- which is the context `C.type D j` actually binds (F3).  `WF.result` is stated
over `D.params`; a consumer that reads the binder list off `ci.type` gets `C.params`, and
the two are only definitionally equal.  This is the transport that joins them. -/
theorem VIndCtor.WF.result' {env₁ : VEnv} {D : VInductDecl'} {j T C}
    (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    env₁.HasType D.uvars ((C.fields.map (·.type)).reverse ++ C.params.reverse)
      (C.canonResult D j) (.sort D.lvl) :=
  VEnv.HasType.defeqDFC henv (h.defeqCtx henv (h.onCtxAllFields henv)) h.result

/-! ## D6's body: the recursor's codomain

`motive_j` applied to the index variables and to the major premise.  Everything applied here
is a variable, so it goes through `HasArgs.bvars` + `mkApp'`.  Two offset identities make it
work, and they are isolated as `omega` lemmas below so the assembly never has to reason
about arithmetic inline. -/

/-- `HasArgs` transported from the block's universe numbering to the recursor's. -/
theorem VInductDecl'.atRec_hasArgs {env : VEnv} (D : VInductDecl') {Γ As as : List VExpr}
    (h : env.HasArgs D.uvars Γ As as) :
    env.HasArgs D.recUvars (D.atRecCtx Γ) (D.atRecTele As) (as.map D.atRec) :=
  h.instL D.selfLvls_wf

/-- Offset 3: the minor premise's telescope collapse.  `nf` is the field count, `nr` the
number of induction hypotheses, `off = nm + q`. -/
theorem VInductDecl'.minor_tele_offset {nm q nf nr t : Nat} (ht : t < nm) :
    nf + (nm + q) + nr = t + (nr + nf + q + (nm - 1 - t) + 1) := by omega

/-- Offset 4: the minor premise's domain match — the constructor application's type is
exactly what the motive demands after eating the index terms. -/
theorem VInductDecl'.minor_dom_offset {nm q nf nr t ni : Nat} (ht : t < nm) :
    (nr + nf + q + (nm - 1 - t)) + 1 + (ni + t) - ni = nr + nf + (nm + q) := by omega

/-- Offset 1: the telescope `HasArgs.bvars` supplies and the one the motive's type demands
collapse to the same lift. -/
theorem VInductDecl'.rec_tele_offset {nm nmin ni j : Nat} (hj : j < nm) :
    nm + nmin + (1 + ni) = j + (1 + ni + nmin + (nm - 1 - j) + 1) := by omega

/-- Offset 2: after the motive has eaten the index arguments, the parameter block lands
exactly on the major premise's own type. -/
theorem VInductDecl'.rec_dom_offset {nm nmin ni j : Nat} (hj : j < nm) :
    1 + ni + nmin + (nm - 1 - j) + 1 + j = 1 + ni + nmin + nm := by omega

/-- `map_instAll_bvars` with the length supplied as an equation, so callers never need a
`conv` to line the index up. -/
theorem VExpr.map_instAll_bvars' {as : List VExpr} {n : Nat} (h : as.length = n) :
    (bvars 0 n).map (VExpr.instAll · as 0) = as := by
  subst h; exact VExpr.map_instAll_bvars as

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **The motive's index-telescope computation.**  Applying `motive_j`'s stored `I_j p ι`
to index arguments `ιs` shifts the parameter block down by `ni` and returns `ιs`.

`ιs` is arbitrary: D6 instantiates it at `bvars 1 ni` (the index *variables*), D5 at the
constructor's index *terms*. -/
theorem tyApp'_instAll {j ni K M : Nat} {ιs : List VExpr} (hlen : ιs.length = ni)
    (h : K + 1 + (ni + j) - ni = M) :
    VExpr.instAll ((D.tyApp' j (ni + j) (bvars 0 ni)).liftN (K + 1) ni) ιs 0
      = D.tyApp' j M ιs := by
  have hL : (D.tyApp' j (ni + j) (bvars 0 ni)).liftN (K + 1) ni
      = (VExpr.const (D.types.getD j default).name D.selfLvls).mkApp
          (bvars (K + 1 + (ni + j)) D.np ++ bvars 0 ni) := by
    rw [VInductDecl'.tyApp', VExpr.liftN_mkApp, List.map_append,
      VExpr.map_liftN_bvars_lo (Nat.le_add_right ni j),
      VExpr.map_liftN_bvars_hi (Nat.le_of_eq (Nat.zero_add ni))]
    rfl
  rw [hL, VInductDecl'.tyApp', VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    VExpr.map_instAll_bvars_ge (by rw [hlen]; omega), hlen, h,
    VExpr.map_instAll_bvars' hlen]

/-- Applying `motive_j`'s stored `I_j p ι` to `bvars 1 ni` lands on the major premise's own
type: the D6 instance of `tyApp'_instAll`. -/
theorem tyApp'_instAll_bvars {j ni K : Nat} (h : K + 1 + j = 1 + ni + D.nmin + D.nm) :
    VExpr.instAll ((D.tyApp' j (ni + j) (bvars 0 ni)).liftN (K + 1) ni) (bvars 1 ni) 0
      = (D.tyApp' j (ni + D.nmin + D.nm) (bvars 0 ni)).liftN 1 0 := by
  have hR : (D.tyApp' j (ni + D.nmin + D.nm) (bvars 0 ni)).liftN 1 0
      = D.tyApp' j (1 + (ni + D.nmin + D.nm)) (bvars 1 ni) := by
    rw [VInductDecl'.tyApp', VInductDecl'.tyApp', VExpr.liftN_mkApp, List.map_append,
      VExpr.map_liftN_bvars_lo (Nat.zero_le _), VExpr.map_liftN_bvars_lo (Nat.zero_le _)]
    rfl
  rw [hR, tyApp'_instAll (D := D) (M := 1 + (ni + D.nmin + D.nm)) VExpr.length_bvars
    (by omega)]

/-- **The motive application, generically.**  Motive `t`, sitting at offset `K`, applied to
index arguments `ιs` and a major premise `z`.

Stated with `ιs` and `z` arbitrary because it is used twice: `recType`'s body applies the
motive to the index *variables* and the major *variable* (D6), while a minor premise applies
it to the constructor's index *terms* and to a constructor *application* (D5).  Only the two
hypotheses differ. -/
theorem motiveApp_hasType' {T : VIndType} {t K : Nat} {Γ ιs : List VExpr} {z : VExpr}
    (hT : D.types[t]? = some T)
    (hmot : Lookup Γ K ((D.motiveType t).liftN (K + 1)))
    (hidx : env.HasArgs D.recUvars Γ
      (liftTele (K + 1) (liftTele t (D.atRecTele T.indices) 0) 0) ιs)
    (hz : env.HasType D.recUvars Γ z
      (VExpr.instAll ((D.tyApp' t (T.indices.length + t)
        (bvars 0 T.indices.length)).liftN (K + 1) T.indices.length) ιs 0)) :
    env.HasType D.recUvars Γ ((VExpr.bvar K).mkApp (ιs ++ [z])) (.sort D.elimLvl) := by
  have hm0 : env.HasType D.recUvars Γ (.bvar K) ((D.motiveType t).liftN (K + 1)) := .bvar hmot
  have hlenX : (D.atRecTele T.indices).length = T.indices.length :=
    VInductDecl'.length_atRecTele D
  have hmot' : (D.motiveType t).liftN (K + 1)
      = mkPi (liftTele (K + 1) (liftTele t (D.atRecTele T.indices) 0) 0)
          ((VExpr.forallE (D.tyApp' t (T.indices.length + t) (bvars 0 T.indices.length))
              (.sort D.elimLvl)).liftN (K + 1) T.indices.length) := by
    simp only [VInductDecl'.motiveType, getD_types hT]
    rw [VExpr.liftN_mkPi, VExpr.length_liftTele, hlenX, Nat.zero_add]
  rw [hmot'] at hm0
  have happ := VEnv.HasType.mkApp' hidx hm0
  simp only [VExpr.liftN, VExpr.instAll_forallE, VExpr.instAll_sort] at happ
  rw [VExpr.mkApp_concat]
  exact happ.app hz

/-- **D6's body**, the variables-only instance of `motiveApp_hasType'`.  `hidx` is
discharged by `HasArgs.bvars` at the call site. -/
theorem motiveApp_hasType {T : VIndType} {j : Nat} {Γ : List VExpr}
    (hT : D.types[j]? = some T) (hj : j < D.nm)
    (hmot : Lookup Γ (1 + T.indices.length + D.nmin + (D.nm - 1 - j))
      ((D.motiveType j).liftN (1 + T.indices.length + D.nmin + (D.nm - 1 - j) + 1)))
    (hmaj : Lookup Γ 0 ((D.tyApp' j (T.indices.length + D.nmin + D.nm)
      (bvars 0 T.indices.length)).liftN 1))
    (hidx : env.HasArgs D.recUvars Γ
      (liftTele (1 + T.indices.length)
        (liftTele (D.nm + D.nmin) (D.atRecTele T.indices) 0) 0)
      (bvars 1 T.indices.length)) :
    env.HasType D.recUvars Γ
      ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
        (bvars 1 T.indices.length ++ [.bvar 0]))
      (.sort D.elimLvl) := by
  have hcol : liftTele (1 + T.indices.length)
        (liftTele (D.nm + D.nmin) (D.atRecTele T.indices) 0) 0
      = liftTele (1 + T.indices.length + D.nmin + (D.nm - 1 - j) + 1)
          (liftTele j (D.atRecTele T.indices) 0) 0 := by
    rw [VExpr.liftTele_collapse₂, VExpr.liftTele_collapse₂]
    exact congrArg (liftTele · _ _) (VInductDecl'.rec_tele_offset hj)
  rw [hcol] at hidx
  refine motiveApp_hasType' hT hmot hidx ?_
  rw [tyApp'_instAll_bvars (D := D) (j := j) (ni := T.indices.length)
    (K := 1 + T.indices.length + D.nmin + (D.nm - 1 - j)) (VInductDecl'.rec_dom_offset hj)]
  exact .bvar hmaj

/-- **D5's body**, the terms-and-application instance of `motiveApp_hasType'`.

`hidx` comes from `VIndCtor.WF.args_ty` after `atRec` and the two weakenings; `hz` from the
constructor constant applied to the parameters and fields.  Everything offset-related is in
`minor_dom_offset`. -/
theorem minorBody_hasType {T : VIndType} {C : VIndCtor} {t q nr : Nat} {Γ : List VExpr}
    (hT : D.types[t]? = some T) (ht : t < D.nm)
    (hlen : C.args.length = T.indices.length)
    (hmot : Lookup Γ (nr + C.fields.length + q + (D.nm - 1 - t))
      ((D.motiveType t).liftN (nr + C.fields.length + q + (D.nm - 1 - t) + 1)))
    (hidx : env.HasArgs D.recUvars Γ
      (liftTele (nr + C.fields.length + q + (D.nm - 1 - t) + 1)
        (liftTele t (D.atRecTele T.indices) 0) 0)
      (C.args.map fun a => VExpr.shift (D.nm + q) nr C.fields.length (D.atRec a)))
    (hz : env.HasType D.recUvars Γ
      (D.ctorApp' C (nr + C.fields.length + (D.nm + q)) (bvars nr C.fields.length))
      (D.tyApp' t (nr + C.fields.length + (D.nm + q))
        (C.args.map fun a => VExpr.shift (D.nm + q) nr C.fields.length (D.atRec a)))) :
    env.HasType D.recUvars Γ
      ((VExpr.bvar (nr + C.fields.length + q + (D.nm - 1 - t))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) nr C.fields.length (D.atRec a))
          ++ [D.ctorApp' C (nr + C.fields.length + (D.nm + q)) (bvars nr C.fields.length)]))
      (.sort D.elimLvl) := by
  refine motiveApp_hasType' hT hmot hidx ?_
  rw [tyApp'_instAll (D := D) (M := nr + C.fields.length + (D.nm + q))
    (by rw [List.length_map, hlen]) (VInductDecl'.minor_dom_offset ht)]
  exact hz

end VInductDecl'

/-! ## Locating a motive in the context

Both wrappers need `hmot`: the de Bruijn index `nm - 1 - j` into `D.motives.reverse` really
names `motiveType j`.  `D.motives` is `(List.range nm).map motiveType`, so this is a
statement about a reversed mapped range, proved by induction on `n`. -/

theorem List.map_range_reverse_split {α} (f : Nat → α) : ∀ {n j : Nat}, j < n →
    ∃ Ξ rest, ((List.range n).map f).reverse = Ξ ++ f j :: rest ∧ Ξ.length = n - 1 - j
  | n+1, j, hj => by
    rw [List.range_succ, List.map_append, List.reverse_append]
    rcases Nat.lt_or_ge j n with h | h
    · obtain ⟨Ξ, rest, he, hlen⟩ := List.map_range_reverse_split f h
      refine ⟨f n :: Ξ, rest, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append, he]
      · simp only [List.length_cons, hlen]; omega
    · have : j = n := by omega
      subst this
      exact ⟨[], ((List.range j).map f).reverse, by simp, by simp⟩

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **`hmot`.**  Motive `j` sits `Δ.length + (nm - 1 - j)` binders down in any context whose
motive block is `D.motives.reverse`. -/
theorem lookup_motive {j : Nat} (hj : j < D.nm) (Δ Γ₀ : List VExpr) :
    Lookup (Δ ++ D.motives.reverse ++ Γ₀) (Δ.length + (D.nm - 1 - j))
      ((D.motiveType j).liftN (Δ.length + (D.nm - 1 - j) + 1)) := by
  obtain ⟨Ξ, rest, he, hlen⟩ := List.map_range_reverse_split D.motiveType hj
  have hsplit : Δ ++ D.motives.reverse ++ Γ₀
      = (Δ ++ Ξ) ++ D.motiveType j :: (rest ++ Γ₀) := by
    rw [VInductDecl'.motives, he]; simp
  have hΞ : (Δ ++ Ξ).length = Δ.length + (D.nm - 1 - j) := by
    rw [List.length_append, hlen]
  rw [hsplit, ← hΞ]
  exact Lookup.append _

end VInductDecl'

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

@[simp] theorem length_motives : D.motives.length = D.nm := by simp [VInductDecl'.motives]
@[simp] theorem length_minors : D.minors.length = D.nmin := by simp [VInductDecl'.minors]

/-- **D6.**  The recursor's type is well-formed, given that the minor telescope is
(`onCtxMinors`, D5).  Everything else -- the parameters, the motives (D3), the indices
(B6), the major premise (D1) and the codomain (`motiveApp_hasType`) -- is discharged here. -/
theorem recType_isType (hR : D.RecCtx env) {j : Nat} {T : VIndType}
    (hT : D.types[j]? = some T) (hj : j < D.nm)
    (hmin : OnCtx (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars)) :
    env.IsType D.recUvars [] (D.recType j) := by
  have hmem : T ∈ D.types := List.mem_of_getElem? hT
  have hlenEM : (D.minors.reverse ++ D.motives.reverse).length = D.nm + D.nmin := by
    simp; omega
  have W : Ctx.LiftN (D.nm + D.nmin) 0 (D.atRecTele D.params).reverse
      (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse) := by
    exact .zero _ hlenEM
  have hI := VEnv.OnCtx.weakTele hR.ordered W hmin (hR.onCtxIndices hmem)
  have hdom := VInductDecl'.tyApp'_hasType hR hT W hmin
  rw [show T.indices.length + (D.nm + D.nmin)
      = T.indices.length + D.nmin + D.nm from by omega] at hdom
  have hcod : env.HasType D.recUvars
      (D.tyApp' j (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)
        :: ((liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).reverse
            ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      ((VExpr.bvar (1 + T.indices.length + D.nmin + (D.nm - 1 - j))).mkApp
        (bvars 1 T.indices.length ++ [.bvar 0])) (.sort D.elimLvl) := by
    refine VInductDecl'.motiveApp_hasType hT hj ?_ .zero ?_
    · have h := VInductDecl'.lookup_motive (D := D) hj
        (D.tyApp' j (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)
          :: (liftTele (D.nm + D.nmin) (D.atRecTele T.indices)).reverse ++ D.minors.reverse)
        (D.atRecTele D.params).reverse
      simp only [List.length_cons, List.length_append, List.length_reverse,
        VExpr.length_liftTele, VInductDecl'.length_atRecTele,
        VInductDecl'.length_minors] at h
      rw [show T.indices.length + 1 + D.nmin = 1 + T.indices.length + D.nmin from by omega] at h
      simpa using h
    · have h := VEnv.HasArgs.bvars (env := env) (U := D.recUvars)
        (Δ := [D.tyApp' j (T.indices.length + D.nmin + D.nm) (bvars 0 T.indices.length)])
        (As := liftTele (D.nm + D.nmin) (D.atRecTele T.indices))
        (Γ₀ := D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      simp only [List.length_cons, List.length_nil, VExpr.length_liftTele,
        VInductDecl'.length_atRecTele, Nat.zero_add] at h
      simpa using h
  rw [VInductDecl'.recType, getD_types hT]
  refine VEnv.IsType.mkPi ?_ (VEnv.IsType.forallE ?_ ?_)
  · simpa using hI
  · exact ⟨_, by simpa using hdom⟩
  · exact ⟨_, by simpa using hcod⟩

end VInductDecl'

/-- Stage 3: adding the block's recursors preserves `Ordered`, given D5. -/
theorem VInductDecl'.addIndRecs_ordered {env env' : VEnv} {D : VInductDecl'}
    (hR : D.RecCtx env)
    (hmin : OnCtx (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars))
    (he : env.addIndRecs D = some env') : VEnv.Ordered env' := by
  refine VEnv.addConstList_ordered hR.ordered (fun c hc => ?_) he
  simp only [VInductDecl'.recConsts, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : D.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have hj : j < D.nm := by
    rcases Nat.lt_or_ge j D.types.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hT; exact absurd hT (by simp)
  exact VInductDecl'.recType_isType hR hT hj hmin

/-- **`addInduct'` preserves `Ordered`, with D6 discharged.**  The only remaining
obligations are D5 (`hmin`, the minor telescope is a well-formed context) and E5
(`hrules`, each ι-rule is a well-formed `VDefEq`). -/
theorem VInductDecl'.addInduct'_ordered' {env env' : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) (h : D.WF env)
    (hmin : ∀ {env₂ : VEnv}, D.RecCtx env₂ →
      OnCtx (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
        (env₂.IsType D.recUvars))
    (hrules : ∀ {env₁ env₂ env₃ : VEnv}, env.addIndTypes D = some env₁ →
      env₁.addIndCtors D = some env₂ → env₂.addIndRecs D = some env₃ →
      ∀ df ∈ D.iotaRules, df.WF env₃)
    (he : env.addInduct' D = some env') : env'.Ordered := by
  refine VInductDecl'.addInduct'_ordered henv h (fun {env₁ env₂} h1 h2 c hc => ?_) hrules he
  have o1 := VInductDecl'.addIndTypes_ordered henv h h1
  have o2 := VInductDecl'.addIndCtors_ordered o1 h h1 h2
  have hR : D.RecCtx env₂ := h.recCtx h1 h2 VEnv.LE.rfl o2
  simp only [VInductDecl'.recConsts, List.mem_map] at hc
  obtain ⟨⟨T, j⟩, hTj, rfl⟩ := hc
  have hT : D.types[j]? = some T := List.mk_mem_zipIdx_iff_getElem?.1 hTj
  have hj : j < D.nm := by
    rcases Nat.lt_or_ge j D.types.length with hlt | hle
    · exact hlt
    · rw [List.getElem?_eq_none hle] at hT; exact absurd hT (by simp)
  exact VInductDecl'.recType_isType hR hT hj (hmin hR)

/-! ## The constructor interface for `ParamsExtra.ctor_ty`

Everything a consumer destructuring `ci.type = C.type D j` needs, in one place.  `ci.type`
is closed, so its binder telescope and its result indices are too -- which is what makes
`IsDefEqStrong.weak'` provable for a bundle carrying them. -/

theorem VIndCtor.WF.type_closed {env₁ : VEnv} {D : VInductDecl'} {j T C}
    (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    VExpr.ClosedN (C.type D j) 0 :=
  (h.isType henv).choose_spec.closedN henv trivial

/-- The constructor's binder telescope (parameters ++ field types) is closed. -/
theorem VIndCtor.WF.tele_closed {env₁ : VEnv} {D : VInductDecl'} {j T C}
    (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    VExpr.ClosedTele (C.params ++ C.fields.map (·.type)) 0 :=
  (VExpr.closedN_mkPi.1 (h.type_closed henv)).1

/-- Each result index is closed under the constructor's binders. -/
theorem VIndCtor.WF.args_closed {env₁ : VEnv} {D : VInductDecl'} {j T C}
    (henv : VEnv.Ordered env₁) (h : VIndCtor.WF env₁ D j T C) :
    ∀ a ∈ C.args, VExpr.ClosedN a (C.params.length + C.fields.length) := by
  have hb := (VExpr.closedN_mkPi.1 (h.type_closed henv)).2
  simp only [List.length_append, List.length_map, Nat.zero_add] at hb
  rw [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.closedN_mkApp] at hb
  exact fun a ha => hb.2 a (List.mem_append_right _ ha)

/-- The constructor's result head carries the block's **own** universe parameters, i.e. the
identity list.  So `instL ls` on the stored type puts exactly `ls` at the head — which is
what a consumer rebuilding the spine at a different level list needs to know. -/
theorem VIndCtor.canonResult_instL (C : VIndCtor) (D : VInductDecl') (j : Nat)
    {ls : List VLevel} (hls : ls.length = D.uvars) :
    (C.canonResult D j).instL ls
      = (VExpr.const (D.types.getD j default).name ls).mkApp
        (bvars C.fields.length D.np ++ C.args.map (VExpr.instL ls)) := by
  simp only [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.instL_mkApp, List.map_append,
    VExpr.map_instL_bvars, VExpr.instL, VInductDecl'.ownLvls, VLevel.inst_map_id hls]

/-! ## `VIndCtor.Interface`: everything `ParamsExtra.ctor_ty` should conclude

`ctor_ty` itself lives in `Experimental/SExpr.lean`.  This bundles what it needs from this
side so that widening it is a matter of concluding one structure rather than adding a clause
per case -- which is the pattern that has already cost two round-trips (`hu0`, then
`args_len` + closedness). -/

structure VIndCtor.Interface (env : VEnv) (D : VInductDecl') (j : Nat) (T : VIndType)
    (C : VIndCtor) : Prop where
  /-- The stored constant, on the nose -- not up to defeq. -/
  const : env.constants C.name = some ⟨D.uvars, C.type D j⟩
  /-- The binder count of the stored type; exact, since the result is an application. -/
  arity : (C.type D j).piArity = C.params.length + C.fields.length
  /-- Needed if the classification splits parameters from fields (`.etaCtor p a`). -/
  params_len : C.params.length = D.np
  /-- The head-arity of the result, stated constructor-*independently*. -/
  head_arity : (C.canonResult D j).appArity = D.np + T.indices.length
  /-- The clause the shape-model stream asked for. -/
  args_len : C.args.length = T.indices.length
  /-- The result sort, in the context the stored type actually binds (`C.params`, not
  `D.params` -- see `VIndCtor.WF.result'`). -/
  result : env.HasType D.uvars ((C.fields.map (·.type)).reverse ++ C.params.reverse)
    (C.canonResult D j) (.sort D.lvl)
  /-- Closedness.  `CtorBundle` carries the telescope and the indices *separately*, so the
  split form is what it needs; the indices are closed at `np + nf`, not at `0`. -/
  type_closed : VExpr.ClosedN (C.type D j) 0
  tele_closed : VExpr.ClosedTele (C.params ++ C.fields.map (·.type)) 0
  args_closed : ∀ a ∈ C.args, VExpr.ClosedN a (C.params.length + C.fields.length)

theorem VIndCtor.WF.interface {env : VEnv} {D : VInductDecl'} {j T C}
    (henv : VEnv.Ordered env) (h : VIndCtor.WF env D j T C)
    (hconst : env.constants C.name = some ⟨D.uvars, C.type D j⟩) :
    VIndCtor.Interface env D j T C where
  const := hconst
  arity := VIndCtor.type_piArity ..
  params_len := h.params_len
  head_arity := h.canonResult_appArity
  args_len := h.args_len
  result := h.result' henv
  type_closed := h.type_closed henv
  tele_closed := h.tele_closed henv
  args_closed := h.args_closed henv

/-- The interface, for every constructor of a block just added by `addInduct'`. -/
theorem VInductDecl'.addInduct'_ctor_interface {env env' : VEnv} {D : VInductDecl'}
    (henv' : VEnv.Ordered env') (hR : D.RecCtx env')
    (he : env.addInduct' D = some env') {j : Nat} {C : VIndCtor}
    (hC : (j, C) ∈ D.ctorsAll) :
    ∃ T, D.types[j]? = some T ∧ C ∈ T.ctors ∧ VIndCtor.Interface env' D j T C := by
  obtain ⟨T, hT, hmem⟩ := VInductDecl'.mem_ctorsAll hC
  exact ⟨T, hT, hmem, (hR.ctors j T hT C hmem).interface henv' (VEnv.addInduct'_ctors he hC)⟩

/-! ## D4: the induction-hypothesis telescope -/

/-- A declaration-order telescope is a well-formed context as soon as each entry is a type
in the context of its own prefix.  Induction is from the *right*, since the last entry of
the telescope is the innermost of the context. -/
theorem VEnv.OnCtx.ofTele {env : VEnv} {U : Nat} : ∀ {As Γ : List VExpr},
    OnCtx Γ (env.IsType U) →
    (∀ s A, As[s]? = some A → env.IsType U ((As.take s).reverse ++ Γ) A) →
    OnCtx (As.reverse ++ Γ) (env.IsType U)
  | [], Γ, hΓ, _ => by simpa using hΓ
  | A :: As, Γ, hΓ, h => by
    have hA : env.IsType U Γ A := by simpa using h 0 A rfl
    rw [VExpr.tele_ctx_cons]
    refine VEnv.OnCtx.ofTele ⟨hΓ, hA⟩ fun s B hB => ?_
    have hs := h (s + 1) B (by simpa using hB)
    rwa [List.take_succ_cons, VExpr.tele_ctx_cons] at hs

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **D4's body.**  The `s`-th induction hypothesis of minor `q`: `motive_{r.idx}` applied
to the recursive field's index terms `π` and to `fieldᵢ` applied to its own `ξ` variables.

The offsets are `ih_param_offset`'s: `args_ty` places the parameters at `nxi + i`, the two
weakenings add `off = nm + q` and `d = nf - i + s`, and the motive index puts them at
`nxi + s + nf + q + nm`.  Those agree, which is what makes `hz`'s type the one the motive
demands. -/
theorem ihBody_hasType {T' : VIndType} {r : VIndRecArg} {i s nxi nf q off d : Nat}
    {Γ ιs : List VExpr} {z : VExpr}
    (hT' : D.types[r.idx]? = some T') (hridx : r.idx < D.nm)
    (hlen : ιs.length = T'.indices.length)
    (hoff : off = D.nm + q) (hd : d = nf - i + s) (hi : i ≤ nf)
    (hmot : Lookup Γ (nxi + s + nf + q + (D.nm - 1 - r.idx))
      ((D.motiveType r.idx).liftN (nxi + s + nf + q + (D.nm - 1 - r.idx) + 1)))
    (hidx : env.HasArgs D.recUvars Γ
      (liftTele (nxi + s + nf + q + (D.nm - 1 - r.idx) + 1)
        (liftTele r.idx (D.atRecTele T'.indices) 0) 0) ιs)
    (hz : env.HasType D.recUvars Γ z (D.tyApp' r.idx (nxi + i + off + d) ιs)) :
    env.HasType D.recUvars Γ
      ((VExpr.bvar (nxi + s + nf + q + (D.nm - 1 - r.idx))).mkApp (ιs ++ [z]))
      (.sort D.elimLvl) := by
  refine motiveApp_hasType' hT' hmot hidx ?_
  rw [tyApp'_instAll (D := D) (M := nxi + i + off + d) hlen (by omega)]
  exact hz

end VInductDecl'

/-! ### `ihTypes` is a `zipIdx.map`: reading off entries and prefixes

`getElem?_zipIdx` is upstream and `@[simp]`; only `take_zipIdx` is missing.  With `ihType`
factored out (`Decl.lean`), both statements are readable. -/

theorem List.take_zipIdx {α : Type _} : ∀ {l : List α} {j s},
    (l.zipIdx j).take s = (l.take s).zipIdx j
  | [], _, _ => by simp
  | _ :: _, _, 0 => by simp
  | _ :: _, _, _+1 => by
    rw [List.zipIdx_cons, List.take_succ_cons, List.take_succ_cons, List.zipIdx_cons,
      take_zipIdx]

theorem VInductDecl'.ihTypes_getElem? (D : VInductDecl') (q s : Nat) (C : VIndCtor) :
    (D.ihTypes q C)[s]? = (C.recFields[s]?).map fun ir => D.ihType q C ir.1 ir.2 s := by
  simp only [VInductDecl'.ihTypes, List.getElem?_map, List.getElem?_zipIdx, Option.map_map,
    Nat.zero_add]
  rfl

theorem VInductDecl'.ihTypes_take (D : VInductDecl') (q s : Nat) (C : VIndCtor) :
    (D.ihTypes q C).take s
      = (C.recFields.take s).zipIdx.map fun ir => D.ihType q C ir.1.1 ir.1.2 ir.2 := by
  rw [VInductDecl'.ihTypes, ← List.map_take, List.take_zipIdx]

@[simp] theorem VInductDecl'.length_ihTypes (D : VInductDecl') (q : Nat) (C : VIndCtor) :
    (D.ihTypes q C).length = C.recFields.length := by simp [VInductDecl'.ihTypes]

/-! ### D4: the `ξ`-telescope and the per-entry `IsType` -/

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **The two weakenings compose into `shift`.**  A recursive field's `ξ`-telescope, carried
from the field's own context into minor `q`'s `s`-th ih context: `Ctx.LiftN off i` inserts
the motives and minors between the fields and the parameters, `Ctx.LiftN d 0` inserts the
later fields and the earlier ihs, and `liftTele_liftTele_eq_shiftTele` collapses the pair to
the `shiftTele off d i` that `ihType` uses. -/
theorem onCtxXi (henv : VEnv.Ordered env) {off d i : Nat} {Γ₁ Γ₂ Γ₃ X : List VExpr}
    (W₁ : Ctx.LiftN off i Γ₁ Γ₂) (W₂ : Ctx.LiftN d 0 Γ₂ Γ₃)
    (hΓ₂ : OnCtx Γ₂ (env.IsType D.recUvars)) (hΓ₃ : OnCtx Γ₃ (env.IsType D.recUvars))
    (hX : OnCtx (X.reverse ++ Γ₁) (env.IsType D.recUvars)) :
    OnCtx ((shiftTele off d i X 0).reverse ++ Γ₃) (env.IsType D.recUvars) := by
  have h1 := VEnv.OnCtx.weakTele henv W₁ hΓ₂ hX
  have h2 := VEnv.OnCtx.weakTele henv W₂ hΓ₃ h1
  have he := VExpr.liftTele_liftTele_eq_shiftTele (d := d) (off := off) (As := X) (i := i)
    (j := 0)
  rw [Nat.add_zero] at he
  rwa [he] at h2

/-- **D4, per entry.**  The `s`-th induction hypothesis of minor `q` is a type.

`hξ` is `onCtxXi`; the remaining three are the same hypotheses `ihBody_hasType` takes, and
are discharged against the concrete context by `HasArgs.weakN` (for `hidx`, from
`VIndField.WF.pos`'s `args_ty`), `lookup_motive` (for `hmot`) and `appBVars` after
`IsDefEqType.defeq` (for `hz`). -/
theorem ihType_isType {T' : VIndType} {r : VIndRecArg} {C : VIndCtor}
    {q i s nxi nf off d : Nat} {Γ ιs : List VExpr} {z : VExpr}
    (hT' : D.types[r.idx]? = some T') (hridx : r.idx < D.nm)
    (hlen : ιs.length = T'.indices.length)
    (hoff : off = D.nm + q) (hd : d = nf - i + s) (hi : i ≤ nf)
    (hnf : nf = C.fields.length) (hnxi : nxi = r.binders.length)
    (hιs : ιs = r.args.map fun a => VExpr.shift off d i (D.atRec a) nxi)
    (hz' : z = (VExpr.bvar (nxi + s + (nf - 1 - i))).mkApp (bvars 0 nxi))
    (hξ : OnCtx ((shiftTele off d i (D.atRecTele r.binders) 0).reverse ++ Γ)
      (env.IsType D.recUvars))
    (hmot : Lookup ((shiftTele off d i (D.atRecTele r.binders) 0).reverse ++ Γ)
      (nxi + s + nf + q + (D.nm - 1 - r.idx))
      ((D.motiveType r.idx).liftN (nxi + s + nf + q + (D.nm - 1 - r.idx) + 1)))
    (hidx : env.HasArgs D.recUvars
      ((shiftTele off d i (D.atRecTele r.binders) 0).reverse ++ Γ)
      (liftTele (nxi + s + nf + q + (D.nm - 1 - r.idx) + 1)
        (liftTele r.idx (D.atRecTele T'.indices) 0) 0) ιs)
    (hz : env.HasType D.recUvars
      ((shiftTele off d i (D.atRecTele r.binders) 0).reverse ++ Γ) z
      (D.tyApp' r.idx (nxi + i + off + d) ιs)) :
    env.IsType D.recUvars Γ (D.ihType q C i r s) := by
  subst hnf hnxi hoff hd hιs hz'
  exact VEnv.IsType.mkPi hξ ⟨_, ihBody_hasType hT' hridx hlen rfl rfl hi hmot hidx hz⟩

end VInductDecl'

/-! ### Splitting the field telescope at `i`

D4's `W₂` needs the minor's field context decomposed as "the fields after `i`, over the
context of the fields before `i`".  That is `liftTele_append` plus the `take`/`drop` split,
and it is where the `++` associativity has to be paid. -/

theorem VExpr.liftTele_split {n i : Nat} {A B : List VExpr} (h : A.length = i) :
    liftTele n (A ++ B) 0 = liftTele n A 0 ++ liftTele n B i := by
  rw [VExpr.liftTele_append, h, Nat.zero_add]

theorem VInductDecl'.atRecTele_take_drop (D : VInductDecl') (i : Nat) (Φ : List VExpr) :
    D.atRecTele Φ = D.atRecTele (Φ.take i) ++ D.atRecTele (Φ.drop i) := by
  rw [← VInductDecl'.atRecTele_append, List.take_append_drop]

/-- The minor's field context, split at field `i`.  `Γi'` (the right-hand nesting) is the
context of the fields *before* `i`, which is where a recursive field's `ξ`-telescope and its
`args_ty` live. -/
theorem VInductDecl'.fieldCtx_split (D : VInductDecl') {off i : Nat} {Φ Γq : List VExpr}
    (h : (Φ.take i).length = i) :
    (liftTele off (D.atRecTele Φ) 0).reverse ++ Γq
      = (liftTele off (D.atRecTele (Φ.drop i)) i).reverse
        ++ ((liftTele off (D.atRecTele (Φ.take i)) 0).reverse ++ Γq) := by
  rw [D.atRecTele_take_drop i Φ, VExpr.liftTele_append, VInductDecl'.length_atRecTele, h,
    Nat.zero_add, List.reverse_append, List.append_assoc]

/-- The `Ctx.LiftN` D4 needs for its outer weakening: the `s` earlier induction hypotheses
and the `nf - i` later fields, inserted below the context of the fields before `i`. -/
theorem VInductDecl'.liftN_ihCtx (D : VInductDecl') {off i s d : Nat} {Φ Γq V : List VExpr}
    (h : (Φ.take i).length = i) (hd : (V.take s).length + (Φ.drop i).length = d) :
    Ctx.LiftN d 0 ((liftTele off (D.atRecTele (Φ.take i)) 0).reverse ++ Γq)
      ((V.take s).reverse ++ ((liftTele off (D.atRecTele Φ) 0).reverse ++ Γq)) := by
  rw [D.fieldCtx_split h, ← List.append_assoc]
  refine .zero _ ?_
  rw [List.length_append, List.length_reverse, List.length_reverse,
    VExpr.length_liftTele, VInductDecl'.length_atRecTele]
  exact hd

/-- **D4's `hidx`.**  `VIndField.WF.pos`'s `args_ty`, carried from the recursive field's own
context into minor `q`'s `s`-th ih context by `atRec` and the two weakenings, lands on
exactly the telescope the motive's type demands.

`harith` is `ih_param_offset`: the parameters reach the same offset by either route. -/
theorem VInductDecl'.ihArgs_hasArgs {env : VEnv} {D : VInductDecl'} {T' : VIndType}
    {i nxi p off d u L : Nat} {ξ ras Γfield Γa Γξs : List VExpr}
    (henv : VEnv.Ordered env) (hp : p = nxi + i)
    (hargs : env.HasArgs D.uvars (ξ.reverse ++ Γfield)
      (liftTele p T'.indices) ras)
    (W₁ : Ctx.LiftN off p ((D.atRecTele ξ).reverse ++ D.atRecCtx Γfield) Γa)
    (W₂ : Ctx.LiftN d nxi Γa Γξs)
    (hle : nxi ≤ nxi + i + off) (harith : nxi + i + off + d = u + L) :
    env.HasArgs D.recUvars Γξs
      (liftTele L (liftTele u (D.atRecTele T'.indices) 0) 0)
      (ras.map fun a => VExpr.shift off d i (D.atRec a) nxi) := by
  subst hp
  have h0 := D.atRec_hasArgs hargs
  rw [VInductDecl'.atRecCtx, List.map_append, List.map_reverse] at h0
  rw [show D.atRecTele (liftTele (nxi + i) T'.indices)
      = liftTele (nxi + i) (D.atRecTele T'.indices) 0 from VInductDecl'.atRec_liftTele D] at h0
  have h1 := VEnv.HasArgs.weakN henv W₁ h0
  have h2 := VEnv.HasArgs.weakN henv W₂ h1
  rw [VInductDecl'.ih_telescope_eq hle harith] at h2
  have hmap : List.map (fun x => VExpr.liftN d x nxi)
        (List.map (fun x => VExpr.liftN off x (nxi + i)) (List.map D.atRec ras))
      = ras.map fun a => VExpr.shift off d i (D.atRec a) nxi := by
    simp only [List.map_map, Function.comp_def, VExpr.shift, Nat.add_comm i nxi]
  rwa [hmap] at h2

/-! ## D5: the minor premises

The last obligation of `addInduct'_ordered'` apart from E5.  The route is the one D6 used
for the motives, one level deeper: the minor telescope is assembled by `ofTakes`, each
minor's type by `IsType.mkPi` over its field block and its induction-hypothesis block, and
its body by `minorBody_hasType`. -/

/-- `OnCtx.ofTele` with the prefix's own well-formedness handed to the per-entry
obligation.  Both of D5's telescopes need that: a minor premise is typed in the context of
the earlier minors, an induction hypothesis in the context of the earlier ones. -/
theorem VEnv.OnCtx.ofTakes {env : VEnv} {U : Nat} {As Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (h : ∀ s A, As[s]? = some A → OnCtx ((As.take s).reverse ++ Γ) (env.IsType U) →
      env.IsType U ((As.take s).reverse ++ Γ) A) :
    ∀ n, OnCtx ((As.take n).reverse ++ Γ) (env.IsType U)
  | 0 => by simpa using hΓ
  | n+1 => by
    have ih := VEnv.OnCtx.ofTakes hΓ h n
    cases hA : As[n]? with
    | none => rw [List.take_add_one, hA]; simpa using ih
    | some A =>
      have he : (As.take (n+1)).reverse ++ Γ = A :: ((As.take n).reverse ++ Γ) := by
        rw [List.take_add_one, hA]; simp
      rw [he]
      exact ⟨ih, h n A hA ih⟩

theorem VEnv.OnCtx.ofTele₂ {env : VEnv} {U : Nat} {As Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (h : ∀ s A, As[s]? = some A → OnCtx ((As.take s).reverse ++ Γ) (env.IsType U) →
      env.IsType U ((As.take s).reverse ++ Γ) A) :
    OnCtx (As.reverse ++ Γ) (env.IsType U) := by
  simpa using VEnv.OnCtx.ofTakes hΓ h As.length

namespace VEnv

/-- A defeq of contexts extends under a common prefix.  This is `VIndCtor.WF.defeqCtx`'s
induction, stated once. -/
theorem IsDefEqCtx.append {env : VEnv} {U : Nat} {Γ₁ Γ₂ : List VExpr}
    (h : VEnv.IsDefEqCtx env U [] Γ₁ Γ₂) :
    ∀ {Δ : List VExpr}, OnCtx (Δ ++ Γ₁) (env.IsType U) →
      VEnv.IsDefEqCtx env U [] (Δ ++ Γ₁) (Δ ++ Γ₂)
  | [], _ => h
  | _ :: _, hΔ => .succ (IsDefEqCtx.append h hΔ.1) hΔ.2.choose_spec

/-- Level re-indexing of a context defeq. -/
theorem IsDefEqCtx.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {Γ₀ Γ₁ Γ₂ : List VExpr}, VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂ →
      VEnv.IsDefEqCtx env U' (Γ₀.map (VExpr.instL ls)) (Γ₁.map (VExpr.instL ls))
        (Γ₂.map (VExpr.instL ls))
  | _, _, _, .zero => .zero
  | _, _, _, .succ h hA => .succ (IsDefEqCtx.instL hls h) (hA.instL hls)

end VEnv

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **`tyApp` under `atRec` and a `shift`.**  A saturated block-type application, moved from
the context it was recorded in into a recursor-side context, is the same application at the
recursor's universe numbering with the parameter block relocated.

Both places D5 needs this are instances: the minor premise's major argument
(`i := nf`, `j := 0`) and a recursive field's result inside an induction hypothesis
(`i` the field's index, `j := |ξ|`). -/
theorem shift_atRec_tyApp (D : VInductDecl') {t k i off d K j : Nat} {args : List VExpr}
    (hij : i + j ≤ k) (hK : d + (off + k) = K) :
    VExpr.shift off d i (D.atRec (D.tyApp t k args)) j
      = D.tyApp' t K (args.map fun a => VExpr.shift off d i (D.atRec a) j) := by
  have h1 : D.atRec (D.tyApp t k args)
      = (VExpr.const (D.types.getD t default).name D.selfLvls).mkApp
        (bvars k D.np ++ args.map D.atRec) := by
    simp only [VInductDecl'.tyApp, VInductDecl'.atRec_mkApp, List.map_append,
      VInductDecl'.atRec_bvars, VInductDecl'.atRec_const,
      VInductDecl'.ownLvls_inst_selfLvls]
  rw [h1, VExpr.mkApp_append, VExpr.shift_mkApp, VExpr.shift_mkApp_bvars hij, hK,
    VInductDecl'.tyApp', VExpr.mkApp_append, List.map_map]
  rfl

/-- **D5's major premise.**  The constructor `C` at the recursor's universe numbering,
applied to the parameter variables and to its own field variables, has the canonical result
type.  The content beyond `appBVars₂` is the F3 transport: the *stored* type binds
`C.params`, while the ambient context carries `D.params`, so the application is built over
`C.params` and moved across by `defeqDFC`. -/
theorem ctorApp'_hasType (hR : D.RecCtx env) {t : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[t]? = some T) (hC : C ∈ T.ctors) (hCall : (t, C) ∈ D.ctorsAll)
    {m : Nat} {Δ : List VExpr} (hΔ : Δ.length = m)
    (hΓ : OnCtx (Δ ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars)) :
    env.HasType D.recUvars
      ((liftTele m (D.atRecTele (C.fields.map (·.type)))).reverse
        ++ (Δ ++ (D.atRecTele D.params).reverse))
      (D.ctorApp' C (C.fields.length + m) (bvars 0 C.fields.length))
      ((D.atRec (C.canonResult D t)).liftN m C.fields.length) := by
  have henv := hR.ordered
  have hCwf : VIndCtor.WF env D t T C := hR.ctors t T hT C hC
  -- the F3 context defeq, at the recursor's universe numbering
  have hpar : VEnv.IsDefEqCtx env D.recUvars [] (D.atRecTele D.params).reverse
      (D.atRecTele C.params).reverse := by
    have := VEnv.IsDefEqCtx.instL (ls := D.selfLvls) D.selfLvls_wf (hCwf.params_eq.symm henv)
    simpa [VInductDecl'.atRecTele] using this
  -- the field block, over each of the two parameter blocks
  have hBsD : OnCtx ((D.atRecTele (C.fields.map (·.type))).reverse
      ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars) := by
    have := D.atRec_onCtx (hCwf.onCtxAllFields henv)
    rwa [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse] at this
  have hAs0 : OnCtx (D.atRecTele C.params).reverse (env.IsType D.recUvars) := by
    have := D.atRec_onCtx hCwf.params_eq.isType
    rwa [VInductDecl'.atRecCtx, List.map_reverse] at this
  have hBs0 : OnCtx ((D.atRecTele (C.fields.map (·.type))).reverse
      ++ (D.atRecTele C.params).reverse) (env.IsType D.recUvars) := by
    have W := hCwf.defeqCtx henv (Δ := (C.fields.map (·.type)).reverse)
      (hCwf.onCtxAllFields henv)
    have := D.atRec_onCtx ((W.symm henv).isType)
    rwa [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse] at this
  -- the whole context, over each of the two parameter blocks
  have WD : Ctx.LiftN m 0 (D.atRecTele D.params).reverse (Δ ++ (D.atRecTele D.params).reverse) :=
    .zero Δ hΔ
  have hbigD : OnCtx ((liftTele m (D.atRecTele (C.fields.map (·.type)))).reverse
      ++ (Δ ++ (D.atRecTele D.params).reverse)) (env.IsType D.recUvars) :=
    VEnv.OnCtx.weakTele henv WD hΓ hBsD
  have hbigDC := hpar.append
      (Δ := (liftTele m (D.atRecTele (C.fields.map (·.type)))).reverse ++ Δ)
      (by rw [List.append_assoc]; exact hbigD)
  simp only [List.append_assoc] at hbigDC
  have hΓC : OnCtx (Δ ++ (D.atRecTele C.params).reverse) (env.IsType D.recUvars) :=
    ((hpar.append hΓ).symm henv).isType
  -- the constant, at the recursor's numbering
  have hf : env.HasType D.recUvars ([] : List VExpr) (.const C.name D.selfLvls)
      (mkPi (D.atRecTele C.params ++ D.atRecTele (C.fields.map (·.type)))
        (D.atRec (C.canonResult D t))) := by
    have h1 : env.HasType D.recUvars ([] : List VExpr) (.const C.name D.selfLvls)
        (D.atRec (C.type D t)) :=
      VEnv.HasType.const (hR.ctorConsts t C hCall) D.selfLvls_wf (by simp)
    rwa [VIndCtor.type, VInductDecl'.atRec_mkPi, VInductDecl'.atRecTele_append] at h1
  have WC : Ctx.LiftN m 0 ((D.atRecTele C.params).reverse ++ [])
      (Δ ++ (D.atRecTele C.params).reverse) := by simpa using Ctx.LiftN.zero Δ hΔ
  have happ := VEnv.HasType.appBVars₂ (As := D.atRecTele C.params)
    (Bs := D.atRecTele (C.fields.map (·.type))) (Γ₀ := []) (m := m)
    (f := .const C.name D.selfLvls) henv trivial
    (by simpa using hf) (by simpa using hAs0) (by simpa using hBs0) WC hΓC
  simp only [VInductDecl'.length_atRecTele, List.length_map, hCwf.params_len] at happ
  exact VEnv.HasType.defeqDFC henv (hbigDC.symm henv) happ

end VInductDecl'

/-- Reading a recursive-field entry back: `recFields` is a `filterMap` over `zipIdx`, so an
entry `(i, r)` really is field `i` with `recArg = some r`. -/
theorem VIndCtor.mem_recFields {C : VIndCtor} {i : Nat} {r : VIndRecArg}
    (h : (i, r) ∈ C.recFields) : ∃ F, C.fields[i]? = some F ∧ F.recArg = some r := by
  simp only [VIndCtor.recFields, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨F, i'⟩, hF, r', hr, rfl, rfl⟩ := h
  exact ⟨F, List.mk_mem_zipIdx_iff_getElem?.1 hF, hr⟩

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **Where field `i` sits, seen from inside the `s`-th induction hypothesis.**  The minor's
field block is split at `i+1`, which puts field `i` at the bottom of the part above it. -/
theorem lookup_field (D : VInductDecl') {off i s nf : Nat} {Φ Γq V : List VExpr} {A : VExpr}
    (hi : i < nf) (hnf : Φ.length = nf) (hA : Φ[i]? = some A) (hs : (V.take s).length = s) :
    Lookup ((V.take s).reverse ++ ((liftTele off (D.atRecTele Φ) 0).reverse ++ Γq))
      (s + (nf - 1 - i)) (((D.atRec A).liftN off i).liftN (s + (nf - 1 - i) + 1)) := by
  have htake : (Φ.take i).length = i := by rw [List.length_take]; omega
  have hpre : (liftTele off (D.atRecTele (Φ.take (i+1))) 0).reverse
      = (D.atRec A).liftN off i :: (liftTele off (D.atRecTele (Φ.take i)) 0).reverse := by
    rw [List.take_add_one, hA]
    simp only [Option.toList_some, VInductDecl'.atRecTele_append]
    rw [VExpr.liftTele_split (i := i)
      (by rw [VInductDecl'.length_atRecTele]; exact htake)]
    simp [VInductDecl'.atRecTele, VInductDecl'.atRec]
  have hsplit1 := D.fieldCtx_split (off := off) (i := i+1) (Φ := Φ) (Γq := Γq)
    (by rw [List.length_take]; omega)
  rw [hsplit1, hpre]
  have hΞ : ((V.take s).reverse
      ++ (liftTele off (D.atRecTele (Φ.drop (i+1))) (i+1)).reverse).length
      = s + (nf - 1 - i) := by
    rw [List.length_append, List.length_reverse, List.length_reverse, VExpr.length_liftTele,
      VInductDecl'.length_atRecTele, List.length_drop, hs, hnf]
    omega
  rw [← List.append_assoc, ← hΞ]
  exact Lookup.append _

end VInductDecl'

theorem VEnv.IsDefEqType.weakN {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr} {A B : VExpr}
    (henv : VEnv.Ordered env) (W : Ctx.LiftN n k Γ Γ')
    (h : env.IsDefEqType U Γ A B) : env.IsDefEqType U Γ' (A.liftN n k) (B.liftN n k) :=
  ⟨_, h.choose_spec.weakN henv W⟩

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **What a recursive field provides.**  Shared by D4 and by the ι-rule's
induction-hypothesis *values*, which need the same three facts about field `i` of minor `q`
at ih-depth `s`: its `ξ`-telescope is a well-formed context, its index arguments instantiate
the index telescope of `I_{r.idx}`, and the field applied to its own `ξ` variables inhabits
`I_{r.idx} p π`.

D4 uses it at minor `q`'s own offsets; the ι-rule at `q := nmin`, `s := 0`, where the ih
block above the fields is empty.  The index telescope's split and the result offset are left
universally quantified, because the two callers split them differently: D4 against the
motive's stored telescope (`u := r.idx`), the ι-rule against the recursor's (`u := 0`). -/
theorem recField_facts (hR : D.RecCtx env) {t q s i : Nat} {T : VIndType} {C : VIndCtor}
    {r : VIndRecArg} {F : VIndField}
    (hT : D.types[t]? = some T) (hC : C ∈ T.ctors)
    (hF : C.fields[i]? = some F) (hrec : F.recArg = some r)
    {M : List VExpr} (hMlen : M.length = q)
    (hM : OnCtx (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars))
    (hsV : ((D.ihTypes q C).take s).length = s)
    (hΓ₃ : OnCtx (((D.ihTypes q C).take s).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      (env.IsType D.recUvars)) :
    i < C.fields.length ∧ r.idx < D.nm
    ∧ r.args.length = (D.types.getD r.idx default).indices.length
    ∧ OnCtx ((shiftTele (D.nm + q) (C.fields.length - i + s) i (D.atRecTele r.binders) 0).reverse
            ++ (((D.ihTypes q C).take s).reverse
              ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
                ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))) (env.IsType D.recUvars)
    ∧ (∀ (T'' : VIndType), D.types[r.idx]? = some T'' → ∀ u L : Nat,
        r.binders.length + i + (D.nm + q) + (C.fields.length - i + s) = u + L →
        env.HasArgs D.recUvars ((shiftTele (D.nm + q) (C.fields.length - i + s) i (D.atRecTele r.binders) 0).reverse
            ++ (((D.ihTypes q C).take s).reverse
              ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
                ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))))
          (liftTele L (liftTele u (D.atRecTele T''.indices) 0) 0)
          (r.args.map fun a => VExpr.shift (D.nm + q) (C.fields.length - i + s) i
            (D.atRec a) r.binders.length))
    ∧ (∀ K : Nat, r.binders.length + i + (D.nm + q) + (C.fields.length - i + s) = K →
        env.HasType D.recUvars ((shiftTele (D.nm + q) (C.fields.length - i + s) i (D.atRecTele r.binders) 0).reverse
            ++ (((D.ihTypes q C).take s).reverse
              ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
                ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))))
          ((VExpr.bvar (r.binders.length + s + (C.fields.length - 1 - i))).mkApp
            (bvars 0 r.binders.length))
          (D.tyApp' r.idx K (r.args.map fun a => VExpr.shift (D.nm + q) (C.fields.length - i + s) i
            (D.atRec a) r.binders.length))) := by
  have henv := hR.ordered
  have hCwf : VIndCtor.WF env D t T C := hR.ctors t T hT C hC
  have hi : i < C.fields.length := by
    rcases Nat.lt_or_ge i C.fields.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hF; exact absurd hF (by simp)
  have hmt : (C.fields.take i).map (·.type) = (C.fields.map (·.type)).take i := List.map_take ..
  have hFwf := hCwf.fields i F hF
  rw [hmt] at hFwf
  have hpos := hFwf.pos
  rw [hrec] at hpos
  obtain ⟨hridx, hargl, -, -, hXi, -, hargs, hFdefeq⟩ := hpos
  obtain ⟨T', hT'⟩ : ∃ T', D.types[r.idx]? = some T' := ⟨_, List.getElem?_eq_getElem hridx⟩
  have hΦi : (C.fields.map (·.type))[i]? = some F.type := by rw [List.getElem?_map, hF]; rfl
  have htakei : ((C.fields.map (·.type)).take i).length = i := by
    rw [List.length_take, List.length_map]; omega
  -- the parameter block, and the whole context below the fields
  have WD : Ctx.LiftN (D.nm + q) 0 (D.atRecTele D.params).reverse
      (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse) :=
    .zero (M ++ D.motives.reverse)
      (by rw [List.length_append, List.length_reverse, VInductDecl'.length_motives, hMlen]; omega)
  have hac : D.atRecCtx (((C.fields.map (·.type)).take i).reverse ++ D.params.reverse)
      = (D.atRecTele ((C.fields.map (·.type)).take i)).reverse
        ++ (D.atRecTele D.params).reverse := by
    rw [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse]; rfl
  have hΓ₁ : OnCtx ((D.atRecTele ((C.fields.map (·.type)).take i)).reverse
      ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars) := by
    rw [← hac]
    exact D.atRec_onCtx (by rw [← hmt]; exact hCwf.onCtxFields henv i)
  have W₁ : Ctx.LiftN (D.nm + q) i
      ((D.atRecTele ((C.fields.map (·.type)).take i)).reverse
        ++ (D.atRecTele D.params).reverse)
      ((liftTele (D.nm + q) (D.atRecTele ((C.fields.map (·.type)).take i)) 0).reverse
        ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)) := by
    have h := Ctx.LiftN.tele (As := D.atRecTele ((C.fields.map (·.type)).take i)) WD
    rwa [show (0:Nat) + (D.atRecTele ((C.fields.map (·.type)).take i)).length = i from by
      rw [Nat.zero_add, VInductDecl'.length_atRecTele]; exact htakei] at h
  have W₂ : Ctx.LiftN (C.fields.length - i + s) 0
      ((liftTele (D.nm + q) (D.atRecTele ((C.fields.map (·.type)).take i)) 0).reverse
        ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (((D.ihTypes q C).take s).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))) :=
    D.liftN_ihCtx htakei
      (by rw [hsV, List.length_drop, List.length_map]; omega)
  have hΓ₂ : OnCtx ((liftTele (D.nm + q) (D.atRecTele ((C.fields.map (·.type)).take i)) 0).reverse
      ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (env.IsType D.recUvars) := VEnv.OnCtx.weakTele henv WD hM hΓ₁
  have hX : OnCtx ((D.atRecTele r.binders).reverse
      ++ ((D.atRecTele ((C.fields.map (·.type)).take i)).reverse
        ++ (D.atRecTele D.params).reverse)) (env.IsType D.recUvars) := by
    rw [← hac]
    have h0 := D.atRec_onCtx hXi
    rwa [VInductDecl'.atRecCtx, List.map_append, List.map_reverse] at h0
  have hξ := VInductDecl'.onCtxXi (D := D) henv W₁ W₂ hΓ₂ hΓ₃ hX
  have W₁' : Ctx.LiftN (D.nm + q) (r.binders.length + i)
      ((D.atRecTele r.binders).reverse
        ++ D.atRecCtx (((C.fields.map (·.type)).take i).reverse ++ D.params.reverse))
      ((liftTele (D.nm + q) (D.atRecTele r.binders) i).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele ((C.fields.map (·.type)).take i)) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))) := by
    rw [hac]
    have h := Ctx.LiftN.tele (As := D.atRecTele r.binders) W₁
    rwa [show i + (D.atRecTele r.binders).length = r.binders.length + i from by
      rw [VInductDecl'.length_atRecTele]; omega] at h
  have W₂' : Ctx.LiftN (C.fields.length - i + s) r.binders.length
      ((liftTele (D.nm + q) (D.atRecTele r.binders) i).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele ((C.fields.map (·.type)).take i)) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      ((shiftTele (D.nm + q) (C.fields.length - i + s) i (D.atRecTele r.binders) 0).reverse
        ++ (((D.ihTypes q C).take s).reverse
          ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
            ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))) := by
    have h := Ctx.LiftN.tele (As := liftTele (D.nm + q) (D.atRecTele r.binders) i) W₂
    rw [show (0:Nat) + (liftTele (D.nm + q) (D.atRecTele r.binders) i).length
        = r.binders.length from by simp] at h
    have he := VExpr.liftTele_liftTele_eq_shiftTele (d := C.fields.length - i + s)
      (off := D.nm + q) (As := D.atRecTele r.binders) (i := i) (j := 0)
    rw [Nat.add_zero] at he
    rwa [he] at h
  have hlook := D.lookup_field (off := D.nm + q) (i := i) (s := s) (nf := C.fields.length)
    (Φ := C.fields.map (·.type)) (V := D.ihTypes q C) (A := F.type)
    (Γq := M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
    hi (by simp) hΦi hsV
  have hlook' : Lookup (((D.ihTypes q C).take s).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      (s + (C.fields.length - 1 - i))
      (((D.atRec F.type).liftN (D.nm + q) i).liftN (C.fields.length - i + s) 0) := by
    rw [show C.fields.length - i + s = s + (C.fields.length - 1 - i) + 1 from by omega]
    exact hlook
  have hdf0 : env.IsDefEqType D.recUvars
      ((D.atRecTele ((C.fields.map (·.type)).take i)).reverse
        ++ (D.atRecTele D.params).reverse)
      (D.atRec F.type) (D.atRec (r.canonType D i)) := by
    rw [← hac]; exact hFdefeq.instL D.selfLvls_wf
  have hfun0 := (VEnv.IsDefEqType.weakN henv W₂
    (VEnv.IsDefEqType.weakN henv W₁ hdf0)).defeq (.bvar hlook')
  rw [show ((D.atRec (r.canonType D i)).liftN (D.nm + q) i).liftN (C.fields.length - i + s) 0
        = mkPi (shiftTele (D.nm + q) (C.fields.length - i + s) i (D.atRecTele r.binders) 0)
          (VExpr.shift (D.nm + q) (C.fields.length - i + s) i
            (D.atRec (r.canonResult D i)) r.binders.length) from by
      rw [show ((D.atRec (r.canonType D i)).liftN (D.nm + q) i).liftN
            (C.fields.length - i + s) 0
          = VExpr.shift (D.nm + q) (C.fields.length - i + s) i
            (D.atRec (r.canonType D i)) 0 from by rw [VExpr.shift_def, Nat.add_zero],
        VIndRecArg.canonType, VInductDecl'.atRec_mkPi, VExpr.shift_mkPi,
        VInductDecl'.length_atRecTele, Nat.zero_add]] at hfun0
  have htyp : VExpr.shift (D.nm + q) (C.fields.length - i + s) i
        (D.atRec (r.canonResult D i)) r.binders.length
      = D.tyApp' r.idx (r.binders.length + i + (D.nm + q) + (C.fields.length - i + s))
        (r.args.map fun a => VExpr.shift (D.nm + q) (C.fields.length - i + s) i
          (D.atRec a) r.binders.length) := by
    rw [VIndRecArg.canonResult,
      D.shift_atRec_tyApp (t := r.idx) (k := r.binders.length + i) (i := i)
        (off := D.nm + q) (d := C.fields.length - i + s)
        (K := r.binders.length + i + (D.nm + q) + (C.fields.length - i + s))
        (j := r.binders.length) (args := r.args) (by omega) (by omega)]
  have happ := VEnv.HasType.appBVars henv hξ hfun0
  rw [VExpr.length_shiftTele, VInductDecl'.length_atRecTele,
    show (VExpr.bvar (s + (C.fields.length - 1 - i))).liftN r.binders.length
      = VExpr.bvar (r.binders.length + s + (C.fields.length - 1 - i)) from by
        simp only [VExpr.liftN, liftVar, Nat.not_lt_zero, ite_false]
        congr 1
        omega,
    htyp] at happ
  refine ⟨hi, hridx, hargl, hξ, ?_, ?_⟩
  · intro T'' hT'' u L harith
    exact VInductDecl'.ihArgs_hasArgs (D := D) (T' := T'') (u := u) (L := L)
      henv rfl (hargs T'' hT'') W₁' W₂' (by omega) harith
  · intro K hK
    subst hK
    exact happ

/-- **D4, per entry.**  The `s`-th induction hypothesis of minor `q` is a type in the context
of the earlier ones: `recField_facts` plus the motive lookup. -/
theorem ihType_isType' (hR : D.RecCtx env) {t q s i : Nat} {T : VIndType} {C : VIndCtor}
    {r : VIndRecArg} {F : VIndField}
    (hT : D.types[t]? = some T) (hC : C ∈ T.ctors)
    (hF : C.fields[i]? = some F) (hrec : F.recArg = some r)
    {M : List VExpr} (hMlen : M.length = q)
    (hM : OnCtx (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars))
    (hsV : ((D.ihTypes q C).take s).length = s)
    (hΓ₃ : OnCtx (((D.ihTypes q C).take s).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      (env.IsType D.recUvars)) :
    env.IsType D.recUvars
      (((D.ihTypes q C).take s).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      (D.ihType q C i r s) := by
  obtain ⟨hi, hridx, hargl, hξ, hidxf, hzf⟩ :=
    VInductDecl'.recField_facts hR hT hC hF hrec hMlen hM hsV hΓ₃
  obtain ⟨T', hT'⟩ : ∃ T', D.types[r.idx]? = some T' := ⟨_, List.getElem?_eq_getElem hridx⟩
  -- `hmot`
  have hmot : Lookup ((shiftTele (D.nm + q) (C.fields.length - i + s) i
        (D.atRecTele r.binders) 0).reverse
      ++ (((D.ihTypes q C).take s).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))))
      (r.binders.length + s + C.fields.length + q + (D.nm - 1 - r.idx))
      ((D.motiveType r.idx).liftN
        (r.binders.length + s + C.fields.length + q + (D.nm - 1 - r.idx) + 1)) := by
    have h := VInductDecl'.lookup_motive (D := D) hridx
      ((shiftTele (D.nm + q) (C.fields.length - i + s) i (D.atRecTele r.binders) 0).reverse
        ++ ((D.ihTypes q C).take s).reverse
        ++ (liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse ++ M)
      (D.atRecTele D.params).reverse
    simp only [List.length_append, List.length_reverse, VExpr.length_shiftTele,
      VInductDecl'.length_atRecTele, VExpr.length_liftTele, List.length_map, hsV, hMlen] at h
    simpa using h
  have hidx := hidxf T' hT' r.idx
    (r.binders.length + s + C.fields.length + q + (D.nm - 1 - r.idx) + 1) (by omega)
  have hz := hzf (r.binders.length + i + (D.nm + q) + (C.fields.length - i + s)) rfl
  exact VInductDecl'.ihType_isType (D := D) (T' := T') (q := q) (C := C) (i := i) (s := s)
    hT' hridx (by rw [List.length_map, hargl, getD_types hT']) rfl rfl (Nat.le_of_lt hi)
    rfl rfl rfl rfl hξ hmot hidx hz

end VInductDecl'

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- **D4.**  The induction-hypothesis telescope of minor `q` is a well-formed context over
the minor's field block. -/
theorem onCtxIhs (hR : D.RecCtx env) {t q : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[t]? = some T) (hC : C ∈ T.ctors)
    {M : List VExpr} (hMlen : M.length = q)
    (hM : OnCtx (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars))
    (hΓf : OnCtx ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (env.IsType D.recUvars)) :
    OnCtx ((D.ihTypes q C).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      (env.IsType D.recUvars) := by
  refine VEnv.OnCtx.ofTele₂ hΓf fun s A hA hpre => ?_
  rw [VInductDecl'.ihTypes_getElem?] at hA
  obtain ⟨⟨i, r⟩, hir, rfl⟩ := Option.map_eq_some_iff.1 hA
  obtain ⟨F, hF, hrec⟩ := VIndCtor.mem_recFields (List.mem_of_getElem? hir)
  have hs : s < C.recFields.length := by
    rcases Nat.lt_or_ge s C.recFields.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hir; exact absurd hir (by simp)
  have hsV : ((D.ihTypes q C).take s).length = s := by
    rw [List.length_take, VInductDecl'.length_ihTypes]; omega
  exact ihType_isType' hR hT hC hF hrec hMlen hM hsV hpre

/-- **D5, per minor.**  Minor premise `q` is a type in the context of the parameters, the
motives and the earlier minors. -/
theorem minorType_isType (hR : D.RecCtx env) {t q : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[t]? = some T) (ht : t < D.nm) (hC : C ∈ T.ctors)
    (hCall : (t, C) ∈ D.ctorsAll)
    {M : List VExpr} (hMlen : M.length = q)
    (hM : OnCtx (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars)) :
    env.IsType D.recUvars (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (D.minorType q t C) := by
  have henv := hR.ordered
  have hCwf : VIndCtor.WF env D t T C := hR.ctors t T hT C hC
  have hMD : (M ++ D.motives.reverse).length = D.nm + q := by
    rw [List.length_append, List.length_reverse, VInductDecl'.length_motives, hMlen]; omega
  have WD : Ctx.LiftN (D.nm + q) 0 (D.atRecTele D.params).reverse
      (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse) := .zero (M ++ D.motives.reverse) hMD
  have hacΦ : D.atRecCtx ((C.fields.map (·.type)).reverse ++ D.params.reverse)
      = (D.atRecTele (C.fields.map (·.type))).reverse ++ (D.atRecTele D.params).reverse := by
    rw [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse]; rfl
  have hΦ : OnCtx ((D.atRecTele (C.fields.map (·.type))).reverse
      ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars) := by
    rw [← hacΦ]; exact D.atRec_onCtx (hCwf.onCtxAllFields henv)
  have hΓf := VEnv.OnCtx.weakTele henv WD hM hΦ
  have hΓV := onCtxIhs hR hT hC hMlen hM hΓf
  -- `hmot`
  have hmot : Lookup ((D.ihTypes q C).reverse
      ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)))
      ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))
      ((D.motiveType t).liftN
        ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t) + 1)) := by
    have h := VInductDecl'.lookup_motive (D := D) ht
      ((D.ihTypes q C).reverse
        ++ (liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse ++ M)
      (D.atRecTele D.params).reverse
    simp only [List.length_append, List.length_reverse, VExpr.length_liftTele,
      VInductDecl'.length_atRecTele, List.length_map, hMlen] at h
    simpa using h
  -- `hidx`
  have W₁min : Ctx.LiftN (D.nm + q) C.fields.length
      ((D.atRecTele ([] : List VExpr)).reverse
        ++ D.atRecCtx ((C.fields.map (·.type)).reverse ++ D.params.reverse))
      ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)) := by
    rw [hacΦ]
    have h := Ctx.LiftN.tele (As := D.atRecTele (C.fields.map (·.type))) WD
    rwa [show (0:Nat) + (D.atRecTele (C.fields.map (·.type))).length = C.fields.length from by
      rw [Nat.zero_add, VInductDecl'.length_atRecTele, List.length_map]] at h
  have W₂min : Ctx.LiftN (D.ihTypes q C).length 0
      ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      ((D.ihTypes q C).reverse
        ++ ((liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) 0).reverse
          ++ (M ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))) :=
    .zero (D.ihTypes q C).reverse (by rw [List.length_reverse])
  have hidx := VInductDecl'.ihArgs_hasArgs (D := D) (T' := T) (ξ := []) (ras := C.args)
    (Γfield := (C.fields.map (·.type)).reverse ++ D.params.reverse)
    (i := C.fields.length) (nxi := 0) (p := C.fields.length)
    (off := D.nm + q) (d := (D.ihTypes q C).length) (u := t)
    (L := (D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t) + 1)
    henv (by omega) hCwf.args_ty W₁min W₂min (by omega) (by omega)
  -- `hz`
  have hz0 := VInductDecl'.ctorApp'_hasType hR hT hC hCall (m := D.nm + q)
    (Δ := M ++ D.motives.reverse) hMD hM
  have hz := hz0.weakN henv
    (Ctx.LiftN.zero (D.ihTypes q C).reverse (by rw [List.length_reverse]))
  rw [show (D.ctorApp' C (C.fields.length + (D.nm + q)) (bvars 0 C.fields.length)).liftN
        (D.ihTypes q C).length 0
      = D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
        (bvars (D.ihTypes q C).length C.fields.length) from by
      rw [VInductDecl'.ctorApp', VInductDecl'.ctorApp', VExpr.liftN_mkApp, List.map_append,
        VExpr.map_liftN_bvars_lo (Nat.zero_le _), VExpr.map_liftN_bvars_lo (Nat.zero_le _)]
      simp only [VExpr.liftN, Nat.add_zero, Nat.add_assoc],
    show ((D.atRec (C.canonResult D t)).liftN (D.nm + q) C.fields.length).liftN
        (D.ihTypes q C).length 0
      = D.tyApp' t ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
        (C.args.map fun a => VExpr.shift (D.nm + q) (D.ihTypes q C).length C.fields.length
          (D.atRec a)) from by
      rw [show ((D.atRec (C.canonResult D t)).liftN (D.nm + q) C.fields.length).liftN
            (D.ihTypes q C).length 0
          = VExpr.shift (D.nm + q) (D.ihTypes q C).length C.fields.length
            (D.atRec (C.canonResult D t)) 0 from by rw [VExpr.shift_def, Nat.add_zero],
        VIndCtor.canonResult,
        D.shift_atRec_tyApp (t := t) (k := C.fields.length) (i := C.fields.length)
          (off := D.nm + q) (d := (D.ihTypes q C).length)
          (K := (D.ihTypes q C).length + C.fields.length + (D.nm + q)) (j := 0)
          (args := C.args) (by omega) (by omega)]] at hz
  -- assembly
  simp only [VInductDecl'.minorType]
  refine VEnv.IsType.mkPi ?_ ?_
  · rw [List.reverse_append, List.append_assoc]; exact hΓV
  · refine ⟨D.elimLvl, ?_⟩
    rw [List.reverse_append, List.append_assoc]
    exact VInductDecl'.minorBody_hasType hT ht hCwf.args_len hmot hidx hz

end VInductDecl'

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

theorem minors_getElem? (D : VInductDecl') (q : Nat) :
    D.minors[q]? = (D.ctorsAll[q]?).map fun tC => D.minorType q tC.1 tC.2 := by
  simp only [VInductDecl'.minors, List.getElem?_map, List.getElem?_zipIdx, Option.map_map,
    Nat.zero_add]
  rfl

/-- **D5.**  The minor telescope is a well-formed context over the parameters and the
motives -- the last obligation of `addInduct'_ordered'` apart from E5. -/
theorem onCtxMinors (hR : D.RecCtx env) :
    OnCtx (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      (env.IsType D.recUvars) := by
  rw [List.append_assoc]
  refine VEnv.OnCtx.ofTele₂ (onCtxMotives hR) fun q A hA hpre => ?_
  rw [VInductDecl'.minors_getElem?] at hA
  obtain ⟨⟨t, C⟩, htC, rfl⟩ := Option.map_eq_some_iff.1 hA
  have hCall : (t, C) ∈ D.ctorsAll := List.mem_of_getElem? htC
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll hCall
  have ht : t < D.nm := by
    rcases Nat.lt_or_ge t D.types.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hT; exact absurd hT (by simp)
  have hq : q < D.nmin := by
    rcases Nat.lt_or_ge q D.ctorsAll.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at htC; exact absurd htC (by simp)
  have hMlen : (D.minors.take q).reverse.length = q := by
    rw [List.length_reverse, List.length_take, VInductDecl'.length_minors]; omega
  rw [← List.append_assoc] at hpre ⊢
  exact minorType_isType hR hT ht hC hCall hMlen hpre

end VInductDecl'

/-- **`addInduct'` preserves `Ordered`, with D5 and D6 both discharged.**  E5 (`hrules`) is
the only obligation left. -/
theorem VInductDecl'.addInduct'_ordered'' {env env' : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) (h : D.WF env)
    (hrules : ∀ {env₁ env₂ env₃ : VEnv}, env.addIndTypes D = some env₁ →
      env₁.addIndCtors D = some env₂ → env₂.addIndRecs D = some env₃ →
      ∀ df ∈ D.iotaRules, df.WF env₃)
    (he : env.addInduct' D = some env') : env'.Ordered :=
  VInductDecl'.addInduct'_ordered' henv h (fun hR => VInductDecl'.onCtxMinors hR) hrules he

/-! ## E5: the ι-rules

`VDefEq.WF` asks for both sides of each rule to have the rule's own type in the empty
context.  Both go through `HasType.mkLams` over `iotaCtx C`, whose `OnCtx` is D5 plus one
`weakTele`; the content is in the two bodies. -/

/-- **Locating an entry of a reversed telescope.**  If `l[q]? = some A` then, in any context
whose `l`-block is `l.reverse`, the index `|Δ| + (|l| - 1 - q)` names `A`.  (`lookup_motive`
is the `List.range`-specific version; this one is what the minors need, since `D.minors` is
a `zipIdx.map` rather than a mapped range.) -/
theorem Lookup.of_reverse {l : List VExpr} {q : Nat} {A : VExpr} (h : l[q]? = some A)
    (Δ Γ₀ : List VExpr) :
    Lookup (Δ ++ l.reverse ++ Γ₀) (Δ.length + (l.length - 1 - q))
      (A.liftN (Δ.length + (l.length - 1 - q) + 1)) := by
  have hq : q < l.length := by
    rcases Nat.lt_or_ge q l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; exact absurd h (by simp)
  have ha : l[q] = A := by
    have h2 := List.getElem?_eq_getElem hq
    rw [h] at h2; exact (Option.some_inj.1 h2).symm
  have hsplit : l.reverse = (l.drop (q+1)).reverse ++ A :: (l.take q).reverse := by
    have h1 : (l.take q ++ A :: l.drop (q+1)).reverse
        = (l.drop (q+1)).reverse ++ A :: (l.take q).reverse := by simp
    rw [← h1, ← ha, ← List.drop_eq_getElem_cons hq, List.take_append_drop]
  have hΞ : (Δ ++ (l.drop (q+1)).reverse).length = Δ.length + (l.length - 1 - q) := by
    simp only [List.length_append, List.length_reverse, List.length_drop]
    omega
  have hctx : Δ ++ l.reverse ++ Γ₀
      = (Δ ++ (l.drop (q+1)).reverse) ++ A :: ((l.take q).reverse ++ Γ₀) := by
    rw [hsplit]; simp
  rw [hctx, ← hΞ]
  exact Lookup.append _

namespace VEnv

/-- Extend a `HasArgs` by one more argument at the end of the telescope. -/
theorem HasArgs.concat {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As as A a}, HasArgs env U Γ As as → env.HasType U Γ a (VExpr.instAll A as 0) →
      HasArgs env U Γ (As ++ [A]) (as ++ [a])
  | _, _, A, a, .nil, ha => .cons (by simpa using ha) .nil
  | A₀ :: As, a₀ :: as, A, a, .cons h0 h, ha => by
    refine .cons h0 ?_
    show HasArgs env U Γ (VExpr.instTele a₀ (As ++ [A])) (as ++ [a])
    rw [VExpr.instTele_append, Nat.zero_add]
    refine HasArgs.concat h ?_
    rw [VExpr.instAll_cons, Nat.zero_add] at ha
    rwa [show As.length = as.length from by
      have h2 := h.length_eq; rwa [VExpr.length_instTele] at h2]

end VEnv

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- The `d := 0` companion of `shift_atRec_tyApp`: a plain weakening rather than a
`shift`. -/
theorem liftN_atRec_tyApp (D : VInductDecl') {t k i off K : Nat} {args : List VExpr}
    (hik : i ≤ k) (hK : off + k = K) :
    (D.atRec (D.tyApp t k args)).liftN off i
      = D.tyApp' t K (args.map fun a => (D.atRec a).liftN off i) := by
  have h1 : D.atRec (D.tyApp t k args)
      = (VExpr.const (D.types.getD t default).name D.selfLvls).mkApp
        (bvars k D.np ++ args.map D.atRec) := by
    simp only [VInductDecl'.tyApp, VInductDecl'.atRec_mkApp, List.map_append,
      VInductDecl'.atRec_bvars, VInductDecl'.atRec_const,
      VInductDecl'.ownLvls_inst_selfLvls]
  rw [h1, VExpr.mkApp_append, VExpr.liftN_mkApp, VExpr.liftN_mkApp_bvars_lo hik, hK,
    VInductDecl'.tyApp', VExpr.mkApp_append, List.map_map]
  rfl

/-- `tyApp'_instAll` with the inner parameter offset left free: the recursor's major-premise
domain is `I_j p ι` with the parameters at `ni + nmin + nm`, not at `ni + j`. -/
theorem tyApp'_instAll' {j ni K₀ L M : Nat} {ιs : List VExpr} (hlen : ιs.length = ni)
    (hni : ni ≤ K₀) (h : L + K₀ - ni = M) :
    VExpr.instAll ((D.tyApp' j K₀ (bvars 0 ni)).liftN L ni) ιs 0 = D.tyApp' j M ιs := by
  have hL : (D.tyApp' j K₀ (bvars 0 ni)).liftN L ni
      = (VExpr.const (D.types.getD j default).name D.selfLvls).mkApp
          (bvars (L + K₀) D.np ++ bvars 0 ni) := by
    rw [VInductDecl'.tyApp', VExpr.liftN_mkApp, List.map_append,
      VExpr.map_liftN_bvars_lo hni,
      VExpr.map_liftN_bvars_hi (Nat.le_of_eq (Nat.zero_add ni))]
    rfl
  rw [hL, VInductDecl'.tyApp', VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    VExpr.map_instAll_bvars_ge (by rw [hlen]; omega), hlen, h,
    VExpr.map_instAll_bvars' hlen]

/-- **The recursor's codomain, saturated.**  `recType`'s body -- the motive applied to the
index variables and the major variable -- lifted past the minor's field block and then
instantiated by the constructor's index *terms* and the constructor application, is exactly
`iotaType`'s shape.  The spine `bvars 1 ni ++ [.bvar 0]` is `bvars 0 (ni+1)`, so this is one
application of `map_instAll_bvars'`. -/
theorem recCod_instAll {ni nf B M : Nat} {ιs : List VExpr} {z : VExpr}
    (hlen : ιs.length = ni) (hB : ni + 1 ≤ B) (hM : nf + B - (ni + 1) = M) :
    VExpr.instAll
        (((VExpr.bvar B).mkApp (bvars 1 ni ++ [VExpr.bvar 0])).liftN nf (ni + 1))
        (ιs ++ [z]) 0
      = (VExpr.bvar M).mkApp (ιs ++ [z]) := by
  have hb : bvars 1 ni ++ [VExpr.bvar 0] = bvars 0 (ni + 1) := by
    rw [VExpr.bvars_add (m := ni) (n := 1)]; rfl
  have hz : (ιs ++ [z]).length = ni + 1 := by rw [List.length_append, hlen]; rfl
  rw [hb, VExpr.liftN_mkApp_bvars_hi (Nat.le_of_eq (Nat.zero_add _)), VExpr.instAll_mkApp,
    VExpr.map_instAll_bvars' hz,
    show (VExpr.bvar B).liftN nf (ni + 1) = VExpr.bvar (nf + B) from by
      simp only [VExpr.liftN, liftVar, if_neg (show ¬ (B < ni + 1) by omega)],
    VExpr.instAll_bvar_ge (by rw [hz]; omega), hz, hM]

end VInductDecl'

/-! ### The two `shift` laws the ι-rule's induction hypotheses need

An induction-hypothesis *type* is recorded at minor `q`'s offsets and at ih-depth `s`; the
ι-rule needs it at the block's full offsets (`nmin` in place of `q`) and at depth `0`.  The
two moves are a weakening in the `off` slot and a weakening in the `d` slot, and each is one
application of the `liftN` algebra. -/

namespace VExpr

/-- Widening the `d` slot: `s` more binders below the fields. -/
theorem shift_add_d (e : VExpr) (off d i j s : Nat) :
    (shift off d i e j).liftN s j = shift off (d + s) i e j := by
  rw [shift_def, shift_def, liftN'_liftN_hi]

theorem shiftTele_add_d : ∀ (X : List VExpr) (off d i s j : Nat),
    liftTele s (shiftTele off d i X j) j = shiftTele off (d + s) i X j
  | [], _, _, _, _, _ => rfl
  | A :: X, off, d, i, s, j => by
    rw [shiftTele_cons, liftTele_cons, shift_add_d, shiftTele_cons,
      shiftTele_add_d X off d i s (j + 1)]

/-- Widening the `off` slot: `R` more binders between the fields and the parameters.  The
cut is `d + (i + j)`, i.e. exactly the top of the field block. -/
theorem shift_add_off (e : VExpr) (off d i j R : Nat) :
    (shift off d i e j).liftN R (d + (i + j)) = shift (off + R) d i e j := by
  rw [shift_def, shift_def, ← liftN'_liftN_hi e off R (i + j),
    liftN'_comm (liftN off e (i + j)) R d (i + j) j (Nat.le_add_left ..)]

theorem shiftTele_add_off : ∀ (X : List VExpr) (off d i R j : Nat),
    liftTele R (shiftTele off d i X j) (d + (i + j)) = shiftTele (off + R) d i X j
  | [], _, _, _, _, _ => rfl
  | A :: X, off, d, i, R, j => by
    rw [shiftTele_cons, liftTele_cons, shift_add_off, shiftTele_cons,
      show d + (i + j) + 1 = d + (i + (j + 1)) from by omega,
      shiftTele_add_off X off d i R (j + 1)]

end VExpr

namespace VEnv

/-- **A telescope whose entries do not depend on the earlier arguments.**  If entry `s` is a
lift by `s` of a term that already types argument `s`, the whole `HasArgs` follows: each
`instTele` step just cancels one of those lifts (`inst_liftN'`).

This is what the ι-rule's induction-hypothesis block needs -- an ih type mentions the
motives, the fields and the parameters, but never an earlier ih. -/
theorem HasArgs.of_lifts {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As bs : List VExpr}, As.length = bs.length →
      (∀ s A b, As[s]? = some A → bs[s]? = some b →
        ∃ A', A = A'.liftN s 0 ∧ env.HasType U Γ b A') →
      HasArgs env U Γ As bs
  | [], [], _, _ => .nil
  | A₀ :: As, b₀ :: bs, hlen, h => by
    obtain ⟨A₀', hA₀, hb₀⟩ := h 0 A₀ b₀ rfl rfl
    rw [VExpr.liftN_zero] at hA₀
    subst hA₀
    refine .cons hb₀ (HasArgs.of_lifts ?_ fun s A b hA hb => ?_)
    · simpa using hlen
    · rw [VExpr.getElem?_instTele] at hA
      obtain ⟨A₁, hA₁, rfl⟩ := Option.map_eq_some_iff.1 hA
      obtain ⟨A', rfl, hb'⟩ := h (s + 1) A₁ b (by simpa using hA₁) (by simpa using hb)
      refine ⟨A', ?_, hb'⟩
      rw [Nat.zero_add,
        ← VExpr.liftN'_liftN' (n1 := s) (n2 := 1) (k1 := 0) (k2 := s)
          (Nat.zero_le _) (Nat.le_of_eq (Nat.add_zero s).symm),
        VExpr.inst_liftN]

end VEnv

/-! ### Splitting a saturated application into two blocks

`iotaLam`'s body applies the minor premise to the field variables *and* the
induction-hypothesis values, so both the telescope and the `instAll` on the codomain have to
be split after the field block. -/

namespace VExpr

/-- `instAll` over a concatenated spine: consume the first block with the second block's
length added to the cut, then the second. -/
theorem instAll_append : ∀ {as bs : List VExpr} {e k},
    instAll e (as ++ bs) k = instAll (instAll e as (k + bs.length)) bs k
  | [], _, _, _ => by simp
  | a :: as, bs, e, k => by
    have h : k + (as ++ bs).length = k + bs.length + as.length := by simp; omega
    rw [List.cons_append, instAll_cons, h, instAll_append (as := as), instAll_cons]

theorem instAllTele_nil_args : ∀ {As : List VExpr} {k}, instAllTele As [] k = As
  | [], _ => rfl
  | _ :: _, _ => by rw [instAllTele_cons, instAll_nil, instAllTele_nil_args]

theorem instAllTele_cons_args : ∀ {As : List VExpr} {a as k},
    instAllTele As (a :: as) k = instAllTele (instTele a As (k + as.length)) as k
  | [], _, _, _ => rfl
  | A :: As, a, as, k => by
    rw [instAllTele_cons, instAll_cons, instTele_cons, instAllTele_cons,
      show k + as.length + 1 = k + 1 + as.length from by omega,
      instAllTele_cons_args (As := As)]

/-- **Reading a value out of a saturated substitution.**  `instAll e as k` replaces the
variable at position `k + |as| - 1 - t` by `as[t]`, weakened past the `k` binders below the
window.  Stated with the index as an equation so callers never meet a truncated subtraction. -/
theorem instAll_bvar_get : ∀ {as : List VExpr} {k t B : Nat} {a : VExpr}, as[t]? = some a →
    k + as.length = B + 1 + t → instAll (.bvar B) as k = a.liftN k 0
  | [], _, _, _, _, h, _ => by simp at h
  | a₀ :: as, k, 0, B, a, h, hB => by
    rw [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have hB' : B = k + as.length := by simp at hB; omega
    subst hB'
    rw [instAll_cons,
      show (VExpr.bvar (k + as.length)).inst a₀ (k + as.length) = a₀.liftN (k + as.length) 0 from by
        simp only [inst, instVar, if_neg (Nat.lt_irrefl _), if_true],
      ← liftN'_liftN' (n1 := k) (n2 := as.length) (k1 := 0) (k2 := k)
        (Nat.zero_le _) (Nat.le_of_eq (Nat.add_zero k).symm),
      instAll_liftN]
  | a₀ :: as, k, t + 1, B, a, h, hB => by
    rw [List.getElem?_cons_succ] at h
    have hlt : B < k + as.length := by simp at hB; omega
    rw [instAll_cons,
      show (VExpr.bvar B).inst a₀ (k + as.length) = VExpr.bvar B from by
        simp only [inst, instVar, if_pos hlt],
      instAll_bvar_get h (by simp at hB ⊢; omega)]

/-- Below the substitution window, `instAll` is the identity. -/
theorem instAll_bvar_lt' : ∀ {as : List VExpr} {k i : Nat}, i < k →
    instAll (.bvar i) as k = .bvar i
  | [], _, _, _ => rfl
  | a₀ :: as, k, i, h => by
    rw [instAll_cons,
      show (VExpr.bvar i).inst a₀ (k + as.length) = VExpr.bvar i from by
        simp only [inst, instVar, if_pos (show i < k + as.length by omega)],
      instAll_bvar_lt' h]

theorem map_instAll_bvars_lt {as : List VExpr} {lo k : Nat} :
    ∀ {n : Nat}, lo + n ≤ k → (bvars lo n).map (instAll · as k) = bvars lo n
  | 0, _ => rfl
  | n + 1, h => by
    rw [bvars_succ, List.map_cons, instAll_bvar_lt' (show lo + n < k by omega),
      map_instAll_bvars_lt (show lo + n ≤ k by omega)]

/-- A `bvars` block sitting at the *top* of the substitution window picks out the first `n`
values, each weakened past the `k` binders below the window. -/
theorem map_instAll_bvars_top {as : List VExpr} {lo n k : Nat}
    (hk : k ≤ lo) (h : lo + n = k + as.length) :
    (bvars lo n).map (instAll · as k) = (as.take n).map (liftN k · 0) := by
  have hn : n ≤ as.length := by omega
  refine List.ext_getElem? fun m => ?_
  rw [List.getElem?_map, List.getElem?_map, getElem?_bvars, List.getElem?_take]
  rcases Nat.lt_or_ge m n with hm | hm
  · rw [if_pos hm, if_pos hm]
    obtain ⟨a, ha⟩ : ∃ a, as[m]? = some a := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [ha, Option.map_some, Option.map_some, Option.some.injEq]
    exact instAll_bvar_get ha (by omega)
  · rw [if_neg (by omega), if_neg (by omega)]
    rfl

/-- The `R`-fold generalisation of `instAll_liftN_bvars`: instantiating `n` of the `R + n`
inserted binders by the identity spine leaves a lift by `R`. -/
theorem instAll_liftN_bvars₂ (n R k : Nat) (e : VExpr) :
    instAll (liftN (R + n) e (k + n)) (bvars 0 n) k = liftN R e (k + n) := by
  rw [← liftN'_liftN_hi e R n (k + n), instAll_liftN_bvars]

theorem instAllTele_liftTele_bvars₂ (n R : Nat) : ∀ (As : List VExpr) (k : Nat),
    instAllTele (liftTele (R + n) As (k + n)) (bvars 0 n) k = liftTele R As (k + n)
  | [], _ => rfl
  | A :: As, k => by
    rw [liftTele_cons, instAllTele_cons, instAll_liftN_bvars₂, liftTele_cons,
      show k + n + 1 = k + 1 + n from by omega, instAllTele_liftTele_bvars₂ n R As (k + 1)]

end VExpr

namespace VEnv

/-- `HasArgs` over a concatenated telescope.  The second block must be stated with the first
block's arguments already substituted -- that is what `instAllTele_liftTele_bvars₂` computes
for the minor premise's induction-hypothesis block. -/
theorem HasArgs.append {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As as Bs bs : List VExpr}, HasArgs env U Γ As as →
      HasArgs env U Γ (VExpr.instAllTele Bs as 0) bs →
      HasArgs env U Γ (As ++ Bs) (as ++ bs)
  | _, _, _, _, .nil, h => by rwa [VExpr.instAllTele_nil_args] at h
  | A₀ :: As, a₀ :: as, Bs, bs, .cons h0 h, hB => by
    refine .cons h0 ?_
    show HasArgs env U Γ (VExpr.instTele a₀ (As ++ Bs)) (as ++ bs)
    rw [VExpr.instTele_append, Nat.zero_add]
    refine HasArgs.append h ?_
    rw [VExpr.instAllTele_cons_args, Nat.zero_add] at hB
    rwa [show As.length = as.length from by
      have h2 := h.length_eq; rwa [VExpr.length_instTele] at h2]

end VEnv

/-! ### An induction-hypothesis type, moved from minor `q` to the ι-rule

`ihType` is a single formula in four offsets, so the two moves the ι-rule needs -- widening
`off` from `nm + q` to `nm + nmin`, and widening `d` past the `s` earlier ihs -- are each one
lemma about that shape rather than a second traversal of the definition. -/

/-- The shape of an induction-hypothesis type with its offsets abstracted: `off`/`d`/`i` for
the `shift`, `m` for the motive variable and `f` for the recursive field. -/
def VInductDecl'.ihShape (D : VInductDecl') (off d i : Nat) (r : VIndRecArg) (m f : Nat) :
    VExpr :=
  mkPi (shiftTele off d i (D.atRecTele r.binders)) <|
    (VExpr.bvar m).mkApp <|
      r.args.map (fun a => shift off d i (D.atRec a) r.binders.length) ++
      [(VExpr.bvar f).mkApp (bvars 0 r.binders.length)]

theorem VInductDecl'.ihType_eq_ihShape (D : VInductDecl') (q : Nat) (C : VIndCtor) (i : Nat)
    (r : VIndRecArg) (s : Nat) :
    D.ihType q C i r s = D.ihShape (D.nm + q) (C.fields.length - i + s) i r
      (r.binders.length + s + C.fields.length + q + (D.nm - 1 - r.idx))
      (r.binders.length + s + (C.fields.length - 1 - i)) := rfl

/-- Widening `d`: `s` more binders below the fields.  Both variables sit at or above the
`ξ`-telescope, so both move up by `s`. -/
theorem VInductDecl'.ihShape_add_d (D : VInductDecl') {off d i m f s : Nat} {r : VIndRecArg}
    (hm : r.binders.length ≤ m) (hf : r.binders.length ≤ f) :
    (D.ihShape off d i r m f).liftN s 0
      = D.ihShape off (d + s) i r (s + m) (s + f) := by
  rw [VInductDecl'.ihShape, VInductDecl'.ihShape, VExpr.liftN_mkPi, VExpr.length_shiftTele,
    VInductDecl'.length_atRecTele, Nat.zero_add, VExpr.shiftTele_add_d, VExpr.liftN_mkApp,
    List.map_append, List.map_map, List.map_cons, List.map_nil,
    VExpr.liftN_mkApp_bvars_hi (Nat.le_of_eq (Nat.zero_add _)),
    show (VExpr.bvar m).liftN s r.binders.length = VExpr.bvar (s + m) from by
      simp only [VExpr.liftN, liftVar, if_neg (show ¬ (m < r.binders.length) by omega)],
    show (VExpr.bvar f).liftN s r.binders.length = VExpr.bvar (s + f) from by
      simp only [VExpr.liftN, liftVar, if_neg (show ¬ (f < r.binders.length) by omega)]]
  simp only [Function.comp_def, VExpr.shift_add_d]

/-- Widening `off`: `R` more binders between the fields and the parameters.  The cut is the
top of the field block, so the motive variable (above it) moves and the recursive field
(below it) does not. -/
theorem VInductDecl'.ihShape_add_off (D : VInductDecl') {off d i m f R : Nat}
    {r : VIndRecArg} (hm : d + i + r.binders.length ≤ m)
    (hf : f < d + i + r.binders.length) :
    (D.ihShape off d i r m f).liftN R (d + i)
      = D.ihShape (off + R) d i r (R + m) f := by
  rw [VInductDecl'.ihShape, VInductDecl'.ihShape, VExpr.liftN_mkPi, VExpr.length_shiftTele,
    VInductDecl'.length_atRecTele,
    show d + i + r.binders.length = d + (i + r.binders.length) from by omega,
    show d + i = d + (i + 0) from by omega, VExpr.shiftTele_add_off, VExpr.liftN_mkApp,
    List.map_append, List.map_map, List.map_cons, List.map_nil,
    VExpr.liftN_mkApp_bvars_hi (by omega),
    show (VExpr.bvar m).liftN R (d + (i + r.binders.length)) = VExpr.bvar (R + m) from by
      simp only [VExpr.liftN, liftVar,
        if_neg (show ¬ (m < d + (i + r.binders.length)) by omega)],
    show (VExpr.bvar f).liftN R (d + (i + r.binders.length)) = VExpr.bvar f from by
      simp only [VExpr.liftN, liftVar, if_pos (show f < d + (i + r.binders.length) by omega)]]
  simp only [Function.comp_def, VExpr.shift_add_off]

/-- **The ι-rule's induction-hypothesis type.**  Minor `q` records its `s`-th ih at offset
`nm + q` and ih-depth `s`; the ι-rule needs it at `nm + q'` and depth `0`, weakened past the
`s` earlier ihs.  This is what makes `iotaLam`'s ih block independent of the earlier ih
*values*: entry `s` is a lift by `s` of a term that never mentions them. -/
theorem VInductDecl'.ihType_shift (D : VInductDecl') {q q' R s i : Nat} {C : VIndCtor}
    {r : VIndRecArg} (hi : i < C.fields.length) (hR : q + R = q') :
    (D.ihType q C i r s).liftN R (C.fields.length + s)
      = (D.ihType q' C i r 0).liftN s 0 := by
  rw [VInductDecl'.ihType_eq_ihShape, VInductDecl'.ihType_eq_ihShape,
    show C.fields.length + s = C.fields.length - i + s + i from by omega,
    D.ihShape_add_off (by omega) (by omega),
    D.ihShape_add_d (by omega) (by omega)]
  congr 1 <;> omega

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

@[simp] theorem length_ihValues (D : VInductDecl') (C : VIndCtor) :
    (D.ihValues C).length = C.recFields.length := by simp [VInductDecl'.ihValues]

/-- **The minor premise's body is a lift by `nr`.**  It mentions the fields, the motives and
the parameters, but never an induction hypothesis -- which is what lets the ih half of
`minorBody_instAll` collapse by `instAll_liftN`. -/
theorem minorBody_eq_liftN (D : VInductDecl') (j q : Nat) (C : VIndCtor) :
    (VExpr.bvar (C.recFields.length + C.fields.length + q + (D.nm - 1 - j))).mkApp
        ((C.args.map fun a => VExpr.shift (D.nm + q) C.recFields.length C.fields.length
            (D.atRec a))
          ++ [D.ctorApp' C (C.recFields.length + C.fields.length + (D.nm + q))
              (bvars C.recFields.length C.fields.length)])
      = ((VExpr.bvar (C.fields.length + q + (D.nm - 1 - j))).mkApp
          ((C.args.map fun a => (D.atRec a).liftN (D.nm + q) C.fields.length)
            ++ [D.ctorApp' C (C.fields.length + (D.nm + q)) (bvars 0 C.fields.length)])).liftN
        C.recFields.length 0 := by
  simp only [VExpr.liftN_mkApp, List.map_append, List.map_map, List.map_cons, List.map_nil,
    Function.comp_def, VExpr.shift_def, VInductDecl'.ctorApp',
    VExpr.map_liftN_bvars_lo (Nat.zero_le _), VExpr.liftN, liftVar, Nat.not_lt_zero,
    ite_false, Nat.add_zero, Nat.add_assoc]

/-- **…and that lift, widened from minor `q`'s offsets to the block's, is `iotaType`.** -/
theorem minorBody_liftN_eq (D : VInductDecl') {j q R : Nat} (C : VIndCtor)
    (hR : q + R = D.nmin) :
    ((VExpr.bvar (C.fields.length + q + (D.nm - 1 - j))).mkApp
        ((C.args.map fun a => (D.atRec a).liftN (D.nm + q) C.fields.length)
          ++ [D.ctorApp' C (C.fields.length + (D.nm + q)) (bvars 0 C.fields.length)])).liftN
      R C.fields.length
      = D.iotaType j C := by
  rw [VInductDecl'.iotaType, VExpr.liftN_mkApp, List.map_append, List.map_map,
    List.map_cons, List.map_nil,
    show (VExpr.bvar (C.fields.length + q + (D.nm - 1 - j))).liftN R C.fields.length
        = VExpr.bvar (C.fields.length + D.nmin + (D.nm - 1 - j)) from by
      simp only [VExpr.liftN, liftVar,
        if_neg (show ¬ (C.fields.length + q + (D.nm - 1 - j) < C.fields.length) by omega)]
      congr 1
      omega,
    VInductDecl'.ctorApp', VInductDecl'.ctorApp', VExpr.liftN_mkApp, List.map_append,
    VExpr.map_liftN_bvars_lo (Nat.le_add_right ..),
    VExpr.map_liftN_bvars_hi (Nat.le_of_eq (Nat.zero_add _)),
    show R + (C.fields.length + (D.nm + q)) = C.fields.length + (D.nm + D.nmin) from by omega]
  refine congrArg _ (congrArg (· ++ _) ?_)
  refine List.map_congr_left fun a _ => ?_
  rw [Function.comp_apply, VExpr.liftN'_liftN_hi,
    show D.nm + q + R = D.nm + D.nmin from by omega]

/-- **The minor premise's codomain, saturated.**  `minorType q`'s body, weakened into the
ι-rule's context and then applied to the field variables and the induction-hypothesis
*values*, is exactly `iotaType`.

`instAll_append` splits the spine after the fields: the field half collapses by
`instAll_liftN_bvars` (the `K`-lift contains the `nf` binders the identity spine
instantiates) and the ih half by `instAll_liftN` (the body is a lift by `nr`). -/
theorem minorBody_instAll (D : VInductDecl') {j q : Nat} (C : VIndCtor) (hq : q < D.nmin) :
    VExpr.instAll
      (((VExpr.bvar (C.recFields.length + C.fields.length + q + (D.nm - 1 - j))).mkApp
          ((C.args.map fun a => VExpr.shift (D.nm + q) C.recFields.length C.fields.length
              (D.atRec a))
            ++ [D.ctorApp' C (C.recFields.length + C.fields.length + (D.nm + q))
                (bvars C.recFields.length C.fields.length)])).liftN
        (C.fields.length + (D.nmin - 1 - q) + 1)
        (C.fields.length + C.recFields.length))
      (bvars 0 C.fields.length ++ D.ihValues C) 0
      = D.iotaType j C := by
  rw [D.minorBody_eq_liftN j q C, VExpr.instAll_append,
    show (D.ihValues C).length = C.recFields.length from D.length_ihValues C,
    Nat.zero_add,
    show C.fields.length + (D.nmin - 1 - q) + 1
        = (D.nmin - 1 - q + 1) + C.fields.length from by omega,
    ← VExpr.liftN'_liftN_hi _ (D.nmin - 1 - q + 1) C.fields.length
      (C.fields.length + C.recFields.length),
    show C.fields.length + C.recFields.length = C.recFields.length + C.fields.length from by
      omega,
    VExpr.instAll_liftN_bvars,
    ← VExpr.liftN'_comm _ (D.nmin - 1 - q + 1) C.recFields.length C.fields.length 0
      (Nat.zero_le _),
    show C.recFields.length = (D.ihValues C).length from (D.length_ihValues C).symm,
    VExpr.instAll_liftN,
    D.minorBody_liftN_eq (R := D.nmin - 1 - q + 1) C (by omega)]

end VInductDecl'

/-- The situation in which the ι-rules are checked: everything `RecCtx` provides, plus the
block's recursor constants at their generated types.  `addIndRecs` produces exactly this,
which is why `addInduct'_ordered`'s `hrules` is stated over the staged environments. -/
structure VInductDecl'.IotaCtx (env : VEnv) (D : VInductDecl') : Prop where
  toRecCtx : D.RecCtx env
  recConsts : ∀ j (T : VIndType), D.types[j]? = some T →
    env.constants (Lean.mkRecName T.name) = some ⟨D.recUvars, D.recType j⟩

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- The ι-rule's binder context is well-formed: D5 plus one `weakTele` for the fields. -/
theorem onCtxIota (hR : D.RecCtx env) {j : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[j]? = some T) (hC : C ∈ T.ctors) :
    OnCtx ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (env.IsType D.recUvars) := by
  have henv := hR.ordered
  have hCwf : VIndCtor.WF env D j T C := hR.ctors j T hT C hC
  have hacΦ : D.atRecCtx ((C.fields.map (·.type)).reverse ++ D.params.reverse)
      = (D.atRecTele (C.fields.map (·.type))).reverse ++ (D.atRecTele D.params).reverse := by
    rw [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse]; rfl
  have hΦ : OnCtx ((D.atRecTele (C.fields.map (·.type))).reverse
      ++ (D.atRecTele D.params).reverse) (env.IsType D.recUvars) := by
    rw [← hacΦ]; exact D.atRec_onCtx (hCwf.onCtxAllFields henv)
  exact VEnv.OnCtx.weakTele henv
    (.zero (D.minors.reverse ++ D.motives.reverse) (by
      rw [List.length_append, List.length_reverse, List.length_reverse,
        VInductDecl'.length_minors, VInductDecl'.length_motives]; omega))
    (VInductDecl'.onCtxMinors hR) hΦ

/-- **The recursor, saturated.**  `I_u.rec` at the recursor's own level list, applied to the
parameter, motive and minor variable blocks sitting `lo` binders up, then to index terms
`ιs` and a major premise `z`, has type `motive_u ιs z`.

`lo` and the block `Ξ` sitting above the minors are parameters because this is used at two
different depths: the ι-rule's own left-hand side (`Ξ` the field block, `lo = nf`) and each
induction-hypothesis *value* (`Ξ` the field block under a recursive field's `ξ`-telescope,
`lo = nxi + nf`).

The three variable blocks are contiguous in the context -- everything else sits *above*
them -- so a single `appBVars` over `params ++ motives ++ minors` covers all three, and only
the last two arguments need a real `HasArgs`.  The codomain computation is
`recCod_instAll`. -/
theorem recApp_hasType (hI : D.IotaCtx env) {u lo M : Nat} {T' : VIndType}
    (hT' : D.types[u]? = some T') (hu : u < D.nm)
    {Ξ ιs : List VExpr} {z : VExpr} (hΞ : Ξ.length = lo)
    (hlen : ιs.length = T'.indices.length)
    (hidx : env.HasArgs D.recUvars
      (Ξ ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (liftTele (D.nm + D.nmin + lo) (D.atRecTele T'.indices) 0) ιs)
    (hz : env.HasType D.recUvars
      (Ξ ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      z (D.tyApp' u (D.nm + D.nmin + lo) ιs))
    (hM : lo + D.nmin + (D.nm - 1 - u) = M) :
    env.HasType D.recUvars
      (Ξ ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      ((VExpr.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars)).mkApp
        (bvars lo (D.np + D.nm + D.nmin) ++ (ιs ++ [z])))
      ((VExpr.bvar M).mkApp (ιs ++ [z])) := by
  have hR := hI.toRecCtx
  have henv := hR.ordered
  have hmin := VInductDecl'.onCtxMinors hR
  -- the recursor constant, with its telescope split after the minors
  have hrec0 : env.HasType D.recUvars ([] : List VExpr)
      (.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars)) (D.recType u) :=
    VEnv.HasType.const0 (hI.recConsts u T' hT') (VInductDecl'.recType_isType hR hT' hu hmin)
  rw [VInductDecl'.recType, getD_types hT'] at hrec0
  have hrec1 : env.HasType D.recUvars ([] : List VExpr)
      (.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars))
      (mkPi (D.atRecTele D.params ++ D.motives ++ D.minors)
        (mkPi (liftTele (D.nm + D.nmin) (D.atRecTele T'.indices))
          (.forallE (D.tyApp' u (T'.indices.length + D.nmin + D.nm)
              (bvars 0 T'.indices.length))
            ((VExpr.bvar (1 + T'.indices.length + D.nmin + (D.nm - 1 - u))).mkApp
              (bvars 1 T'.indices.length ++ [.bvar 0]))))) := by
    rw [← VExpr.mkPi_append]; exact hrec0
  have hclosed : VExpr.ClosedN
      (VExpr.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars)) 0 := trivial
  have hspine := VEnv.HasType.appBVars henv
    (As := D.atRecTele D.params ++ D.motives ++ D.minors) (Γ := []) (by simpa using hmin) hrec1
  rw [show ((D.atRecTele D.params ++ D.motives ++ D.minors).reverse ++ ([] : List VExpr))
        = D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse from by simp,
    show (D.atRecTele D.params ++ D.motives ++ D.minors).length = D.np + D.nm + D.nmin from by
      simp [VInductDecl'.np]; omega,
    hclosed.liftN_eq (Nat.zero_le _)] at hspine
  -- weaken past `Ξ`, and re-split the telescope after the index block
  have hspine3 : env.HasType D.recUvars
      (Ξ ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      ((VExpr.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars)).mkApp
        (bvars lo (D.np + D.nm + D.nmin)))
      (mkPi (liftTele (D.nm + D.nmin + lo) (D.atRecTele T'.indices) 0
          ++ [(D.tyApp' u (T'.indices.length + D.nmin + D.nm)
                (bvars 0 T'.indices.length)).liftN lo T'.indices.length])
        (((VExpr.bvar (1 + T'.indices.length + D.nmin + (D.nm - 1 - u))).mkApp
            (bvars 1 T'.indices.length ++ [VExpr.bvar 0])).liftN lo
              (T'.indices.length + 1))) := by
    rw [VExpr.mkPi_append]
    have h := hspine.weakN henv (Ctx.LiftN.zero (n := lo) Ξ hΞ)
    rw [VExpr.liftN_mkApp_bvars_lo (Nat.le_refl 0), hclosed.liftN_eq (Nat.zero_le _),
      Nat.add_zero, VExpr.liftN_mkPi, VExpr.length_liftTele,
      VInductDecl'.length_atRecTele, Nat.zero_add, VExpr.liftTele_collapse₂] at h
    exact h
  have hz' : env.HasType D.recUvars
      (Ξ ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)) z
      (VExpr.instAll ((D.tyApp' u (T'.indices.length + D.nmin + D.nm)
        (bvars 0 T'.indices.length)).liftN lo T'.indices.length) ιs 0) := by
    rw [VInductDecl'.tyApp'_instAll' (D := D) (M := D.nm + D.nmin + lo) hlen
      (by omega) (by omega)]
    exact hz
  have hfinal := VEnv.HasType.mkApp' (VEnv.HasArgs.concat hidx hz') hspine3
  rwa [VInductDecl'.recCod_instAll (nf := lo) (M := M) hlen (by omega) (by omega),
    ← VExpr.mkApp_append] at hfinal

theorem iotaCtx_reverse (D : VInductDecl') (C : VIndCtor) :
    (D.iotaCtx C).reverse ++ ([] : List VExpr)
      = (liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse) := by
  simp [VInductDecl'.iotaCtx]

/-- **The ι-rule's induction-hypothesis values.**  The `s`-th ih *value* is `I_{r.idx}.rec`
applied, under the recursive field's own `ξ`-telescope, to the parameters, motives, minors,
the field's index terms and the field applied to its `ξ` variables -- and its type is the
`s`-independent ih type `ihType nmin C i r 0`, which is what `ihType_shift` reduces the
minor's own ih binder to.

`recField_facts` supplies the index arguments and the major premise at `q := nmin, s := 0`;
`recApp_hasType` supplies the recursor spine at depth `nxi + nf`. -/
theorem ihValue_hasType (hI : D.IotaCtx env) {j i : Nat} {T : VIndType} {C : VIndCtor}
    {r : VIndRecArg} {F : VIndField}
    (hT : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hF : C.fields[i]? = some F) (hrec : F.recArg = some r) :
    env.HasType D.recUvars
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (mkLams (shiftTele (D.nm + D.nmin) (C.fields.length - i) i (D.atRecTele r.binders) 0) <|
        (VExpr.const (Lean.mkRecName (D.types.getD r.idx default).name)
            (VLevel.params D.recUvars)).mkApp <|
          bvars (r.binders.length + C.fields.length + (D.nm + D.nmin)) D.np
            ++ bvars (r.binders.length + C.fields.length + D.nmin) D.nm
            ++ bvars (r.binders.length + C.fields.length) D.nmin
            ++ r.args.map (fun a => VExpr.shift (D.nm + D.nmin) (C.fields.length - i) i
                (D.atRec a) r.binders.length)
            ++ [(VExpr.bvar (r.binders.length + (C.fields.length - 1 - i))).mkApp
                (bvars 0 r.binders.length)])
      (D.ihType D.nmin C i r 0) := by
  have hR := hI.toRecCtx
  have henv := hR.ordered
  have hmin := VInductDecl'.onCtxMinors hR
  have hΓι := VInductDecl'.onCtxIota hR hT hC
  obtain ⟨hi, hridx, hargl, hξ, hidxf, hzf⟩ :=
    VInductDecl'.recField_facts (q := D.nmin) (s := 0) (M := D.minors.reverse)
      hR hT hC hF hrec (by simp) hmin (by simp) (by simpa using hΓι)
  obtain ⟨T', hT'⟩ : ∃ T', D.types[r.idx]? = some T' := ⟨_, List.getElem?_eq_getElem hridx⟩
  have hassoc : ((shiftTele (D.nm + D.nmin) (C.fields.length - i + 0) i
          (D.atRecTele r.binders) 0).reverse
        ++ (liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse)
      ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
      = (shiftTele (D.nm + D.nmin) (C.fields.length - i + 0) i (D.atRecTele r.binders) 0).reverse
        ++ (((D.ihTypes D.nmin C).take 0).reverse
          ++ ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
            ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))) := by
    simp
  have hlen : (r.args.map fun a => VExpr.shift (D.nm + D.nmin) (C.fields.length - i + 0) i
      (D.atRec a) r.binders.length).length = T'.indices.length := by
    rw [List.length_map, hargl, getD_types hT']
  have hidx := hidxf T' hT' 0 (D.nm + D.nmin + (r.binders.length + C.fields.length)) (by omega)
  rw [VExpr.liftTele_zero, ← hassoc] at hidx
  have hz := hzf (D.nm + D.nmin + (r.binders.length + C.fields.length)) (by omega)
  rw [← hassoc] at hz
  have hbody := VInductDecl'.recApp_hasType hI hT' hridx
    (Ξ := (shiftTele (D.nm + D.nmin) (C.fields.length - i + 0) i
        (D.atRecTele r.binders) 0).reverse
      ++ (liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse)
    (M := r.binders.length + 0 + C.fields.length + D.nmin + (D.nm - 1 - r.idx))
    (by rw [List.length_append, List.length_reverse, List.length_reverse,
      VExpr.length_shiftTele, VExpr.length_liftTele, VInductDecl'.length_atRecTele,
      VInductDecl'.length_atRecTele, List.length_map])
    hlen hidx hz (by omega)
  rw [hassoc,
    show bvars (r.binders.length + C.fields.length) (D.np + D.nm + D.nmin)
        ++ ((r.args.map fun a => VExpr.shift (D.nm + D.nmin) (C.fields.length - i + 0) i
              (D.atRec a) r.binders.length)
            ++ [(VExpr.bvar (r.binders.length + 0 + (C.fields.length - 1 - i))).mkApp
                (bvars 0 r.binders.length)])
      = bvars (r.binders.length + C.fields.length + (D.nm + D.nmin)) D.np
          ++ bvars (r.binders.length + C.fields.length + D.nmin) D.nm
          ++ bvars (r.binders.length + C.fields.length) D.nmin
          ++ (r.args.map fun a => VExpr.shift (D.nm + D.nmin) (C.fields.length - i + 0) i
              (D.atRec a) r.binders.length)
          ++ [(VExpr.bvar (r.binders.length + 0 + (C.fields.length - 1 - i))).mkApp
              (bvars 0 r.binders.length)] from by
      rw [VExpr.bvars_add₃]; simp [Nat.add_assoc]] at hbody
  rw [getD_types hT']
  exact VEnv.HasType.mkLams (by simpa using hξ) hbody

/-- **E5's right-hand side, before η-expansion.**  `iotaLam` is the minor premise applied to
the field variables and the induction-hypothesis values, abstracted over the ι-rule's whole
binder context.

The field block instantiates by `HasArgs.bvars`; the ih block by `HasArgs.of_lifts`, whose
per-entry obligation is `ihType_shift` (the minor's `s`-th ih binder, moved to the ι-rule's
offsets, is a lift by `s` of an `s`-independent type) together with `ihValue_hasType`.  The
codomain is `minorBody_instAll`. -/
theorem iotaLam_hasType (hI : D.IotaCtx env) {j q : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[j]? = some T) (_hj : j < D.nm) (hC : C ∈ T.ctors)
    (hqC : D.ctorsAll[q]? = some (j, C)) :
    env.HasType D.recUvars [] (D.iotaLam q C) (mkPi (D.iotaCtx C) (D.iotaType j C)) := by
  have hR := hI.toRecCtx
  have henv := hR.ordered
  have hq : q < D.nmin := by
    rcases Nat.lt_or_ge q D.ctorsAll.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hqC; exact absurd hqC (by simp)
  have hΓι := VInductDecl'.onCtxIota hR hT hC
  refine VEnv.HasType.mkLams (Γ := []) (by rw [D.iotaCtx_reverse C]; exact hΓι) ?_
  rw [D.iotaCtx_reverse C]
  -- the minor premise variable, and its type split after the field block
  have hminors : D.minors[q]? = some (D.minorType q j C) := by
    rw [VInductDecl'.minors_getElem?, hqC]; rfl
  have hm : env.HasType D.recUvars
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (.bvar (C.fields.length + (D.nmin - 1 - q)))
      ((D.minorType q j C).liftN (C.fields.length + (D.nmin - 1 - q) + 1)) := by
    refine .bvar ?_
    have h := Lookup.of_reverse hminors
      (liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
      (D.motives.reverse ++ (D.atRecTele D.params).reverse)
    simp only [List.length_reverse, VExpr.length_liftTele, VInductDecl'.length_atRecTele,
      List.length_map, VInductDecl'.length_minors] at h
    simpa using h
  rw [VInductDecl'.minorType, VExpr.liftN_mkPi, VExpr.liftTele_append,
    VExpr.length_liftTele, VInductDecl'.length_atRecTele, List.length_map, Nat.zero_add,
    VExpr.liftTele_collapse₂,
    show D.nm + q + (C.fields.length + (D.nmin - 1 - q) + 1) = D.nm + D.nmin + C.fields.length
      from by omega,
    VInductDecl'.length_ihTypes, List.length_append, VExpr.length_liftTele,
    VInductDecl'.length_atRecTele, List.length_map, VInductDecl'.length_ihTypes] at hm
  -- the field block
  have hfields : env.HasArgs D.recUvars
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (liftTele (D.nm + D.nmin + C.fields.length) (D.atRecTele (C.fields.map (·.type))) 0)
      (bvars 0 C.fields.length) := by
    have h := VEnv.HasArgs.bvars (env := env) (U := D.recUvars) (Δ := [])
      (As := liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0)
      (Γ₀ := D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)
    simp only [List.length_nil, Nat.zero_add, VExpr.length_liftTele,
      VInductDecl'.length_atRecTele, List.length_map, List.nil_append] at h
    rwa [VExpr.liftTele_collapse₂] at h
  -- the induction-hypothesis block
  have hihs : env.HasArgs D.recUvars
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (VExpr.instAllTele
        (liftTele (C.fields.length + (D.nmin - 1 - q) + 1) (D.ihTypes q C) C.fields.length)
        (bvars 0 C.fields.length) 0) (D.ihValues C) := by
    have hcollapse : VExpr.instAllTele
        (liftTele (C.fields.length + (D.nmin - 1 - q) + 1) (D.ihTypes q C) C.fields.length)
        (bvars 0 C.fields.length) 0
        = liftTele (D.nmin - 1 - q + 1) (D.ihTypes q C) C.fields.length := by
      have h := VExpr.instAllTele_liftTele_bvars₂ C.fields.length (D.nmin - 1 - q + 1)
        (D.ihTypes q C) 0
      rw [Nat.zero_add] at h
      rw [show C.fields.length + (D.nmin - 1 - q) + 1
          = D.nmin - 1 - q + 1 + C.fields.length from by omega]
      exact h
    rw [hcollapse]
    refine VEnv.HasArgs.of_lifts (by simp) fun s A b hA hb => ?_
    rw [VInductDecl'.ihValues, List.getElem?_map] at hb
    obtain ⟨⟨i, r⟩, hir, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨F, hF, hrec⟩ := VIndCtor.mem_recFields (List.mem_of_getElem? hir)
    have hi : i < C.fields.length := by
      rcases Nat.lt_or_ge i C.fields.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hF; exact absurd hF (by simp)
    rw [VExpr.getElem?_liftTele, VInductDecl'.ihTypes_getElem?, hir] at hA
    simp only [Option.map_some, Option.some.injEq] at hA
    refine ⟨D.ihType D.nmin C i r 0, ?_, ?_⟩
    · rw [← hA, ← D.ihType_shift (q := q) (R := D.nmin - 1 - q + 1) hi (by omega)]
    · exact VInductDecl'.ihValue_hasType hI hT hC hF hrec
  -- saturate, and compute the codomain
  have hfinal := VEnv.HasType.mkApp' (VEnv.HasArgs.append hfields hihs) hm
  rw [Nat.zero_add] at hfinal
  rwa [D.minorBody_instAll C hq] at hfinal

/-- **E5's left-hand side**: `recApp_hasType` at the ι-rule's own depth, with the index
arguments coming from `VIndCtor.WF.args_ty` and the major premise from
`ctorApp'_hasType`. -/
theorem iotaLhs_hasType (hI : D.IotaCtx env) {j : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[j]? = some T) (hj : j < D.nm) (hC : C ∈ T.ctors)
    (hCall : (j, C) ∈ D.ctorsAll) :
    env.HasType D.recUvars
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (D.iotaLhs j C) (D.iotaType j C) := by
  have hR := hI.toRecCtx
  have henv := hR.ordered
  have hCwf : VIndCtor.WF env D j T C := hR.ctors j T hT C hC
  have hmin := VInductDecl'.onCtxMinors hR
  have hMD : (D.minors.reverse ++ D.motives.reverse).length = D.nm + D.nmin := by
    rw [List.length_append, List.length_reverse, List.length_reverse,
      VInductDecl'.length_minors, VInductDecl'.length_motives]; omega
  have WD : Ctx.LiftN (D.nm + D.nmin) 0 (D.atRecTele D.params).reverse
      (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse) :=
    .zero (D.minors.reverse ++ D.motives.reverse) hMD
  have hacΦ : D.atRecCtx ((C.fields.map (·.type)).reverse ++ D.params.reverse)
      = (D.atRecTele (C.fields.map (·.type))).reverse ++ (D.atRecTele D.params).reverse := by
    rw [VInductDecl'.atRecCtx, List.map_append, List.map_reverse, List.map_reverse]; rfl
  -- the index arguments
  have Wf : Ctx.LiftN (D.nm + D.nmin) C.fields.length
      ((D.atRecTele (C.fields.map (·.type))).reverse ++ (D.atRecTele D.params).reverse)
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse)) := by
    have h := Ctx.LiftN.tele (As := D.atRecTele (C.fields.map (·.type))) WD
    rwa [show (0:Nat) + (D.atRecTele (C.fields.map (·.type))).length = C.fields.length from by
      rw [Nat.zero_add, VInductDecl'.length_atRecTele, List.length_map]] at h
  have hidx : env.HasArgs D.recUvars
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (liftTele (D.nm + D.nmin + C.fields.length) (D.atRecTele T.indices) 0)
      (C.args.map fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length) := by
    have h0 := D.atRec_hasArgs hCwf.args_ty
    rw [hacΦ, VInductDecl'.atRec_liftTele] at h0
    have h := VEnv.HasArgs.weakN henv Wf h0
    rw [VExpr.liftTele_liftTele (Nat.zero_le _) (Nat.le_of_eq (Nat.add_zero _).symm),
      show C.fields.length + (D.nm + D.nmin) = D.nm + D.nmin + C.fields.length from by omega,
      List.map_map] at h
    exact h
  -- the major premise
  have hz : env.HasType D.recUvars
      ((liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse
        ++ (D.minors.reverse ++ D.motives.reverse ++ (D.atRecTele D.params).reverse))
      (D.ctorApp' C (C.fields.length + (D.nm + D.nmin)) (bvars 0 C.fields.length))
      (D.tyApp' j (D.nm + D.nmin + C.fields.length)
        (C.args.map fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length)) := by
    have h := VInductDecl'.ctorApp'_hasType hR hT hC hCall (m := D.nm + D.nmin)
      (Δ := D.minors.reverse ++ D.motives.reverse) hMD hmin
    rwa [VIndCtor.canonResult, D.liftN_atRec_tyApp (Nat.le_refl _) rfl] at h
  have hfinal := VInductDecl'.recApp_hasType hI hT hj
    (Ξ := (liftTele (D.nm + D.nmin) (D.atRecTele (C.fields.map (·.type))) 0).reverse)
    (M := C.fields.length + D.nmin + (D.nm - 1 - j))
    (by rw [List.length_reverse, VExpr.length_liftTele, VInductDecl'.length_atRecTele,
      List.length_map])
    (by rw [List.length_map, hCwf.args_len]) hidx hz rfl
  have hterm : D.iotaLhs j C
      = (VExpr.const (Lean.mkRecName T.name) (VLevel.params D.recUvars)).mkApp
        (bvars C.fields.length (D.np + D.nm + D.nmin)
          ++ ((C.args.map fun a => (D.atRec a).liftN (D.nm + D.nmin) C.fields.length)
            ++ [D.ctorApp' C (C.fields.length + (D.nm + D.nmin)) (bvars 0 C.fields.length)])) := by
    rw [VInductDecl'.iotaLhs, getD_types hT, VExpr.bvars_add₃]
    simp [Nat.add_assoc]
  rw [hterm, VInductDecl'.iotaType]
  exact hfinal

/-- **E5.**  Each ι-rule is a well-formed `VDefEq`: both sides have the rule's own type in
the empty context.  The right-hand side is the η-expansion `λ Γ'. (iotaLam) Γ'`, which is
`appBVars` against the closed `iotaLam`. -/
theorem iotaRule_WF (hI : D.IotaCtx env) {j q : Nat} {T : VIndType} {C : VIndCtor}
    (hT : D.types[j]? = some T) (hj : j < D.nm) (hC : C ∈ T.ctors)
    (hqC : D.ctorsAll[q]? = some (j, C)) : (D.iotaRule j q C).WF env := by
  have hR := hI.toRecCtx
  have henv := hR.ordered
  have hCall : (j, C) ∈ D.ctorsAll := List.mem_of_getElem? hqC
  have hΓι := VInductDecl'.onCtxIota hR hT hC
  have hlam := VInductDecl'.iotaLam_hasType hI hT hj hC hqC
  refine ⟨?_, ?_⟩
  · exact VEnv.HasType.mkLams (Γ := []) (by rw [D.iotaCtx_reverse C]; exact hΓι)
      (by rw [D.iotaCtx_reverse C]; exact VInductDecl'.iotaLhs_hasType hI hT hj hC hCall)
  · refine VEnv.HasType.mkLams (Γ := []) (by rw [D.iotaCtx_reverse C]; exact hΓι) ?_
    have h := VEnv.HasType.appBVars (As := D.iotaCtx C) (Γ := []) henv
      (by rw [D.iotaCtx_reverse C]; exact hΓι) hlam
    rwa [(hlam.closedN henv trivial).liftN_eq (Nat.zero_le _)] at h

theorem iotaRules_WF (hI : D.IotaCtx env) : ∀ df ∈ D.iotaRules, df.WF env := by
  intro df hdf
  simp only [VInductDecl'.iotaRules, List.mem_map] at hdf
  obtain ⟨⟨⟨j, C⟩, q⟩, hjCq, rfl⟩ := hdf
  have hqC : D.ctorsAll[q]? = some (j, C) := List.mk_mem_zipIdx_iff_getElem?.1 hjCq
  obtain ⟨T, hT, hC⟩ := VInductDecl'.mem_ctorsAll (List.mem_of_getElem? hqC)
  have hj : j < D.nm := by
    rcases Nat.lt_or_ge j D.types.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hT; exact absurd hT (by simp)
  exact VInductDecl'.iotaRule_WF hI hT hj hC hqC


end VInductDecl'

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- The major premise's type, once the parameter/motive/minor block and then the index terms
have been substituted: `I_u ps ιs`, with the parameters read straight off the spine. -/
theorem tyApp'_instAll_spine (D : VInductDecl') {u ni : Nat} {ps rest ιs : List VExpr}
    (hps : ps.length = D.np) (hrest : rest.length = D.nm + D.nmin) (hlen : ιs.length = ni) :
    VExpr.instAll
        (VExpr.instAll (D.tyApp' u (ni + D.nmin + D.nm) (bvars 0 ni)) (ps ++ rest) ni) ιs 0
      = (VExpr.const (D.types.getD u default).name D.selfLvls).mkApp (ps ++ ιs) := by
  have hcancel : ∀ x : VExpr, VExpr.instAll (x.liftN ni 0) ιs 0 = x := by
    intro x; rw [← hlen]; exact VExpr.instAll_liftN ιs x 0
  rw [VInductDecl'.tyApp', VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    VExpr.map_instAll_bvars_top (by omega)
      (by rw [List.length_append, hps, hrest]; omega),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add ni)),
    List.take_left' hps, VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    List.map_map, VExpr.map_instAll_bvars' hlen]
  simp only [Function.comp_def, hcancel, List.map_id']

/-- **The recursor applied to a fully concrete spine.**  Unlike `recApp_hasType`, the
parameter, motive and minor blocks are arbitrary well-typed terms rather than variables of
the canonical recursor context, and the result type is *the caller's own motive* applied to
the indices and the major premise.

This is the form a refinement-layer consumer needs, where the motive and minor are terms it
built rather than `bvars`.  What the caller owes:

* `hspine` -- the parameters, motives and minors instantiate the recursor's first three
  blocks.  This is where "this term inhabits the motive's binder type" enters; the spec side
  only says the binder types *are* types (`motiveType_isType`, `minorType_isType`).
* `hidx` -- the index terms, against the index telescope with the spine already substituted.
  For a block with no indices this is `HasArgs Γ [] []`, i.e. `.nil`.
* `he` -- the major premise inhabits `I_u ps ιs`, stated in exactly that form.

The environment interface is `D.IotaCtx env`: `RecCtx` plus the block's recursor constants
at their generated types.  `addInduct'` produces it (`VInductDecl'.WF.iotaCtx`). -/
theorem recApp_hasType' (hI : D.IotaCtx env) {u : Nat} {T' : VIndType}
    (hT' : D.types[u]? = some T') (hu : u < D.nm)
    {Γ ps ms mins ιs : List VExpr} {e mot : VExpr}
    (hps : ps.length = D.np) (hms : ms.length = D.nm) (hmins : mins.length = D.nmin)
    (hspine : env.HasArgs D.recUvars Γ
      (D.atRecTele D.params ++ D.motives ++ D.minors) (ps ++ (ms ++ mins)))
    (hmot : ms[u]? = some mot)
    (hlen : ιs.length = T'.indices.length)
    (hidx : env.HasArgs D.recUvars Γ
      (VExpr.instAllTele (liftTele (D.nm + D.nmin) (D.atRecTele T'.indices))
        (ps ++ (ms ++ mins)) 0) ιs)
    (he : env.HasType D.recUvars Γ e
      ((VExpr.const T'.name D.selfLvls).mkApp (ps ++ ιs))) :
    env.HasType D.recUvars Γ
      ((VExpr.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars)).mkApp
        (ps ++ (ms ++ mins) ++ (ιs ++ [e])))
      (mot.mkApp (ιs ++ [e])) := by
  have hR := hI.toRecCtx
  have henv := hR.ordered
  have hty := VInductDecl'.recType_isType hR hT' hu (VInductDecl'.onCtxMinors hR)
  have hclosed : VExpr.ClosedN (D.recType u) 0 := hty.choose_spec.closedN henv trivial
  -- the recursor constant, in `Γ`
  have hrecΓ : env.HasType D.recUvars Γ
      (.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars)) (D.recType u) := by
    have h := (VEnv.HasType.const0 (hI.recConsts u T' hT') hty).weakN henv
      (by simpa using Ctx.LiftN.zero (n := Γ.length) (Γ := ([] : List VExpr)) Γ rfl)
    rwa [(show VExpr.ClosedN
        (VExpr.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars)) 0 from trivial).liftN_eq
      (Nat.zero_le _), hclosed.liftN_eq (Nat.zero_le _)] at h
  rw [VInductDecl'.recType, getD_types hT'] at hrecΓ
  -- split the telescope after the minors, keeping the major premise in the second block
  have hrec1 : env.HasType D.recUvars Γ
      (.const (Lean.mkRecName T'.name) (VLevel.params D.recUvars))
      (mkPi (D.atRecTele D.params ++ D.motives ++ D.minors)
        (mkPi (liftTele (D.nm + D.nmin) (D.atRecTele T'.indices)
            ++ [D.tyApp' u (T'.indices.length + D.nmin + D.nm) (bvars 0 T'.indices.length)])
          ((VExpr.bvar (1 + T'.indices.length + D.nmin + (D.nm - 1 - u))).mkApp
            (bvars 1 T'.indices.length ++ [VExpr.bvar 0])))) := by
    simp only [VExpr.mkPi_append] at hrecΓ ⊢
    exact hrecΓ
  have h1 := VEnv.HasType.mkApp' hspine hrec1
  rw [VExpr.instAll_mkPi, VExpr.instAllTele_append, VExpr.length_liftTele,
    VInductDecl'.length_atRecTele, Nat.zero_add, List.length_append,
    VExpr.length_liftTele, VInductDecl'.length_atRecTele, List.length_cons,
    List.length_nil] at h1
  -- the major premise, at the substituted domain
  have he' : env.HasType D.recUvars Γ e
      (VExpr.instAll (VExpr.instAll
        (D.tyApp' u (T'.indices.length + D.nmin + D.nm) (bvars 0 T'.indices.length))
        (ps ++ (ms ++ mins)) T'.indices.length) ιs 0) := by
    rw [D.tyApp'_instAll_spine hps (by rw [List.length_append, hms, hmins]) hlen,
      getD_types hT']
    exact he
  have hfinal := VEnv.HasType.mkApp' (VEnv.HasArgs.concat hidx he') h1
  rw [← VExpr.mkApp_append] at hfinal
  -- the codomain: the motive variable resolves to `mot`, and its `ni + 1` lifts cancel
  have hz : (ιs ++ [e]).length = T'.indices.length + 1 := by
    rw [List.length_append, hlen]; rfl
  simp only [Nat.zero_add] at hfinal
  have hget : (ps ++ (ms ++ mins))[D.np + u]? = some mot := by
    rw [List.getElem?_append_right (by omega), hps, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
    exact hmot
  rw [show bvars 1 T'.indices.length ++ [VExpr.bvar 0] = bvars 0 (T'.indices.length + 1) from by
      rw [VExpr.bvars_add (m := T'.indices.length) (n := 1)]; rfl,
    VExpr.instAll_mkApp, VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add _)),
    VExpr.instAll_bvar_get hget
      (by rw [List.length_append, List.length_append, hps, hms, hmins]; omega),
    VExpr.instAll_mkApp, VExpr.map_instAll_bvars' hz, ← hz, VExpr.instAll_liftN] at hfinal
  exact hfinal

end VInductDecl'

/-! ## The keystone

D5 (`onCtxMinors`), D6 (`recType_isType`) and E5 (`iotaRules_WF`) discharge every obligation
of `addInduct'_ordered`. -/

/-- `addIndRecs` produces exactly the `IotaCtx` the ι-rules are checked in. -/
theorem VInductDecl'.WF.iotaCtx {env env₁ env₂ env₃ : VEnv} {D : VInductDecl'}
    (h : D.WF env) (henv : env.Ordered)
    (he₁ : env.addIndTypes D = some env₁) (he₂ : env₁.addIndCtors D = some env₂)
    (he₃ : env₂.addIndRecs D = some env₃) : D.IotaCtx env₃ := by
  have o1 := VInductDecl'.addIndTypes_ordered henv h he₁
  have o2 := VInductDecl'.addIndCtors_ordered o1 h he₁ he₂
  have hR2 : D.RecCtx env₂ := h.recCtx he₁ he₂ VEnv.LE.rfl o2
  have o3 := VInductDecl'.addIndRecs_ordered hR2 (VInductDecl'.onCtxMinors hR2) he₃
  refine ⟨h.recCtx he₁ he₂ (VEnv.addIndRecs_le he₃) o3, fun j T hT => ?_⟩
  exact VEnv.addConstList_constants he₃ (Lean.mkRecName T.name, ⟨D.recUvars, D.recType j⟩)
    (List.mem_map_of_mem (List.mk_mem_zipIdx_iff_getElem?.2 hT))

/-- **`addInduct'` preserves `Ordered`.**  Every obligation is discharged: the three
`addConstList` stages, the type and constructor constants, D6 for the recursors, and E5 for
the ι-rules. -/
theorem VInductDecl'.addInduct'_ordered_final {env env' : VEnv} {D : VInductDecl'}
    (henv : env.Ordered) (h : D.WF env) (he : env.addInduct' D = some env') : env'.Ordered :=
  VInductDecl'.addInduct'_ordered'' henv h
    (fun h1 h2 h3 => VInductDecl'.iotaRules_WF (h.iotaCtx henv h1 h2 h3)) he
