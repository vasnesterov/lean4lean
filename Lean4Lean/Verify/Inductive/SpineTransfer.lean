import Lean4Lean.Verify.Inductive.NestedFreshBridge
import Lean4Lean.Verify.Inductive.Add

/-!
# The spine transfer: `NoConstIn` ⟹ `NoConsts`, and the `Expr` → `VExpr` half

Handoff §59.7 recorded the `Expr` → `VExpr` transfer for the nested *spine* as "the whole of
ruling 116d's general residual", and §59.10 asked for two lemmas that "do not exist":

1. `TrExprS` preserves constant occurrences;
2. `RestoreData`-level agreement between `aux2nested`'s stored args and `as j`.

**Both premises are wrong about what exists, in opposite directions.**

* (1) exists: `TrExprS.noConsts` (`Verify/Inductive/Add.lean`, §"From the syntactic check to
  `VExpr.NoConsts`") is exactly that transfer, by induction on `TrExprS`, with three named
  side conditions (`hctx`, `hlit`, `hproj`) of which two are discharged there.
* (2) is not needed for the stated purpose.  `ElimNestedInductive.Result.RestoreData` **already
  carries a spine clause** — its fourteenth field
  `args : ∀ j, ∀ a ∈ tyArgs j, a.NoConstIn IsNestedName` — and that field is *stronger* than
  `mkRestore_built_of_spine`'s `hspine`, given only that every companion name carries the
  reserved prefix.  §2 below turns `hspine` into a theorem whose one new hypothesis,
  `∀ n ∈ K, n ∈ D.blockNames`, is the hypothesis `hK` already needs
  (`VInductDecl'.fresh_of_addIndTypes`).  So the spine premise costs a caller **nothing** it was
  not already paying.

What is genuinely open is one level down: `RestoreData.args` itself, for an `as` obtained by
translating `aux2nested`'s stored arguments.  That is where (1) and the agreement clause do the
work, and §4 assembles it.

* §1 the `NoConstIn`/`NoConsts` bridge — the two predicates had never been connected.
* §2 `hspine`, discharged from `RestoreData`; `mkRestore_built_of_spine` restated without it.
* §3 the concrete check: last round's `nfnAs_noK` re-derived from `RestoreData.args`, so the
  round-10 spine `decide` is **redundant** at that witness — not eliminated (`args` is itself a
  `decide`), *merged*: two independent `decide`s become the one the bundle always had.
* §4 the `Expr` → `VExpr` transfer at `NoConstIn`, the reserved-prefix predicate as the
  `Expr`-side test, and a producer for `RestoreData.args` from the gate.
* §5 sharpness: `K ⊆ D.blockNames` is **not** removable — a one-datum perturbation at which all
  fourteen `RestoreData` fields hold and the spine premise is false.
* §6 a measurement that refutes something §4's header first asserted: restoration *erases* the
  auxiliary family, so the reserved prefix is an environment invariant after all, and `hproj`
  splits into a half that invariant bounds and a half it does not.
-/

namespace Lean4Lean

open Lean (Name)

/-! ## §1 `NoConstIn` is `NoConsts` at a name barrier containing `K`

`VExpr.NoConsts` (`Theory/Inductive/Decl.lean`:44) is indexed by a `List Name`;
`VExpr.NoConstIn` (`Verify/Inductive/NestedRestore.lean`:65) by a `Name → Prop`.  They are the
same recursion, and no lemma in the repository relates them (measured: `grep -rn` over all of
`Lean4Lean/` for `noConstIn` outside its defining file, and for the two identifiers on one
line — both empty).  That is why ruling 116d's residual looked like a missing bridge when the
bundle that has to supply it already carried a stronger clause. -/

namespace VExpr

/-- `NoConstIn` at a predicate that covers `K` gives `NoConsts K`. -/
theorem noConsts_of_noConstIn {P : Name → Prop} {K : List Name} (hK : ∀ n ∈ K, P n) :
    ∀ {e : VExpr}, e.NoConstIn P → e.NoConsts K
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => fun hc => h (hK c hc)
  | .app .., h | .lam .., h | .forallE .., h =>
    ⟨noConsts_of_noConstIn hK h.1, noConsts_of_noConstIn hK h.2⟩

/-- …and conversely, `NoConsts K` is `NoConstIn` at any predicate `K` covers.  Together with
`noConsts_of_noConstIn` this pins `NoConstIn (· ∈ K) = NoConsts K`. -/
theorem noConstIn_of_noConsts {P : Name → Prop} {K : List Name} (hK : ∀ n, P n → n ∈ K) :
    ∀ {e : VExpr}, e.NoConsts K → e.NoConstIn P
  | .bvar _, _ | .sort _, _ => trivial
  | .const c _, h => fun hc => h (hK c hc)
  | .app .., h | .lam .., h | .forallE .., h =>
    ⟨noConstIn_of_noConsts hK h.1, noConstIn_of_noConsts hK h.2⟩

/-- The two predicates coincide at the membership predicate. -/
theorem noConstIn_mem_iff {K : List Name} {e : VExpr} :
    e.NoConstIn (· ∈ K) ↔ e.NoConsts K :=
  ⟨noConsts_of_noConstIn fun _ h => h, noConstIn_of_noConsts fun _ h => h⟩

end VExpr

/-! ## §2 `hspine` is a theorem, not a residual

`mkRestore_built_of_spine` (`Verify/Inductive/NestedFreshBridge.lean`) takes

    hspine : ∀ j T, D.types[j]? = some T → T.name ∈ K → ∀ a ∈ as j, VExpr.NoConsts K a

and handoff §59.4/§59.7 recorded it as the irreducible per-block `decide`.  It is derivable from
`RestoreData` alone.  The chain is three steps and uses no environment, no `WF` and no
`TrExprS`:

1. `hKB : ∀ n ∈ K, n ∈ D.blockNames` — the hypothesis `VInductDecl'.fresh_of_addIndTypes`
   already needs to produce `hK`;
2. `RestoreData.companions` + `.on` + `.auxName` ⟹ every name of `K` carries the `_nested`
   prefix;
3. `RestoreData.args` ⟹ every `as j` entry is `NoConstIn IsNestedName`, and §1 converts.

Step 2 is `mkRestore_nestedBarrier.auxTy` re-aimed: that clause proves `IsNestedName T.name`
for a *`D`-member* on `K`, and `hKB` is exactly what extends it to all of `K`. -/

namespace ElimNestedInductive.Result.RestoreData

variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr}
  (h : r.RestoreData types D K as)

include h

/-- **Every companion name carries the reserved prefix.**  `mkRestore_nestedBarrier.auxTy`
gives this for a member of `D.types`; `hKB` is what makes it a statement about `K`. -/
theorem isNestedName_of_mem (hKB : ∀ n ∈ K, n ∈ D.blockNames) : ∀ n ∈ K, IsNestedName n := by
  intro n hn
  obtain ⟨T, hTm, rfl⟩ := List.mem_map.1 (hKB n hn)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hTm
  obtain ⟨t, ht, htn, hle⟩ := h.on hj hn
  exact htn ▸ h.auxName j t ht hle

/-- **The spine premise, discharged.**  This is ruling 116d's general residual: it is
`RestoreData`'s own `args` field read through §1's bridge. -/
theorem spine_noConsts (hKB : ∀ n ∈ K, n ∈ D.blockNames) :
    ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K →
      ∀ a ∈ as j, VExpr.NoConsts K a :=
  fun j _ _ _ a ha =>
    VExpr.noConsts_of_noConstIn (h.isNestedName_of_mem hKB) (h.args j a ha)

end ElimNestedInductive.Result.RestoreData

#print axioms Lean4Lean.VExpr.noConsts_of_noConstIn
#print axioms Lean4Lean.VExpr.noConstIn_of_noConsts
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.isNestedName_of_mem
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.spine_noConsts

namespace ElimNestedInductive.Result.RestoreData

variable {r : Result} {types : List Lean.InductiveType} {D : VInductDecl'} {K : List Name}
  {ls : Nat → List VLevel} {as : Nat → List VExpr} {env : VEnv} {occ : Nat → VNestedOcc}
  (h : r.RestoreData types D K as)

include h

/-- **`Built` with the spine premise gone.**  Compare `mkRestore_built_of_spine`: `hspine` is
replaced by `hKB`, which `hK`'s own producer already demands. -/
theorem mkRestore_built_of_blockK (hcc : env.ConstsClosedC) (hnd : D.blockNames.Nodup)
    (hKB : ∀ n ∈ K, n ∈ D.blockNames) (hK : ∀ n ∈ K, ¬ env.contains n)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ) :
    D.Built (r.mkRestore types D.uvars D.np ls as) K env occ :=
  h.mkRestore_built_of_spine hcc hnd hK (h.spine_noConsts hKB) hl ha hres

/-- …and the whole nested step, with **both** `hK` and `hspine` gone: the step's own
`addIndTypes` success supplies the first and `RestoreData` the second, from the single
hypothesis `K ⊆ D.blockNames`. -/
theorem mkRestore_AddNested_of_blockK {env₀ env' : VEnv} (hwf : D.WF env)
    (hcc : env.ConstsClosedC) (hnd : D.blockNames.Nodup)
    (hKB : ∀ n ∈ K, n ∈ D.blockNames) (hty : env.addIndTypes D = some env₀)
    (hl : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → ls j = (occ j).lvls)
    (ha : ∀ (j : Nat) (T : VIndType), D.types[j]? = some T → T.name ∈ K → as j = (occ j).args)
    (hres : r.OccResidue types D K env (r.mkRestore types D.uvars D.np ls as) occ)
    (hadd : env.addInductR D K (r.mkRestore types D.uvars D.np ls as) = some env') :
    VEnv.AddNested env D K (r.mkRestore types D.uvars D.np ls as)
      (fun j => (occ j).decl.np) env' :=
  h.mkRestore_AddNested_of_spine hwf hcc hnd
    (VInductDecl'.fresh_of_addIndTypes hty hKB) (h.spine_noConsts hKB) hl ha hres hadd

end ElimNestedInductive.Result.RestoreData

#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_built_of_blockK
#print axioms Lean4Lean.ElimNestedInductive.Result.RestoreData.mkRestore_AddNested_of_blockK

/-! ## §3 The witness: round 10's spine `decide` is eliminated, not relocated

`NestedWit.nfnAs_noK` (round 10) discharged `hspine` at the `NFn` block by `decide` on the
`VExpr` side.  It is now a corollary of `nfnResult_restoreData`, whose `args` field was already
there and already `decide`d.  Stated precisely — the `decide` is **not** eliminated, the two
`decide`s are merged: at any block that has a `RestoreData` the spine `decide` *is* the `args`
field, and there is only ever one of them.  The four `fields_noK :=` sites in `Theory/` keep
theirs, and structurally must: they are hand-built `VInductDecl'`s with no
`ElimNestedInductive.Result`, and `Theory/` cannot import `Verify/`. -/

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

/-- `nfnK`'s single name is `_nested.PFn_1`, and `K ⊆ D.blockNames` at this block. -/
theorem nfnK_sub_blockNames : ∀ n ∈ nfnK, n ∈ nfnAux.blockNames := by decide

/-- **`nfnAs_noK`, re-derived.**  No `decide` on the spine here: the content is
`nfnResult_restoreData.args`. -/
theorem nfnAs_noK' : ∀ (j : Nat) (T : VIndType), nfnAux.types[j]? = some T → T.name ∈ nfnK →
    ∀ a ∈ nfnAs j, VExpr.NoConsts nfnK a :=
  nfnResult_restoreData.spine_noConsts nfnK_sub_blockNames

section
variable {env₂ : VEnv} (h : VEnv.empty.addInduct' pfnDecl = some env₂)

include h in
/-- **`Built` with no spine hypothesis at all.**  Same conclusion as `nfnAux_built'` and
`nfnAux_built'_of_spine`; what replaces `BuiltFresh` is `env₂.ConstsClosedC` plus
`K ⊆ blockNames`. -/
theorem nfnAux_built'_of_blockK : nfnAux.Built nfnRestore' nfnK env₂ (fun _ => pfnOcc) :=
  nfnResult_restoreData.mkRestore_built_of_blockK (ls := nfnLs) (occ := fun _ => pfnOcc)
    (pfnEnv_constsClosedC h) (by decide) nfnK_sub_blockNames (nfnK_not_contains h)
    (fun _ _ _ _ => rfl)
    (by rintro (_ | _ | j) T hT hK
        · cases hT; exact absurd hK (by decide)
        · rfl
        · simp [nfnAux] at hT)
    (nfnResult_occResidue h)

end
end NestedWit

#print axioms Lean4Lean.NestedWit.nfnAs_noK'
#print axioms Lean4Lean.NestedWit.nfnAux_built'_of_blockK

/-! ## §4 The `Expr` → `VExpr` transfer, at `NoConstIn`

§59.10's item 1 asked for "`TrExprS` preserves constant occurrences", noting "probably already
implied by something in `Verify/Typing/`; I did not look".  It is implied by something in
`Verify/Inductive/`: **`TrExprS.noConsts`** (`Verify/Inductive/Add.lean`, section "From the
syntactic check to `VExpr.NoConsts`"), which is that induction with three named side conditions.
It is stated for `VExpr.NoConsts S` at a `List Name`; `RestoreData.args` wants
`VExpr.NoConstIn IsNestedName`, and `IsNestedName` is not of the form `(· ∈ S)`, so §4.1 reruns
the same induction at a predicate.  The two proofs are line-for-line the same; the duplication
is deliberate, because generalising in place would rebuild `Verify/Inductive/Add.lean` and its
two dependents for no proof-content gain.

The three side conditions fare **better** here than at `D.blockNames`, and this is the one place
where the reserved-prefix barrier is easier than the block-name barrier rather than harder:

* `hctx` — identical, `VLCtx.noConstIn_of_allVLam`;
* `hlit` — **discharged outright, for both literal kinds** (§4.3).  At `D.blockNames` this
  needed `VEnv.HasPrimitives` and did not close string literals in every environment; at
  `IsNestedName` the names a literal expands to are *fixed* (`Nat.zero`, `Nat.succ`,
  `String.ofList`, `List.nil`, `List.cons`, `Char`, `Char.ofNat`) and none carries the prefix,
  so it is a computation plus one list induction, with no environment hypothesis at all;
* `hproj` — **still a hypothesis.**  I first wrote here that it *cannot* be closed by an
  environment invariant, reasoning that nested elimination declares the `_nested.*` auxiliary
  members permanently, so their stored constructor types would put `_nested` names into declared
  types.  **That reasoning is refuted by measurement** — §6 — and the refutation is favourable:
  restoration erases the auxiliary family, so the prefix *is* an environment invariant in
  practice.  What `hproj` needs is therefore split in two, and only the second half is hard:
  the spliced *stored* data (the structure's recursor name and its field types) is bounded by the
  invariant §6 names, `VEnv.NoNestedC`; the spliced `ps`/`ιs` are pinned only up to conversion,
  which is exactly the residual `Verify/Inductive/Add.lean` records — a canonical-spine
  strengthening of `TrProj`, or re-deriving at the whnf'd spine.  Nothing about `IsNestedName`
  shortens *that* half.
-/

open Lean (Expr Literal)

/-! ### §4.1 The induction, at a name predicate -/

namespace VExpr

theorem NoConstIn.liftN {P : Name → Prop} {n : Nat} :
    ∀ {e : VExpr} {k : Nat}, e.NoConstIn P → (e.liftN n k).NoConstIn P
  | .bvar _, _, h | .sort _, _, h | .const .., _, h => h
  | .app .., _, h | .lam .., _, h | .forallE .., _, h => ⟨h.1.liftN, h.2.liftN⟩

end VExpr

/-- `VLCtx.noConsts_cons` at a predicate. -/
theorem VLCtx.noConstIn_cons {P : Name → Prop} {Δ : VLCtx} {ofv} {d : VLocalDecl}
    (hd : VExpr.NoConstIn P d.value)
    (h : ∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConstIn P x) :
    ∀ v x A, VLCtx.find? ((ofv, d) :: Δ) v = some (x, A) → VExpr.NoConstIn P x := by
  intro v x A hv
  rw [VLCtx.find?] at hv
  split at hv
  · cases hv; exact hd
  · rename_i v' _
    cases hf : Δ.find? v' with
    | none => rw [hf] at hv; exact absurd hv nofun
    | some q => rw [hf] at hv; cases hv; exact (h _ _ _ hf).liftN

/-- **`hctx`, discharged** — `VLCtx.noConsts_of_allVLam` at a predicate.  `AllVLam` is the
invariant `AddInductive` maintains (it binds only with `withLocalDecl`). -/
theorem VLCtx.noConstIn_of_allVLam {P : Name → Prop} :
    ∀ {Δ : VLCtx}, Δ.AllVLam → ∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConstIn P x
  | [], _ => by intro _ _ _ h; exact absurd h nofun
  | (_, .vlam _) :: Δ, hΔ => VLCtx.noConstIn_cons trivial (VLCtx.noConstIn_of_allVLam hΔ)

/-- The only case that consumes `hpS`. -/
theorem noConstIn_const {P : Name → Prop} {p : Expr → Bool} {c : Name} {us : List Lean.Level}
    {us' : List VLevel} (hpS : ∀ c us, P c → p (.const c us) = true)
    (h : anySub p (.const c us) = false) : VExpr.NoConstIn P (.const c us') := by
  show ¬ P c
  intro hc
  have h2 := anySub_self h
  rw [hpS c us hc] at h2
  exact absurd h2 nofun

/-- **The transfer, at a name predicate.**  `TrExprS.noConsts` with `NoConsts S` replaced by
`NoConstIn P`; same three side conditions, same proof. -/
theorem TrExprS.noConstIn {env : VEnv} {Us : List Name} {P : Name → Prop} {p : Expr → Bool}
    (hpS : ∀ c us, P c → p (.const c us) = true)
    (hlit : ∀ l : Literal, anySub p l.toConstructor = false)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConstIn P x → VExpr.NoConstIn P y) :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, TrExprS env Us Δ e e' →
      (∀ v x A, Δ.find? v = some (x, A) → VExpr.NoConstIn P x) →
      anySub p e = false → VExpr.NoConstIn P e' := by
  intro Δ e e' H
  induction H with
  | bvar h => exact fun hctx _ => hctx _ _ _ h
  | fvar h => exact fun hctx _ => hctx _ _ _ h
  | sort => exact fun _ _ => trivial
  | const _ _ _ => exact fun _ h => noConstIn_const hpS h
  | app _ _ _ _ ihf iha =>
    intro hctx h
    exact ⟨ihf hctx (anySub_app h).1, iha hctx (anySub_app h).2⟩
  | lam _ _ _ ihd ihb =>
    intro hctx h
    refine ⟨ihd hctx (anySub_lam h).1, ihb ?_ (anySub_lam h).2⟩
    exact VLCtx.noConstIn_cons trivial hctx
  | forallE _ _ _ _ ihd ihb =>
    intro hctx h
    refine ⟨ihd hctx (anySub_forallE h).1, ihb ?_ (anySub_forallE h).2⟩
    exact VLCtx.noConstIn_cons trivial hctx
  | letE _ _ _ _ iht ihv ihb =>
    intro hctx h
    obtain ⟨_, hv, hb⟩ := anySub_letE h
    exact ihb (VLCtx.noConstIn_cons (ihv hctx hv) hctx) hb
  | lit _ _ ih => exact fun hctx _ => ih hctx (hlit _)
  | mdata _ ih => exact fun hctx h => ih hctx (anySub_mdata h)
  | proj _ hp ih => exact fun hctx h => hproj _ _ _ _ _ hp (ih hctx (anySub_proj h))

#print axioms Lean4Lean.VLCtx.noConstIn_of_allVLam
#print axioms Lean4Lean.TrExprS.noConstIn

/-! ### §4.2 The `Expr`-side predicate is the gate's own

`checkNoNestedAux` (`Lean4Lean/Inductive/Add.lean`:1056) scans with exactly the node test below,
and `IsNestedName` (`Verify/Inductive/NestedRestore.lean`:211) is its `.const` arm lifted to
`Prop`.  So `hpS` is *definitional* here — no `hasIndOcc_hpS`-style connector is needed, which is
the one thing that is cheaper about the reserved-prefix barrier than about `D.blockNames`.

Note this is **not** `Result.spineNoAuxB`'s predicate (`Verify/Inductive/NestedFreshBridge.lean`),
which tests `K.contains c`.  The prefix test is the *stronger* of the two whenever every name of
`K` carries the prefix — which §2's `isNestedName_of_mem` proves — so the gate delivers more than
`SpineNoAux` asks for, and it is the prefix form, not the `K` form, that `RestoreData.args`
wants. -/

/-- The reserved-prefix node test, named. -/
def isNestedNode (e : Expr) : Bool :=
  match e with
  | .const c _ => (`_nested).isPrefixOf c
  | .proj s _ _ => (`_nested).isPrefixOf s
  | _ => false

/-- `hpS`, definitionally: `IsNestedName c` *is* `isNestedNode (.const c us) = true`. -/
theorem isNestedNode_hpS (c : Name) (us : List Lean.Level) (h : IsNestedName c) :
    isNestedNode (.const c us) = true := h

/-- **The gate's scan is `anySub isNestedNode`.**  `anySubterm_eq` is what makes the
`replaceNoCacheT`-based implementation a structural predicate. -/
theorem checkNoNestedAux_eq {n : Name} {e : Expr} :
    checkNoNestedAux n e = .ok () ↔ anySub isNestedNode e = false := by
  show (if anySubterm isNestedNode e = true then _ else _) = _ ↔ _
  rw [anySubterm_eq]
  cases anySub isNestedNode e
  · simp; rfl
  · simp

@[local simp] theorem anySub_isNested_const (c : Name) (us : List Lean.Level) :
    anySub isNestedNode (.const c us) = (`_nested).isPrefixOf c := by
  rw [anySub_eq]; simp [isNestedNode]

@[local simp] theorem anySub_isNested_lit (l : Literal) :
    anySub isNestedNode (.lit l) = false := by rw [anySub_eq]; simp [isNestedNode]

@[local simp] theorem anySub_isNested_app (f a : Expr) :
    anySub isNestedNode (.app f a) = (anySub isNestedNode f || anySub isNestedNode a) := by
  rw [anySub_eq]; simp [isNestedNode]

/-! ### §4.3 `hlit`, discharged outright — both literal kinds, no environment hypothesis -/

/-- The seven names a literal can expand into, none of them prefixed. -/
@[local simp] theorem litNames_not_nested :
    (`_nested).isPrefixOf ``Nat.zero = false ∧ (`_nested).isPrefixOf ``Nat.succ = false ∧
    (`_nested).isPrefixOf ``String.ofList = false ∧ (`_nested).isPrefixOf ``List.nil = false ∧
    (`_nested).isPrefixOf ``List.cons = false ∧ (`_nested).isPrefixOf ``Char = false ∧
    (`_nested).isPrefixOf ``Char.ofNat = false := by decide

/-- The `List Char` spine a string literal expands to, parametric in the two constants so the
induction never has to match `strLitToConstructor`'s `let`s. -/
theorem anySub_isNestedNode_strBody {nil cons : Expr}
    (hnil : anySub isNestedNode nil = false) (hcons : anySub isNestedNode cons = false) :
    ∀ l : List Char, anySub isNestedNode (l.foldr
      (fun c e => .app (.app cons (.app (.const ``Char.ofNat []) (.lit (.natVal c.toNat)))) e)
      nil) = false
  | [] => hnil
  | c :: l => by
    rw [List.foldr_cons]
    simp [hcons, anySub_isNestedNode_strBody hnil hcons l, litNames_not_nested]

/-- **`hlit`, discharged.**  At `D.blockNames` this needed `VEnv.HasPrimitives` and closed only
for numerals; at `IsNestedName` the expansion's constants are fixed, so it is a computation plus
one list induction, with no environment hypothesis at all. -/
theorem anySub_isNestedNode_lit : ∀ l : Literal, anySub isNestedNode l.toConstructor = false
  | .natVal 0 => by decide
  | .natVal (n+1) => by
    show anySub isNestedNode (.app (.const ``Nat.succ []) (.lit (.natVal n))) = false
    simp [litNames_not_nested]
  | .strVal s => by
    show anySub isNestedNode (.app (.const ``String.ofList []) _) = false
    simp only [anySub_isNested_app, Bool.or_eq_false_iff, anySub_isNested_const]
    exact ⟨litNames_not_nested.2.2.1,
      anySub_isNestedNode_strBody (by simp [litNames_not_nested]) (by simp [litNames_not_nested])
        s.toList⟩

#print axioms Lean4Lean.checkNoNestedAux_eq
#print axioms Lean4Lean.anySub_isNestedNode_lit

/-! ### §4.4 A gated application's arguments are gated

The stored spine is read off the `Expr` `aux2nested` holds, by `getAppArgs`.  `Verify/Expr.lean`
already reduces that to the structural `getAppArgsRevList`, so the inheritance is one
induction. -/

theorem anySub_getAppArgsRevList {p : Expr → Bool} : ∀ {e : Expr}, anySub p e = false →
    ∀ a ∈ e.getAppArgsRevList, anySub p a = false := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h b hb
    rw [Lean.Expr.getAppArgsRevList, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact (anySub_app h).2
    · exact ihf (anySub_app h).1 b hb
  | _ => intro _ b hb; simp [Lean.Expr.getAppArgsRevList] at hb

theorem anySub_getAppArgs {p : Expr → Bool} {e : Expr} (h : anySub p e = false) :
    ∀ a ∈ e.getAppArgs.toList, anySub p a = false := by
  rw [Lean.Expr.getAppArgs_toList, ← Lean.Expr.getAppArgsRevList_reverse]
  simpa using anySub_getAppArgsRevList h

/-! ### §4.5 `RestoreData.args`, produced

The clause `RestoreData` needs is `∀ j, ∀ a ∈ as j, a.NoConstIn IsNestedName`, and this is the
producer.  Its three hypotheses are, in order: the *agreement* §59.10 asked for (`htr` — the
abstract spine is the translation of the stored one, which is the same shape of obligation as
`TrIndDeclN.trType`/`trCtors`, and the only sensible way to *supply* `as` at all, since there is
no `Lean.Expr → VExpr` function); the gate, on the stored application; and `hproj`, which is
`Verify/Inductive/Add.lean`'s residual and is **not** discharged (see §4's header for why no
environment invariant can discharge it at this predicate).

So the general chain is complete except for `hproj`:

    gate ⟹ (§4.4) spine args prefix-free ⟹ (§4.1) `as j` is `NoConstIn IsNestedName`
         ⟹ `RestoreData.args` ⟹ (§2) `hspine` ⟹ `Built`. -/

namespace ElimNestedInductive.Result

/-- The stored spine at member `j`, on the `Expr` side: the arguments of the nested application
`aux2nested` files under that member's name.  This is `presentedHead`'s sibling — that function
reads the head, this one the arguments. -/
def storedArgs (r : Result) (j : Nat) : List Expr :=
  match r.types[j]? with
  | none => []
  | some t => match r.aux2nested.lookup t.name with
    | some e => e.getAppArgs.toList
    | none => []

/-- The stored applications are prefix-free ⟹ so is every stored spine argument. -/
theorem storedArgs_clean {r : Result}
    (hgate : ∀ (j : Nat) (t : Lean.InductiveType), r.types[j]? = some t →
      ∀ e, r.aux2nested.lookup t.name = some e → anySub isNestedNode e = false) :
    ∀ j, ∀ a ∈ r.storedArgs j, anySub isNestedNode a = false := by
  intro j a ha
  rw [storedArgs] at ha
  split at ha
  · exact absurd ha (by simp)
  · rename_i t ht
    split at ha
    · rename_i e he; exact anySub_getAppArgs (hgate j t ht e he) a ha
    · exact absurd ha (by simp)

/-- The list form of §4.1, for a spine. -/
theorem noConstIn_of_forall₂ {env : VEnv} {Us : List Name} {Δ : VLCtx} {P : Name → Prop}
    {p : Expr → Bool}
    (hpS : ∀ c us, P c → p (.const c us) = true)
    (hlit : ∀ l : Literal, anySub p l.toConstructor = false)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConstIn P x → VExpr.NoConstIn P y)
    (hΔ : Δ.AllVLam) :
    ∀ {l : List Expr} {l' : List VExpr}, List.Forall₂ (TrExprS env Us Δ) l l' →
      (∀ e ∈ l, anySub p e = false) → ∀ a ∈ l', a.NoConstIn P := by
  intro l l' H
  induction H with
  | nil => intro _ a ha; exact absurd ha (by simp)
  | cons ht _ ih =>
    intro hg a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact TrExprS.noConstIn hpS hlit hproj ht (VLCtx.noConstIn_of_allVLam hΔ)
        (hg _ (List.mem_cons_self ..))
    · exact ih (fun e he => hg e (List.mem_cons_of_mem _ he)) a ha

/-- **`RestoreData.args`, produced from the gate plus the agreement clause.** -/
theorem args_of_source {r : Result} {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {as : Nat → List VExpr} (hΔ : Δ.AllVLam)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConstIn IsNestedName x → VExpr.NoConstIn IsNestedName y)
    (hgate : ∀ (j : Nat) (t : Lean.InductiveType), r.types[j]? = some t →
      ∀ e, r.aux2nested.lookup t.name = some e → anySub isNestedNode e = false)
    (htr : ∀ j, List.Forall₂ (TrExprS env Us Δ) (r.storedArgs j) (as j)) :
    ∀ j, ∀ a ∈ as j, a.NoConstIn IsNestedName := fun j =>
  noConstIn_of_forall₂ isNestedNode_hpS anySub_isNestedNode_lit hproj hΔ (htr j)
    (r.storedArgs_clean hgate j)

/-- …and the same with the gate stated as the implementation's own `Except` value. -/
theorem args_of_gate {r : Result} {env : VEnv} {Us : List Name} {Δ : VLCtx} {n : Name}
    {as : Nat → List VExpr} (hΔ : Δ.AllVLam)
    (hproj : ∀ Γ s i x y, TrProj env Us.length Γ s i x y →
      VExpr.NoConstIn IsNestedName x → VExpr.NoConstIn IsNestedName y)
    (hgate : ∀ (j : Nat) (t : Lean.InductiveType), r.types[j]? = some t →
      ∀ e, r.aux2nested.lookup t.name = some e → checkNoNestedAux n e = .ok ())
    (htr : ∀ j, List.Forall₂ (TrExprS env Us Δ) (r.storedArgs j) (as j)) :
    ∀ j, ∀ a ∈ as j, a.NoConstIn IsNestedName :=
  args_of_source hΔ hproj
    (fun j t ht e he => checkNoNestedAux_eq.1 (hgate j t ht e he)) htr

end ElimNestedInductive.Result

#print axioms Lean4Lean.anySub_getAppArgs
#print axioms Lean4Lean.ElimNestedInductive.Result.storedArgs_clean
#print axioms Lean4Lean.ElimNestedInductive.Result.noConstIn_of_forall₂
#print axioms Lean4Lean.ElimNestedInductive.Result.args_of_source
#print axioms Lean4Lean.ElimNestedInductive.Result.args_of_gate

/-! ## §5 `hKB` is necessary: `RestoreData` alone does **not** give the spine premise

§2 replaced `hspine` by `K ⊆ D.blockNames`.  That hypothesis is not slack.  Perturb the witness
by putting one foreign name into both `K` and the spine:

* `nfnKJunk = [`_nested.PFn_1, `Junk]` — a companion name plus a name the block does not declare;
* `nfnAsJunk` presents the companion's parameter spine as `[Junk]` instead of `[NFn]`.

**All fourteen `RestoreData` fields still hold** — `companions` is unharmed because `Junk` is not
any member's name, and `args` is unharmed because `Junk` does not carry the reserved prefix — and
the spine premise is nevertheless **false**.  So `RestoreData` genuinely cannot see this, `hKB` is
load-bearing, and §2 is not smuggling the residual into a vacuous hypothesis.

This is the same shape of lower bound as §2.1 of `Verify/Inductive/NestedRestoreWit.lean`: a
one-datum perturbation at which the whole bundle survives and the consequence fails. -/

namespace NestedWit
open InductiveDeclExamples ElimNestedInductive

/-- A companion name plus one name the block does not declare. -/
def nfnKJunk : List Name := [`_nested.PFn_1, `Junk]

/-- …and the matching spine. -/
def nfnAsJunk : Nat → List VExpr := fun j => if j = 1 then [.const `Junk []] else []

/-- The perturbation satisfies **every** `RestoreData` field. -/
theorem nfnResult_restoreData_junk :
    nfnResult.RestoreData [nfnIndType] nfnAux nfnKJunk nfnAsJunk :=
  { nfnResult_restoreData with
    companions := by
      rintro (_ | _ | j) T hT <;> simp only [nfnAux] at hT <;> [skip; skip; simp at hT] <;>
        cases hT <;> simp [nfnKJunk]
    args := by
      intro j a ha
      simp only [nfnAsJunk] at ha
      split at ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha; decide
      · simp at ha }

/-- …and its `K` is not inside the block. -/
theorem nfnKJunk_not_sub : ¬ (∀ n ∈ nfnKJunk, n ∈ nfnAux.blockNames) := by decide

/-- **The spine premise fails there.**  So `RestoreData.spine_noConsts` cannot drop `hKB`. -/
theorem spine_needs_blockK :
    ¬ (∀ (j : Nat) (T : VIndType), nfnAux.types[j]? = some T → T.name ∈ nfnKJunk →
        ∀ a ∈ nfnAsJunk j, VExpr.NoConsts nfnKJunk a) := by
  intro h
  exact absurd (h 1 _ rfl (by decide) (.const `Junk []) (by decide)) (by decide)

end NestedWit

#print axioms Lean4Lean.NestedWit.nfnResult_restoreData_junk
#print axioms Lean4Lean.NestedWit.spine_needs_blockK

/-! ## §6 Measured: restoration erases the auxiliary family, so the prefix **is** an
environment invariant

§4's header first asserted, from reading, that `_nested.*` auxiliary members are declared
permanently and so the reserved prefix cannot be an environment invariant.  Measured, that is
**false**, and the measurement is worth recording because it moves `hproj`:

* the repository's own environment holds **228114** constants, of which **0** are
  `_nested`-prefixed and **0** have a type mentioning a `_nested`-prefixed constant — and that
  environment imports Lean core, `batteries`, `Foundation` and all of `Lean4Lean`, i.e. a great
  many nested inductives;
* `Lean4Lean.Environment.addInductive` on `inductive TT | mk : List TT → TT` adds exactly
  `TT`, `TT.mk`, `TT.rec`, `TT.rec_1` — the auxiliary member `_nested.List_1` and its
  constructors are **gone**, renamed away by `restoreNested`, and `TT.rec_1` (`auxRecName`) is
  the only trace.  Both counts stay 0.

(The 228114-constant scan is a one-off; the `#eval` below is its cheap, non-vacuous residue —
it asserts the renamed auxiliary recursor exists, so the probe is not silently testing a
non-nested block, and that no auxiliary name survives.)

So the invariant a full `hproj` would rest on is real.  Named here so the next round has a
target; **not proved preserved** — and it cannot be, without the check
`Verify/Inductive/NestedRestore.lean` §8.2 measures to be missing in *both* kernels, since
`inductive _nested.Foo` is accepted and would break it in one step.  That is a second consumer
for the same missing check that `RestoreData.ownName`/`ownCtor` need, which is new information
about that gap: it is not only a name-discipline nicety, it is what would make the prefix
barrier usable inside `TrProj`. -/

namespace VEnv

/-- No declared constant's type mentions a `_nested`-prefixed name.  Measured to hold of the
repository's own environment (228114 constants) and to be preserved by `addInductive` on a
nested block; **not proved**, and not preservable without §8.2's missing check. -/
def NoNestedC (env : VEnv) : Prop :=
  ∀ {n : Name} {ci : VConstant}, env.constants n = some ci → ci.type.NoConstIn IsNestedName

end VEnv

namespace NestedWit

/-- `inductive TT | mk : List TT → TT` — a nested block, accepted. -/
def restoreErasesTypes : List Lean.InductiveType :=
  let T : Lean.Expr := .const `TT []
  [{ name := `TT, type := .sort (.succ .zero),
     ctors := [{ name := `TT.mk,
                 type := .forallE `x (.app (.const ``List [.zero]) T) T .default }] }]

/-! **Self-checking measurement.**  Four assertions: the block is accepted; the renamed
auxiliary recursor `TT.rec_1` exists (so nesting really fired and the probe is not vacuous); no
`_nested.List_i` survives; and none of the four declared constants has a type mentioning a
`_nested` name.  The build fails if any stops holding. -/
#eval show Lean.CoreM Unit from do
  let kenv := (← Lean.getEnv).toKernelEnv
  let .ok env' := Environment.addInductive kenv [] 0 restoreErasesTypes false false
    | throwError "probe void: addInductive rejected `inductive TT | mk : List TT -> TT`"
  unless (env'.find? `TT.rec_1).isSome do
    throwError "probe void: no renamed auxiliary recursor, so no nesting happened"
  for i in [1, 2, 3] do
    let n := (`_nested).str "List" |>.appendIndexAfter i
    if (env'.find? n).isSome then
      throwError "an auxiliary member survived restoration: {n}"
  for n in [`TT, `TT.mk, `TT.rec, `TT.rec_1] do
    let some ci := env'.find? n | throwError "missing {n}"
    if Lean4Lean.anySubterm isNestedNode ci.type then
      throwError "declared constant {n} has a type mentioning a `_nested` name"
  IO.println "measured: a nested declaration leaves no `_nested`-named constant and no \
    `_nested`-mentioning declared type -- restoration erases the auxiliary family ✓"

end NestedWit

end Lean4Lean
