import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Theory.Inductive.StructureEta

open Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

theorem isDefEqLambda.WF {c : VContext} {s : VState}
    {m} [mwf : c.MLCWF m]
    {fvs : List Expr} (hsubst : subst.toList.reverse = fvs)
    (hfvs : ∀ x ∈ fvs, x.looseBVarRange' = 0)
    (he₁ : (c.withMLC m).TrExprS (e₁.instantiateList fvs) ei₁')
    (he₂ : (c.withMLC m).TrExprS (e₂.instantiateList fvs) ei₂') :
    RecM.WF (c.withMLC m) s (isDefEqLambda e₁ e₂ subst) fun b _ =>
      b → (c.withMLC m).IsDefEqU ei₁' ei₂' := by
  unfold isDefEqLambda; let c' := c.withMLC m
  have hrev (e : Expr) : e.instantiate subst.reverse = e.instantiateList fvs := by
    rw [Expr.instantiate_eq _ _ (by simpa [← hsubst] using hfvs)]; simp [hsubst]
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂; (simp [hrev]; exact isDefEq.WF he₁ he₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  simp at he₁ he₂
  let .lam (ty' := t₁') (body' := b₁') ⟨_, a1⟩ a2 a3 := he₁
  let .lam (ty' := t₂') (body' := b₂') b1 b2 b3 := he₂
  suffices ∀ {x s}
      (_ : match x with
        | none => d₁ == d₂
        | some x => x = d₂.instantiateList fvs),
      c'.IsDefEqU t₁' t₂' →
      (F x).WF c' s fun b _ => b → c'.IsDefEqU (t₁'.lam b₁') (t₂'.lam b₂') by
    split <;> rename_i h
    · refine .pureBind <| this ‹_› ?_
      exact a2.eqv (Expr.instantiateList_eqv h) |>.uniq c'.Ewf (.refl c'.Ewf c'.Δwf) b2
    simp [hrev]
    refine (isDefEq.WF a2 b2).bind fun b _ _ h1 => ?_
    split <;> [exact .pure nofun; rename_i h]
    simp at h; exact this rfl (h1 h)
  intros x s hx tt
  have tt' := tt.of_l c'.Ewf c'.Δwf a1
  have ⟨b₁'', a3', eq⟩ := a3.defeqDFC' c'.Ewf <| .cons (.refl c'.Ewf c'.Δwf) (by nofun) (.vlam tt')
  unfold F
  extract_lets d₂'
  have : d₂' = d₂.instantiateList fvs := by
    split at hx <;> [simp [d₂', hrev]; exact hx]
  clear_value d₂'; subst this
  refine .withLocalDecl b2 b1 .rfl fun v mwf' _ _ _ => ?_
  have b3' := b3.inst_fvar c.Ewf mwf'.1.tr.wf
  have a3'' := a3'.inst_fvar c.Ewf mwf'.1.tr.wf
  rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList] at a3'' b3'
  refine isDefEqLambda.WF (mwf := mwf') (fvs := .fvar v :: fvs) (by simp [hsubst])
    (List.forall_mem_cons.2 ⟨rfl, hfvs⟩) a3'' b3'
    |>.mono fun _ _ _ h hb => ?_
  have ⟨_, bb⟩ := eq.symm.trans c'.Ewf mwf'.1.tr.wf.toCtx (h hb)
  exact ⟨_, .symm <| .lamDF tt'.symm <| bb.symm⟩

theorem isDefEqForall.WF {c : VContext} {s : VState}
    {m} [mwf : c.MLCWF m]
    {fvs : List Expr} (hsubst : subst.toList.reverse = fvs)
    (hfvs : ∀ x ∈ fvs, x.looseBVarRange' = 0)
    (he₁ : (c.withMLC m).TrExprS (e₁.instantiateList fvs) ei₁')
    (he₂ : (c.withMLC m).TrExprS (e₂.instantiateList fvs) ei₂') :
    RecM.WF (c.withMLC m) s (isDefEqForall e₁ e₂ subst) fun b _ =>
      b → (c.withMLC m).IsDefEqU ei₁' ei₂' := by
  unfold isDefEqForall; let c' := c.withMLC m
  have hrev (e : Expr) : e.instantiate subst.reverse = e.instantiateList fvs := by
    rw [Expr.instantiate_eq _ _ (by simpa [← hsubst] using hfvs)]; simp [hsubst]
  split <;> [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂; (simp [hrev]; exact isDefEq.WF he₁ he₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  simp at he₁ he₂
  let .forallE (ty' := t₁') (body' := b₁') ⟨_, a1⟩ _ a2 a3 := he₁
  let .forallE (ty' := t₂') (body' := b₂') b1 ⟨_, bT⟩ b2 b3 := he₂
  suffices ∀ {x s}
      (_ : match x with
        | none => d₁ == d₂
        | some x => x = d₂.instantiateList fvs),
      c'.IsDefEqU t₁' t₂' →
      (F x).WF c' s fun b _ => b → c'.IsDefEqU (t₁'.forallE b₁') (t₂'.forallE b₂') by
    split <;> rename_i h
    · refine .pureBind <| this ‹_› ?_
      exact a2.eqv (Expr.instantiateList_eqv h) |>.uniq c'.Ewf (.refl c'.Ewf c'.Δwf) b2
    simp [hrev]
    refine (isDefEq.WF a2 b2).bind fun b _ _ h1 => ?_
    split <;> [exact .pure nofun; rename_i h]
    simp at h; exact this rfl (h1 h)
  intros x s hx tt
  have tt' := tt.of_l c'.Ewf c'.Δwf a1
  have ⟨b₁'', a3', eq⟩ := a3.defeqDFC' c'.Ewf <| .cons (.refl c'.Ewf c'.Δwf) (by nofun) (.vlam tt')
  unfold F
  extract_lets d₂'
  have : d₂' = d₂.instantiateList fvs := by
    split at hx <;> [simp [d₂', hrev]; exact hx]
  clear_value d₂'; subst this
  refine .withLocalDecl b2 b1 .rfl fun v mwf' _ _ _ => ?_
  have b3' := b3.inst_fvar c.Ewf mwf'.1.tr.wf
  have a3'' := a3'.inst_fvar c.Ewf mwf'.1.tr.wf
  rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList] at a3'' b3'
  refine isDefEqForall.WF (mwf := mwf') (fvs := .fvar v :: fvs) (by simp [hsubst])
    (List.forall_mem_cons.2 ⟨rfl, hfvs⟩) a3'' b3'
    |>.mono fun _ _ _ h hb => ?_
  have bb := eq.symm.trans c'.Ewf mwf'.1.tr.wf.toCtx (h hb) |>.of_r c'.Ewf mwf'.1.tr.wf.toCtx bT
  exact ⟨_, .symm <| .forallEDF tt'.symm <| bb.symm⟩

theorem quickIsDefEq.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (quickIsDefEq e₁ e₂ useHash) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold quickIsDefEq
  refine .bind (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h => ?_
  · intro _ mwf wf _ s₁ eq
    simp [modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, StateT.modifyGet,
      pure, Except.pure] at eq
    split at eq; rename_i b _ b' m hm
    change let s' := _; (_, s') = _ at eq; extract_lets s' at eq
    injection eq; subst b' s₁
    let ⟨_, _, a1, a2, ewf, a4⟩ := wf.ectx
    have ⟨ewf, _, h1⟩ := EquivManager.isEquiv.WF ewf hm
    refine let vs' := { s with toState := s' }; ⟨vs', rfl, .rfl, { wf with ectx := ?_ }, ?_⟩
    · exact ⟨_, _, a1, a2, ewf, a4⟩
    · intro h; apply (VEnv.IsDefEqU.weak'_iff c.Ewf a1 a2.toCtx).1
      exact (h1 h).uniq c.Ewf (a2.bvars_eq.trans c.mlctx.noBV)
        a1 (he₁.weakFV' c.Ewf a2 a1) (he₂.weakFV' c.Ewf a2 a1)
  split <;> [exact .pure fun _ => h ‹_›; split]
  · exact .toLBoolM <| c.withMLC_self ▸
      isDefEqLambda.WF (subst := #[]) (fvs := []) rfl nofun
        (c.withMLC_self ▸ he₁) (c.withMLC_self ▸ he₂)
  · exact .toLBoolM <| c.withMLC_self ▸
      isDefEqForall.WF (subst := #[]) (fvs := []) rfl nofun
        (c.withMLC_self ▸ he₁) (c.withMLC_self ▸ he₂)
  · have .sort hu := he₁; have .sort hv := he₂
    refine .pure fun h => ⟨_, .sortDF (.of_ofLevel hu) (.of_ofLevel hv) ?_⟩
    exact Level.isEquiv_wf (toLBool_true.1 h) hu hv
  · let .mdata he₁ := he₁; let .mdata he₂ := he₂
    exact .toLBoolM <| isDefEq.WF he₁ he₂
  · cases he₁
  · rename_i a1 a2 _; refine .pure fun h => ?_
    simp at h; subst h; exact he₁.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂
  · exact .pure nofun

theorem isDefEqArgs.WF {c : VContext} {s : VState}
    (H : ∃ e₁', c.TrExprS e₁.getAppFn e₁' ∧ ∃ e₂', c.TrExprS e₂.getAppFn e₂' ∧ c.IsDefEqU e₁' e₂')
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqArgs e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqArgs; split <;> (unfold Expr.getAppFn at H)
  · let .app a1 a2 a3 a4 := he₁
    let .app b1 b2 b3 b4 := he₂
    refine (isDefEq.WF a4 b4).bind fun _ _ _ h2 => ?_; extract_lets F
    split <;> [exact .pure nofun; rename_i hb2]
    refine (isDefEqArgs.WF H a3 b3).mono fun _ _ _ h1 hb1 => ?_
    simp at hb2
    exact ⟨_, .appDF ((h1 hb1).of_l c.Ewf c.Δwf a1) ((h2 hb2).of_l c.Ewf c.Δwf a2)⟩
  · exact .pure nofun
  · exact .pure nofun
  · refine .pure fun _ => ?_
    simp [*] at H; let ⟨_, h1, _, h2, h3⟩ := H
    have a1 := he₁.uniq c.Ewf (.refl c.Ewf c.Δwf) h1
    have a2 := he₂.uniq c.Ewf (.refl c.Ewf c.Δwf) h2
    exact a1.trans c.Ewf c.Δwf h3 |>.trans c.Ewf c.Δwf a2.symm

theorem tryEtaExpansionCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaExpansionCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold tryEtaExpansionCore; split <;> [skip; exact .pure nofun]
  refine (inferType.WF he₂).bind fun _ _ _ ⟨ty₁, a1, a2, a3, a4⟩ => ?_
  refine (whnf.WF a3).bind fun _ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [skip; exact .pure nofun]
  let .forallE (ty' := ty') c1 c2 c3 c4 := b2
  replace a4 := a4.defeqU_r c.Ewf c.Δwf b3.symm
  -- have := b2.uniq c.Ewf (.refl c.Ewf c.Δwf) (.forallE c1 c2 c3 c4)
  refine (isDefEq.WF he₁ (.lam c1 c3 (.app (a4.weak c.Ewf) (.bvar .zero) (
    Expr.liftLooseBVars_eq_self (c.mlctx.noBV ▸ a2.closed).looseBVarRange_le ▸
      a2.weakBV c.Ewf (.skip (.vlam ty') .refl)) (.bvar rfl)))).mono fun _ _ _ h hb => ?_
  exact (h hb).trans c.Ewf c.Δwf ⟨_, .eta a4⟩

theorem tryEtaExpansion.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaExpansion e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  simp [tryEtaExpansion, orM, toBool]
  refine (tryEtaExpansionCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h rfl; skip]
  exact (tryEtaExpansionCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

/-- **Vacuity witness for `tryEtaStructCore.WF`.  Read this before proving that theorem.**

`tryEtaStructCore` provably never returns `true` today, and this is the machine-checked
statement of that.  Its second step is `let .ctorInfo fInfo ← env.get f | return false` on the
head constant of `s`; `s` is translated, so its head is named in the `VEnv`, and
`TrEnv.not_ctorInfo` (`Verify/TypeChecker/Reduce.lean`) then forbids the constant map from
holding a `.ctorInfo` under that name.

**Note what this statement does not mention: `e₁` plays no role at all.**  That is the
signature of vacuity — `tryEtaStructCore.WF`'s conclusion `c.IsDefEqU e₁' e₂'` would be
derived without any hypothesis relating `e₁` to `e₁'`, i.e. for a completely arbitrary `e₁'`.
A "proof" of `tryEtaStructCore.WF` via this route establishes no relation between the two
terms; it only re-states that the branch is dead.

**Why it is dead, and when it stops being.**  `not_ctorInfo` holds only because `AddInduct`
(`Verify/Environment/Basic.lean`) has no constructors, so `TrEnv'.induct` cannot fire and
`TrEnv'.find?_shape` lists only the five non-inductive shapes.  The moment `AddInduct` becomes
`AddInductStages` — complete, proved, and witnessed by `R10.Wit` in that same file —
`find?_shape` gains `.inductInfo`/`.ctorInfo`/`.recInfo` and all three `not_*Info` lemmas
become **false**.  This theorem then goes red, which is exactly why it is kept live: it is the
marker that `tryEtaStructCore.WF` has no content yet, and it fails loudly rather than
silently.

The real proof needs `structEta`, a `VEnv.IsDefEq` constructor the abstract spec does not have
(`docs/design-inductive.md:724-765`, `docs/research-structeta.md`), plus `TrProj`
functionality. -/
theorem tryEtaStructCore_never_true {c : VContext} {s : VState} (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b = false := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold tryEtaStructCore
  obtain ⟨f', hf⟩ := head_tr he₂
  split <;> [skip; exact .pure rfl]
  rename_i f us heq
  rw [heq] at hf
  let .const hc _ _ := hf
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
  cases ci <;> first
    | exact absurd hci fun hh => c.trenv.not_ctorInfo ⟨_, hc⟩ hh
    | exact .pure rfl

/-- **Loop rule with `break`.**  `M.WF.forIn` (`Verify/TypeChecker.lean`) requires the body to
`yield` on every iteration, which none of `tryEtaStructCore`'s, `isDefEqApp`'s or
`isDefEqArgs`' loops do — they `return false` on the first failure.  This is the
early-exit version, for `forIn'` (the body takes the membership proof, which the
`args[i]` access needs) and in `RecM` rather than `M`.

The invariant is *not* indexed by the remaining list, because a `break` skips the rest: what
it records is the state discipline, which is what `RecM.WF` demands beyond the postcondition
and which is what the loop obligation actually is.  Instantiate `Inv` at `fun _ _ => True`
when the postcondition is already in hand. -/
theorem RecM.WF.forIn'Break {c : VContext} {Inv : β → VState → Prop} :
    ∀ {xs : List α} {f : (a : α) → a ∈ xs → β → RecM (ForInStep β)},
    (∀ v (h : v ∈ xs) b s, Inv b s → RecM.WF c s (f v h b) fun r s' => Inv r.value s') →
    ∀ {b : β} {s : VState}, Inv b s →
      RecM.WF c s (forIn' xs b f) fun b' s' => Inv b' s'
  | [], _, _, _, _, h => .pure h
  | v :: vs, f, H, b, s, h => by
    rw [List.forIn'_cons]
    refine (H v (.head _) b s h).bind fun r s' _ hr => ?_
    match r with
    | .done b' => exact .pure hr
    | .yield b' => exact RecM.WF.forIn'Break (fun v hv b s hb => H v (.tail _ hv) b s hb) hr

/-- **`forIn'Break` with the invariant indexed by the prefix already processed.**

`forIn'Break` deliberately does not index its invariant, which is exactly what makes it unable
to accumulate anything across iterations: a `break` skips the rest of the list, so a
non-indexed invariant cannot say "and every element so far satisfied `P`".  This version can.
It splits the body's obligation in two — a `yield` must extend the invariant by the element
just processed, a `done` must land in a separate break predicate `Br` — and concludes with the
disjunction: either the whole list was traversed and `Inv` holds at it, or the loop broke and
`Br` holds.

This is the lemma `docs/handoff-eta.md` §4 named as missing for the non-`Prop` half of
`tryEtaStructCore.WF`.  Like `forIn'Break` it is reusable: `isDefEqApp`'s and `isDefEqArgs`'
loops have the same shape. -/
theorem RecM.WF.forIn'Prefix {c : VContext} {Inv : List α → β → VState → Prop}
    {Br : β → VState → Prop} :
    ∀ {xs : List α} {f : (a : α) → a ∈ xs → β → RecM (ForInStep β)} {pre : List α},
    (∀ (ys : List α) (v : α) (h : v ∈ xs) (b : β) (s : VState), Inv ys b s →
      RecM.WF c s (f v h b) fun r s' =>
        match r with
        | .yield b' => Inv (ys ++ [v]) b' s'
        | .done b' => Br b' s') →
    ∀ {b : β} {s : VState}, Inv pre b s →
      RecM.WF c s (forIn' xs b f) fun b' s' => Inv (pre ++ xs) b' s' ∨ Br b' s'
  | [], _, pre, _, _, _, h => .pure (.inl (by simpa using h))
  | v :: vs, f, pre, H, b, s, h => by
    rw [List.forIn'_cons]
    refine (H pre v (.head _) b s h).bind fun r s' _ hr => ?_
    match r with
    | .done b' => exact .pure (.inr hr)
    | .yield b' =>
      refine (RecM.WF.forIn'Prefix (pre := pre ++ [v])
        (fun ys w hw bb ss hbb => H ys w (.tail _ hw) bb ss hbb) hr).mono ?_
      intro _ _ _ hh
      simpa using hh

/-- **The `IsStructure` bridge, at `tryEtaStructCore`'s gate**, in the form its loop consumes.

`docs/handoff-eta.md` §5 recorded the residual as "supply `c.venv.IsStructure I D T C` from
`c.env.isNonRecStructure I = true`", on the grounds that `TrProj.mk` opens with `IsStructure`.
That is right about *why* the loop stops but **understates what it needs**: the loop's first
argument is `.proj I (i - np) t`, whose translation is a `TrProj` (hence `IsStructure` plus the
whole `TrProj.mk` premise list), and its *second* argument is `s.getAppArgs[i]`, whose
translation has to be read off `he₂`'s spine.  Both are needed before `isDefEq.WF` fires, so
the residual is two translations per iteration, not one `IsStructure`.

Stating it as "the two translations exist" rather than as `IsStructure` keeps the hypothesis at
exactly what is consumed and leaves the `TrProj` construction — `Verify/Typing/ProjWfWitness.lean`
has a worked sorry-free example — on the supplying side.

Every binder is pinned by a gate: `f` and `w` by the head equation and the lookup, and the
`i` clause fires only under the arity and `isNonRecStructure` checks the function performs. -/
def EtaStructBridge (c : VContext) (t s : Expr) : Prop :=
  ∀ {f : Name} {w : ConstructorVal},
    (∃ us, s.getAppFn = .const f us) →
    c.env.find? f = some (.ctorInfo w) →
    (s.getAppNumArgs == w.numParams + w.numFields) = true →
    c.env.isNonRecStructure w.induct = true →
    ∀ i (h : i < s.getAppArgs.size),
      (∃ p', c.TrExprS (.proj w.induct (i - w.numParams) t) p') ∧
      (∃ q', c.TrExprS s.getAppArgs[i] q')

/-- **The `Prop` half of `tryEtaStructCore.WF`, discharged** — the counterpart of
`isDefEqUnitLike.WF_prop`, and the theorem `docs/handoff-eta.md` §5 reported as stopping at the
loop.

It no longer stops.  The four gates split cleanly, both `inferType.WF`s and `isDefEq.WF` fire,
`proofIrrel` yields `key : c.IsDefEqU e₁' e₂'` before the loop, and the loop itself — whose
obligation is *state* well-formedness, not the postcondition — goes through by
`Std.Legacy.Range.forIn'_eq_forIn'_range'` followed by `RecM.WF.forIn'Break`, with the body
discharged from `EtaStructBridge`.

**What is assumed and what is not.**  `EtaStructBridge` is the only hypothesis beyond `hprop`;
in particular **no** structure-eta rule is used — in the `Prop` case `proofIrrel` settles the
conclusion outright, exactly as it does for `isDefEqUnitLike`.  Like `WF_prop` there, this
proof enters the real `.ctorInfo` arm and never mentions `AddInduct` or `TrEnv.not_ctorInfo`, so
it survives the flip verbatim.

**The non-`Prop` case is no longer open**: `WF_of_structEta` below does it, with a
prefix-indexed loop rule (`RecM.WF.forIn'Prefix`), the decomposition of `e₂'` supplied by the
strengthened bridge `EtaStructSpine`, and `VEnv.StructEta.congrProj` for the assembly.  This
lemma is kept because its hypothesis list is strictly weaker on the block side — it needs no
`IsStructure` at all — so it is the one to use wherever `hprop` is available.

**Honest note on today's satisfiability.**  `EtaStructBridge c e₁ e₂` is *currently* provable
for every `c`, because its premise asks for a `.ctorInfo` under the head of a translated term
and `TrEnv.not_ctorInfo` forbids that — the same wall as everything else in this corner.  So
this theorem is instantiable today, but the instantiation is empty; what it buys is that the
proof of the conclusion is built from `proofIrrel` and the loop rule rather than from the
vacuity, so it keeps working when the bridge stops being free. -/
theorem tryEtaStructCore.WF_prop {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hprop : ∀ A, c.HasType e₁' A → c.HasType A (.sort .zero))
    (hbr : EtaStructBridge c e₁ e₂) :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold tryEtaStructCore
  split <;> [skip; exact .pure nofun]
  rename_i f us heq
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
  split <;> [skip; exact .pure nofun]
  rename_i fInfo hfi
  split <;> [skip; exact .pure nofun]
  rename_i hnum
  split <;> [skip; exact .pure nofun]
  rename_i hnrs
  refine (inferType.WF he₁).bind fun _ _ _ ⟨_, _, _, ht1, hT1⟩ => ?_
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, _, _, ht2, hT2⟩ => ?_
  refine (isDefEq.WF ht1 ht2).bind fun b _ _ hb => ?_
  split <;> [skip; exact .pure nofun]
  have key : c.IsDefEqU e₁' e₂' :=
    ⟨_, .proofIrrel (hprop _ hT1) hT1 (hT2.defeqU_r c.Ewf c.Δwf (hb ‹_›).symm)⟩
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine (RecM.WF.forIn'Break (Inv := fun _ _ => True) ?_ trivial).bind fun r _ _ _ => ?_
  · intro i hi bb ss _
    have hlt : i < e₂.getAppArgs.size := by
      simp [List.mem_range'] at hi
      omega
    obtain ⟨⟨p', hp⟩, ⟨q', hq⟩⟩ := hbr ⟨us, heq⟩ hci hnum hnrs i hlt
    refine (isDefEq.WF hp hq).bind fun r _ _ _ => ?_
    split <;> exact .pure trivial
  · split <;> exact .pure fun _ => key

/-- **The bridge at `tryEtaStructCore`'s gate, in the form the *non*-`Prop` proof consumes.**

`EtaStructBridge` above is what the `Prop` half needs: two translations per iteration and
nothing else, because `proofIrrel` settles the conclusion before the loop runs.  Outside `Prop`
the loop's output is the whole content, so the bridge has to say *which* abstract terms the two
translations land on, and hand over the block data the assembly needs:

* the block itself — `IsStructure` plus the eta rule's side conditions (`T.indices = []`, the
  level and parameter data, `t' : S ps`, and F17);
* the **decomposition of the second term**, `s' = C.mk us (ps ++ args)`, which is what
  `docs/handoff-eta.md` §4 listed as the second missing ingredient;
* the constructor's declared telescope, split at the parameter/field boundary (`hctor`), and
  its result (`hB`);
* and, per iteration, the two translations *pinned*: the first argument translates to
  `D.projTerm … (i - np) t'` — the term `TrProj` produces — and the second to `args[i - np]`.

**What is deliberately *not* here: the projections' typing.**  An earlier draft carried
`∀ k < n, HasType (projTerm … k t') …` as a further conjunct.  It is not needed:
`projTerm_hasType` (`Verify/Typing/Lemmas.lean`) derives it from `IsStructure`, the universe
data and the F17 clause — all of which are already listed — and `WF_of_structEta` below does
exactly that.  The F17 clause is what pays for it, in both of `TrProj.wf`'s branches.

Every binder is pinned by a gate: `f` and `w` by the head equation and the lookup, and the
per-iteration clause fires only under the arity and `isNonRecStructure` checks.

**Satisfiability today: empty, and that is unchanged.**  Like `EtaStructBridge`, this predicate
is currently provable for every `c` — its premise asks for a `.ctorInfo` under the head of a
translated term and `TrEnv.not_ctorInfo` forbids that.  What the theorem below buys is that its
conclusion comes from `StructEta.congrProj` and the loop rule, not from that vacuity. -/
def EtaStructSpine (c : VContext) (t s : Expr) (t' s' : VExpr) : Prop :=
  ∀ {f : Name} {w : ConstructorVal},
    (∃ us, s.getAppFn = .const f us) →
    c.env.find? f = some (.ctorInfo w) →
    (s.getAppNumArgs == w.numParams + w.numFields) = true →
    c.env.isNonRecStructure w.induct = true →
    ∃ (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
      (ps args : List VExpr) (B : VExpr),
      c.venv.IsStructure w.induct D T C ∧ C.name = f ∧ T.indices = [] ∧
      us.length = D.uvars ∧ (∀ l ∈ us, l.WF c.lparams.length) ∧ ps.length = D.np ∧
      w.numParams = D.np ∧ C.fields.length = w.numFields ∧
      args.length = C.fields.length ∧
      c.venv.HasArgs c.lparams.length c.vlctx.toCtx (D.params.map (VExpr.instL us)) ps ∧
      c.venv.HasType c.lparams.length c.vlctx.toCtx t'
        ((VExpr.const w.induct us).mkApp ps) ∧
      (D.isLE = true ∨ ∀ k, k < C.fields.length →
        (C.fields.getD k default).lvl.inst us ≈ .zero) ∧
      s' = (VExpr.const C.name us).mkApp (ps ++ args) ∧
      c.venv.HasType c.lparams.length c.vlctx.toCtx (VExpr.const C.name us)
        (VExpr.mkPi (D.params.map (VExpr.instL us) ++
          C.fields.map (fun F => VExpr.instL us F.type)) B) ∧
      VExpr.instAll B (ps ++ D.projAll T C us ps t') = (VExpr.const w.induct us).mkApp ps ∧
      (∀ i (h : i < s.getAppArgs.size), w.numParams ≤ i →
        c.TrExprS (.proj w.induct (i - w.numParams) t)
          (D.projTerm T C us ps [] (i - w.numParams) t') ∧
        c.TrExprS s.getAppArgs[i] (args.getD (i - w.numParams) default))

/-- **`tryEtaStructCore.WF`, modulo structure eta and the bridge — the whole statement, `Prop`
case included.**

`WF_prop` above is the `Prop` column.  This is both columns, and it is the theorem
`docs/handoff-eta.md` §4 left open with its failing step named.  All three named ingredients
are now here:

1. **the prefix-indexed loop rule** (`RecM.WF.forIn'Prefix`), which did not exist — the loop's
   per-iteration `IsDefEqU (proj_k t') args_k` is carried in the invariant instead of being
   discarded, and a `break` is absorbed by the separate break predicate;
2. **the decomposition of `e₂'`** as `(.const C.name us).mkApp (ps ++ args)`, which the bridge
   supplies rather than the proof recovering it by `AppStack` inversion;
3. **`VEnv.StructEta.congrProj`** (`Theory/Inductive/StructureEta.lean`), which assembles the
   per-field comparisons into a `HasArgsDF` over the constructor's field telescope and closes
   with `congrSpine`.

**The projections' typing is derived here, not assumed.**  `projTerm_hasType`
(`Verify/Typing/Lemmas.lean`) turns the bridge's `IsStructure` + universe data + F17 clause into
`ProjHasType` at every field, with the same two-branch level argument `TrProj.wf` uses.  So the
one heavy typing fact in `congrProj`'s premise list costs nothing extra at this call site.

Like `WF_prop`, the proof **enters the live `.ctorInfo` arm** — it never touches
`TrEnv.not_ctorInfo` — so it survives the `AddInduct` flip verbatim.  And like `WF_prop`, its
hypothesis is empty *today*, for the reason `EtaStructSpine`'s docstring records; the
instantiation is what is missing, not the derivation. -/
theorem tryEtaStructCore.WF_of_structEta {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hSE : c.venv.StructEta) (hbr : EtaStructSpine c e₁ e₂ e₁' e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold tryEtaStructCore
  split <;> [skip; exact .pure nofun]
  rename_i f us heq
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
  split <;> [skip; exact .pure nofun]
  rename_i fInfo hfi
  split <;> [skip; exact .pure nofun]
  rename_i hnum
  split <;> [skip; exact .pure nofun]
  rename_i hnrs
  obtain ⟨D, T, C, us', ps, args, B, hIS, hCname, hidx, hus, huswf, hps, hnp, hnf, hargl,
    hpsA, hty1, hF17, he₂eq, hctor, hB, hiter⟩ := hbr ⟨us, heq⟩ hci hnum hnrs
  -- the projections' typing, derived from the block data and F17 (`TrProj.wf`'s argument)
  have hprojty : ∀ k, k < C.fields.length →
      c.venv.HasType c.lparams.length c.vlctx.toCtx (D.projTerm T C us' ps [] k e₁')
        (VExpr.instAll ((C.fields.getD k default).type.instL us')
          (ps ++ (List.range k).map fun m => D.projTerm T C us' ps [] m e₁')) := by
    intro k hk
    refine projTerm_hasType c.Ewf hIS hus huswf k hk ?_ c.Δwf ?_ hps ?_ hpsA ?_
    · intro m _ _
      by_cases hLE : D.isLE = true
      · simp only [VInductDecl'.elimLvl, VInductDecl'.projLvls, hLE, if_true, VLevel.inst,
          List.getD_cons_zero]
        rfl
      · simp only [Bool.not_eq_true] at hLE
        rw [VInductDecl'.elimLvl, VInductDecl'.projLvls, if_neg (by simp [hLE]),
          if_neg (by simp [hLE])]
        rcases hF17 with h | h
        · exact absurd h (by simp [hLE])
        · exact h m (by omega)
    · simpa using hty1
    · simp [hidx]
    · simp [hidx]; exact .nil
  refine (inferType.WF he₁).bind fun _ _ _ ⟨_, _, _, ht1, _⟩ => ?_
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, _, _, ht2, _⟩ => ?_
  refine (isDefEq.WF ht1 ht2).bind fun b _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine (RecM.WF.forIn'Prefix
    (Inv := fun ys st _ => st.1 = none ∧ ∀ a ∈ ys,
      c.IsDefEqU (D.projTerm T C us' ps [] (a - hfi.numParams) e₁')
        (args.getD (a - hfi.numParams) default))
    (Br := fun st _ => st.1 = some false)
    (pre := []) ?_ ⟨rfl, nofun⟩).bind fun r _ _ hr => ?_
  · intro ys a ha bb ss ⟨_, hb2⟩
    have hlt : a < e₂.getAppArgs.size := by simp [List.mem_range'] at ha; omega
    have hge : hfi.numParams ≤ a := by simp [List.mem_range'] at ha; omega
    obtain ⟨hp, hq⟩ := hiter a hlt hge
    refine (isDefEq.WF hp hq).bind fun _ _ _ hres => ?_
    split
    · rename_i hrt
      refine .pure ⟨rfl, ?_⟩
      intro x hx
      simp at hx
      rcases hx with hx | rfl
      · exact hb2 x hx
      · exact hres hrt
    · exact .pure rfl
  · rcases hr with ⟨h1, h2⟩ | h1
    · rw [h1]
      refine .pure fun _ => ?_
      have hkey : ∀ k, k < C.fields.length →
          c.IsDefEqU (D.projTerm T C us' ps [] k e₁') (args.getD k default) := by
        intro k hk
        have hmem : hfi.numParams + k ∈
            [] ++ List.range' hfi.numParams [hfi.numParams:e₂.getAppArgs.size].size := by
          simp [List.mem_range']
          have hsz : e₂.getAppArgs.size = hfi.numParams + hfi.numFields := by
            have h0 : e₂.getAppArgs.toList.length = e₂.getAppNumArgs := by
              rw [Expr.getAppArgs_toList_rev, List.length_reverse, ← Expr.getAppNumArgs_eq]
            simp only [Array.length_toList] at h0
            rw [h0]; simpa using hnum
          omega
        simpa using h2 _ hmem
      exact ⟨_, he₂eq ▸ hSE.congrProj hIS hidx hus huswf hps hpsA hty1 hF17 hargl
        hprojty hkey hctor hB c.Ewf c.Δwf⟩
    · rw [h1]; exact .pure nofun

/-- Still `sorry`, deliberately.  `(tryEtaStructCore_never_true he₂).mono
fun _ _ _ h hb => absurd (h ▸ hb) nofun` discharges it in one line — but that close is
vacuous, is discarded the moment `AddInduct` gains constructors, and would make the
refinement layer read as complete on structure-eta when it has no content on it at all.

`WF_of_structEta` above is the non-vacuous version: **this statement is exactly that one with
its two hypotheses removed**, and neither is provable in this tree.  `c.venv.StructEta` is an
addition to the abstract theory (`Theory/Inductive/StructureEta.lean` says why it is a
predicate rather than an `IsDefEq` constructor); `EtaStructSpine` needs the `IsStructure`
bridge, which `Verify/StructureBridge.lean` shows is not attainable as `IsStructure` currently
stands — and, since Lean's kernel performs structure eta on members of *mutual* non-recursive
blocks (`MutNonRec.kernelProjChecks`), not attainable by weakening `IsStructure.types` either.

See `tryEtaStructCore_never_true` for the vacuity argument.

**Status 2026-08-31 (checked, not attempted).**  Re-verified against the source rather than
taken from the note above: `WF_of_structEta` and `WF_prop` are both `sorry`-free (census: the
only hole in this file's eta section is this theorem and `isDefEqUnitLike.WF`), so the residual
really is exactly the two hypotheses.  Of those, `EtaStructSpine`'s missing ingredient is the
strengthening of `VEnv.IsStructure`'s `decl` field, which is being worked in
`Theory/Inductive/Structure.lean` and `Verify/Typing/Lemmas.lean`; this round did not touch it
(scope boundary), and there is nothing else on the `Verify` side to do here first. -/
theorem tryEtaStructCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := sorry

theorem tryEtaStruct.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStruct e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  simp [tryEtaStruct, orM, toBool]
  refine (tryEtaStructCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h rfl; skip]
  exact (tryEtaStructCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

theorem isDefEqApp.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqApp e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqApp; split <;> [skip; exact .pure nofun]
  rw [Expr.withApp_eq, Expr.withApp_eq]
  split <;> [rename_i eq; exact .pure nofun]
  have ⟨_, he₁'⟩ := AppStack.build <| e₁.mkAppList_getAppArgsList ▸ he₁
  have ⟨_, he₂'⟩ := AppStack.build <| e₂.mkAppList_getAppArgsList ▸ he₂
  refine (isDefEq.WF he₁'.tr he₂'.tr).bind fun _ _ _ h => ?_
  split <;> [skip; exact .pure nofun]
  let rec loop.WF {s args₁ args₂ f₁ f₂ f₁' f₂' eq i} (l₁ r₁ l₂ r₂)
      (h₁ : args₁.toList = l₁ ++ r₁) (hi₁ : l₁.length = i)
      (h₂ : args₂.toList = l₂ ++ r₂) (hi₂ : l₂.length = i)
      (he₁ : AppStack c.venv c.lparams c.vlctx (.mkAppList f₁ l₁) f₁' r₁)
      (he₂ : AppStack c.venv c.lparams c.vlctx (.mkAppList f₂ l₂) f₂' r₂)
      (H1 : c.IsDefEqU f₁' f₂') :
      RecM.WF c s (loop args₁ args₂ eq i) fun b _ => b →
        ∀ e₁', c.TrExprS (f₁.mkAppList args₁.toList) e₁' →
        ∀ e₂', c.TrExprS (f₂.mkAppList args₂.toList) e₂' → c.IsDefEqU e₁' e₂' := by
    unfold loop; split <;> rename_i h
    · have hr₁ : r₁.length > 0 := by simp [← Array.length_toList, h₁] at h; omega
      have hr₂ : r₂.length > 0 := by simp [eq, ← Array.length_toList, h₂] at h; omega
      let .app (a := a₁) (as := r₁) a1 a2 a3 a4 a5 := he₁
      let .app (a := a₂) (as := r₂) b1 b2 b3 b4 b5 := he₂
      simp [
        show args₁[i] = a₁ by cases args₁; cases h₁; simp [hi₁],
        show args₂[i] = a₂ by cases args₂; cases h₂; simp [hi₂]]
      refine (isDefEq.WF a4 b4).bind fun _ _ _ h => ?_
      split <;> [skip; exact .pure nofun]
      have H := (H1.of_l c.Ewf c.Δwf a1).appDF <| (h ‹_›).of_l c.Ewf c.Δwf a2
      exact loop.WF (l₁ ++ [a₁]) r₁ (l₂ ++ [a₂]) r₂
        (by simp [h₁]) (by simp [hi₁]) (by simp [h₂]) (by simp [hi₂])
        (by simp [a5]) (by simp [b5]) ⟨_, H⟩
    · have hr₁ : r₁.length = 0 := by simp [← Array.length_toList, h₁] at h; omega
      have hr₂ : r₂.length = 0 := by simp [eq, ← Array.length_toList, h₂] at h; omega
      simp at hr₁ hr₂; subst r₁ r₂; simp at h₁ h₂; subst l₁ l₂
      refine .pure fun _ _ h1 _ h2 => ?_
      have u1 := h1.uniq c.Ewf (.refl c.Ewf c.Δwf) he₁.tr
      have u2 := h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂.tr
      exact u1.trans c.Ewf c.Δwf H1 |>.trans c.Ewf c.Δwf u2.symm
  refine loop.WF [] _ [] _ (i := 0) (by simp [Expr.getAppArgs_toList]) rfl
    (by simp [Expr.getAppArgs_toList]) rfl he₁' he₂' (h ‹_›) |>.mono fun _ _ _ h2 hb => ?_
  simp [Expr.getAppArgs_toList, Expr.mkAppList_getAppArgsList] at h2
  exact h2 hb _ he₁ _ he₂

theorem getSortLevel.WF
    (he : c.TrExprS e e') : (getSortLevel e).WF c s fun l _ =>
      ∃ u', VLevel.ofLevel c.lparams l = some u' ∧ c.HasType e' (.sort u') := by
  refine (inferType.WF he).bind fun ty _ le ⟨ty', _, _, h1, h2⟩ => ?_
  refine (ensureSortCore.WF h1).bind fun ty _ le h => ?_
  obtain ⟨⟨u, rfl⟩, ⟨ty₂, h3, h4⟩, _⟩ := h
  let .sort hu := h3
  exact .pure ⟨_, hu, h2.defeqU_r c.Ewf c.Δwf h4.symm⟩

theorem isProp.WF
    (he : c.TrExprS e e') : (isProp e).WF c s fun b _ => b → c.HasType e' (.sort .zero) := by
  refine (getSortLevel.WF he).bind fun l _ le ⟨u', hu, h⟩ => .pure fun H => ?_
  exact h.defeqU_r c.Ewf c.Δwf
    ⟨_, .sortDF (.of_ofLevel hu) trivial (ofLevel_isAlwaysZero hu H)⟩

theorem isDefEqProofIrrel.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqProofIrrel e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqProofIrrel
  refine (inferType.WF he₁).bind fun _ _ _ ⟨_, a1, a2, a3, a4⟩ => ?_
  refine (isProp.WF a3).bind fun _ _ _ h1 => ?_
  split <;> [exact .pure nofun; skip]
  rename_i h; simp at h
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, b1, b2, b3, b4⟩ => .toLBoolM ?_
  refine (isDefEq.WF a3 b3).mono fun _ _ _ h2 hb => ?_
  exact ⟨_, .proofIrrel (h1 h) a4 (b4.defeqU_r c.Ewf c.Δwf (h2 hb).symm)⟩

theorem cacheFailure.WF {c : VContext} {s : VState} :
    (cacheFailure e₁ e₂).WF c s fun _ _ => True := by
  rintro wf _ _ ⟨⟩
  exact ⟨{ s with toState := _ }, rfl, .rfl, { wf with }, ⟨⟩⟩

theorem tryUnfoldProjApp.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    (tryUnfoldProjApp e).WF c s fun oe _ =>
    ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold tryUnfoldProjApp; extract_lets f
  split <;> [exact .pure nofun; skip]
  refine (whnfCore.WF he).bind fun _ _ _ h => ?_
  refine .pure fun _ => ?_
  split <;> rintro ⟨⟩; exact h

def _root_.Lean4Lean.TypeChecker.ReductionStatus.WF
    (c : VContext) (e₁' e₂' : VExpr) (allowContinue := false) : ReductionStatus → Prop
  | .continue e₁ e₂ => allowContinue ∧ c.TrExpr e₁ e₁' ∧ c.TrExpr e₂ e₂'
  | .unknown e₁ e₂ | .false e₁ e₂ => c.TrExpr e₁ e₁' ∧ c.TrExpr e₂ e₂'
  | .true => c.IsDefEqU e₁' e₂'

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.WF.bool
    (H1 : c.TrExpr e₁ e₁') (H2 : c.TrExpr e₂ e₂') (H : b = true → c.IsDefEqU e₁' e₂') :
    ReductionStatus.WF c e₁' e₂' allowContinue (.bool e₁ e₂ b) :=
  match b with
  | .false => ⟨H1, H2⟩
  | .true => H rfl

def _root_.Lean4Lean.TypeChecker.ReductionStatus.WF.defeq
    (h1 : c.IsDefEqU e₁' e₁'') (h2 : c.IsDefEqU e₂' e₂'')
    (H : ReductionStatus.WF c e₁' e₂' ac r) : ReductionStatus.WF c e₁'' e₂'' ac r :=
  match r, H with
  | .continue .., ⟨a1, a2, a3⟩ =>
    ⟨a1, a2.defeq c.Ewf c.Δwf h1, a3.defeq c.Ewf c.Δwf h2⟩
  | .unknown .., ⟨a2, a3⟩ | .false .., ⟨a2, a3⟩ =>
    ⟨a2.defeq c.Ewf c.Δwf h1, a3.defeq c.Ewf c.Δwf h2⟩
  | .true, h => h1.symm.trans c.Ewf c.Δwf h |>.trans c.Ewf c.Δwf h2

theorem lazyDeltaReductionStep.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (lazyDeltaReductionStep e₁ e₂).WF c s fun r _ => r.WF c e₁' e₂' true := by
  unfold lazyDeltaReductionStep
  refine .getEnv ?_; extract_lets delta cont F1 F2
  have hdelta {s e e' ci} (he : c.TrExprS e e') (H : isDelta c.env e = some ci) :
      (delta e).WF c s fun r _ => c.TrExpr r e' := by
    let ⟨n, h1, ⟨_, h2⟩, ls, h3, _⟩ := isDelta_is_some.1 H
    have ⟨_, stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
    have .const a1 a2 a3 := h3 ▸ stk.tr
    have ⟨b1, b2, b3, b4⟩ := c.trenv.find?_uniq h1 a1
    refine (unfoldDefinition.WF he).bind fun oe _ _ H => ?_
    obtain _ | e' := oe; · cases H h1 h2 h3 (a3.trans b3.symm)
    have ⟨_, _, c1, c2⟩ := H
    exact (whnfCore.WF c1).mono fun x _ _ h => h.2.defeq c.Ewf c.Δwf c2
  have hcont {s e₁ e₂} (he₁ : c.TrExpr e₁ e₁') (he₂ : c.TrExpr e₂ e₂') :
      (cont e₁ e₂).WF c s fun r _ => r.WF c e₁' e₂' true := by
    let ⟨_, se₁, de₁⟩ := he₁; let ⟨_, se₂, de₂⟩ := he₂
    refine (quickIsDefEq.WF se₁ se₂).bind fun _ _ _ h => .pure ?_; split
    · exact ⟨rfl, he₁, he₂⟩
    · exact de₁.symm.trans c.Ewf c.Δwf (h rfl) |>.trans c.Ewf c.Δwf de₂
    · exact ⟨he₁, he₂⟩
  split
  · exact .pure ⟨he₁.trExpr c.Ewf c.Δwf, he₂.trExpr c.Ewf c.Δwf⟩
  · refine (tryUnfoldProjApp.WF he₂).bind fun _ _ _ h => ?_; split
    · exact hcont (he₁.trExpr c.Ewf c.Δwf) (h _ rfl).2
    · exact (hdelta he₁ ‹_›).bind fun _ _ _ h => hcont h (he₂.trExpr c.Ewf c.Δwf)
  · refine (tryUnfoldProjApp.WF he₁).bind fun _ _ _ h => ?_; split
    · exact hcont (h _ rfl).2 (he₂.trExpr c.Ewf c.Δwf)
    · exact (hdelta he₂ ‹_›).bind fun _ _ _ h => hcont (he₁.trExpr c.Ewf c.Δwf) h
  rename_i dt dt' hd1 hd2; extract_lets ht hs; split <;> [skip; split]
  · exact (hdelta he₂ ‹_›).bind fun _ _ _ h => hcont (he₁.trExpr c.Ewf c.Δwf) h
  · exact (hdelta he₁ ‹_›).bind fun _ _ _ h => hcont h (he₂.trExpr c.Ewf c.Δwf)
  have hF1 {s} : (F1 ⟨⟩).WF c s fun r _ => r.WF c e₁' e₂' true :=
    (hdelta he₁ ‹_›).bind fun _ _ _ h1 => (hdelta he₂ ‹_›).bind fun _ _ _ h2 => hcont h1 h2
  refine .get ?_; split <;> [skip; exact hF1]
  split <;> [skip; exact cacheFailure.WF.lift.bind fun _ _ _ _ => hF1]
  rename_i h1 h2; simp at h1
  cases ptrEqConstantInfo_eq h1.1.1.2
  have ⟨n₁, b1₁, ⟨_, b2₁⟩, ls₁, b3₁, _⟩ := isDelta_is_some.1 hd1
  have ⟨n₂, b1₂, ⟨_, b2₂⟩, ls₂, b3₂, _⟩ := isDelta_is_some.1 hd2
  simp [b3₁, b3₂, Expr.constLevels!] at h2
  have ⟨_, stk₁⟩ := AppStack.build (e₁.mkAppList_getAppArgsList ▸ he₁)
  have ⟨_, stk₂⟩ := AppStack.build (e₂.mkAppList_getAppArgsList ▸ he₂)
  have .const (us' := ls₁) c1₁ c2₁ c3₁ := b3₁ ▸ stk₁.tr
  have .const (us' := ls₂) c1₂ c2₂ c3₂ := b3₂ ▸ stk₂.tr
  cases (c.trenv.find?_uniq b1₁ c1₁).1
  cases (c.trenv.find?_uniq b1₂ c1₂).1
  cases c1₁.symm.trans c1₂
  have := VEnv.IsDefEq.constDF c1₁
    (Γ := c.vlctx.toCtx) (.of_mapM_ofLevel c2₁) (.of_mapM_ofLevel c2₂)
    ((List.mapM_eq_some.1 c2₁).length_eq.symm.trans c3₁)
    (Level.isEquivList_wf h2 c2₁ c2₂)
  refine (isDefEqArgs.WF ⟨_, stk₁.tr, _, stk₂.tr, _, this⟩ he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [skip; exact cacheFailure.WF.lift.bind fun _ _ _ _ => hF1]
  exact .pure <| h ‹_›

theorem isNatZero_wf {c : VContext} (H : isNatZero e) (h : c.TrExprS e e') : e' = .natZero := by
  have h1 : c.TrExprS (.lit (.natVal 0)) e' := by
    simp [isNatZero] at H; obtain H|H := H
    · have := h.eqv H; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · split at H <;> [exact h; cases H]
  have := TrExprS.lit_has_type (l := .natVal 0) h1
  exact h1.unique (by trivial) (TrExprS.natLit c.hasPrimitives this 0).1

theorem isNatSuccOf?_wf {c : VContext} (H : isNatSuccOf? e = some e₁)
    (h : c.TrExprS e e') : ∃ x, c.TrExprS e₁ x ∧ e' = .app .natSucc x := by
  unfold isNatSuccOf? at H; split at H <;> cases H
  · rename_i n
    have := TrExprS.lit_has_type (l := .natVal (n+1)) h
    refine ⟨_, (TrExprS.natLit c.hasPrimitives this n).1, ?_⟩
    exact h.unique (by trivial) (TrExprS.natLit c.hasPrimitives this (n+1)).1
  · let .app a1 a2 a3 a4 := h
    let .const b1 b2 b3 := a3
    cases c.hasPrimitives.natSucc b1
    simp at b3; subst b3; simp at b2; subst b2
    exact ⟨_, a4, rfl⟩

theorem isDefEqOffset.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (isDefEqOffset e₁ e₂).WF c s fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqOffset; split
  · rename_i h; simp at h
    cases isNatZero_wf h.1 he₁; cases isNatZero_wf h.2 he₂
    exact .pure fun _ => .refl <| he₁.wf c.Ewf c.Δwf
  · split <;> [skip; exact .pure nofun]
    obtain ⟨_, a1, rfl⟩ := isNatSuccOf?_wf ‹_› he₁
    obtain ⟨_, b1, rfl⟩ := isNatSuccOf?_wf ‹_› he₂
    refine .toLBoolM <| (isDefEqCore.WF a1 b1).mono fun _ _ _ h hb => ?_
    let ⟨_, de'⟩ := he₁.wf c.Ewf c.Δwf
    let ⟨_, _, c1, c2⟩ := de'.hasType.1.app_inv c.Ewf c.Δwf
    exact ⟨_, c1.appDF <| (h hb).of_l c.Ewf c.Δwf c2⟩

theorem lazyDeltaReduction.loop.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (lazyDeltaReduction.loop e₁ e₂ n).WF c s fun r _ => r.WF c e₁' e₂' := by
  induction n generalizing s e₁ e₂ e₁' e₂' with | zero => exact .throw | succ n ih
  unfold loop; extract_lets F1
  refine (isDefEqOffset.WF he₁ he₂).bind fun _ _ _ h => ?_; split
  · exact .pure <| .bool (he₁.trExpr c.Ewf c.Δwf) (he₂.trExpr c.Ewf c.Δwf) fun hb =>
      h (by simpa using hb)
  suffices hF1 : ∀ {s}, (F1 ⟨⟩).WF c s fun r _ => r.WF c e₁' e₂' by
    refine .readThe ?_; split <;> [skip; exact hF1]
    refine (reduceNat.WF he₁).bind fun _ _ _ h => ?_; split
    · have ⟨_, a1, a2⟩ := (h _ rfl).2
      refine (isDefEqCore.WF a1 he₂).bind fun _ _ _ h => ?_
      refine .pure <| .bool ⟨_, a1, a2⟩ (he₂.trExpr c.Ewf c.Δwf) fun hb => ?_
      exact a2.symm.trans c.Ewf c.Δwf (h hb)
    refine (reduceNat.WF he₂).bind fun _ _ _ h => ?_; split
    · have ⟨_, a1, a2⟩ := (h _ rfl).2
      refine (isDefEqCore.WF he₁ a1).bind fun _ _ _ h => ?_
      refine .pure <| .bool (he₁.trExpr c.Ewf c.Δwf) ⟨_, a1, a2⟩ fun hb => ?_
      exact (h hb).trans c.Ewf c.Δwf a2
    exact hF1
  intro s; unfold F1; refine .getEnv ?_
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h _ rfl; skip]
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h _ rfl; skip]
  refine (lazyDeltaReductionStep.WF he₁ he₂).bind fun r _ _ h => ?_
  cases r with
  | «continue» =>
    let ⟨_, ⟨_, a1, a2⟩, ⟨_, b1, b2⟩⟩ := h
    exact (ih a1 b1).mono fun _ _ _ h => h.defeq a2 b2
  | _ => exact .pure h

theorem tryStringLitExpansionCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryStringLitExpansionCore e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold tryStringLitExpansionCore; iterate 3 split <;> [skip; exact .pure nofun]
  let .lit _ he₁ := he₁
  exact .toLBoolM <| isDefEqCore.WF he₁ he₂

theorem tryStringLitExpansion.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryStringLitExpansion e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  refine (tryStringLitExpansionCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [skip; exact .pure h]
  exact (tryStringLitExpansionCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

/-- **Vacuity witness for `isDefEqUnitLike.WF`.**  Same shape as
`tryEtaStructCore_never_true`, one step further in: the gate is
`let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I | return
false` on the head constant of `whnf (inferType t)`, which is translated, so
`TrEnv.not_inductInfo` kills it.

Note again what is absent: **`e₂` plays no role.**  `isDefEqUnitLike.WF` claims
`c.IsDefEqU e₁' e₂'`, and this witness shows the branch is dead without ever looking at the
second term.  Dies with `AddInduct`, exactly as the sibling above; see its docstring for the
mechanism and for what the real proof needs (`structEta` at zero fields, twice, plus a
kernel→abstract `IsStructure` bridge — but **no** `TrProj`, since a zero-field structure has
no projections). -/
theorem isDefEqUnitLike_never_true {c : VContext} {s : VState} (he₁ : c.TrExprS e₁ e₁') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = false := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold isDefEqUnitLike
  refine (inferType.WF he₁).bind fun ty _ _ ⟨_, _, _, hty, _⟩ => ?_
  refine (whnf.WF hty).bind fun tType _ _ ⟨_, _, htT, _⟩ => ?_
  obtain ⟨f', hf⟩ := head_tr htT
  split <;> [skip; exact .pure rfl]
  rename_i I us heq
  rw [heq] at hf
  let .const hc _ _ := hf
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
  cases ci <;> first
    | exact absurd hci fun hh => c.trenv.not_inductInfo ⟨_, hc⟩ hh
    | exact .pure rfl

/-- **The `Prop` half of `isDefEqUnitLike.WF`, discharged — and discharged without the dead
`.inductInfo` gate.**

`docs/research-structeta.md` §2 observed that neither `isDefEqUnitLike` nor `tryEtaStructCore`
tests the structure's level, so both fire on `Prop` structures (`And`, `True`) as well as on
`Type`-valued ones, and that the obligation therefore splits in two:

| | `Prop` case | non-`Prop` case |
|---|---|---|
| `isDefEqUnitLike` | `IsDefEq.proofIrrel` — already a spec rule | `structEta` at zero fields, which the spec does not have |

That observation was never machine-checked.  This theorem is the `Prop` column, checked.

**Two properties make it worth having.**

1. *It does not use the vacuity.*  `isDefEqUnitLike_never_true` below kills the branch by
   `TrEnv.not_inductInfo`; this proof instead `split`s at each gate, discharges the four
   `return false` arms by `nofun`, and **enters** the `.inductInfo`/`.ctorInfo` arm, deriving
   its conclusion from the final `isDefEqCore tType (← inferType s)` alone.  Nothing here
   mentions `AddInduct`, so — unlike `isDefEqUnitLike_never_true`, which is scheduled to go red
   — this survives the flip verbatim and is a *component* of the eventual real proof, not a
   placeholder for it.
2. *Its residual holes are all borrowed, none of them structure-eta.*  Measured cone (a
   transitive `getUsedConstantsAsSet` sweep against the 20 census holes):
   `{IsDefEqU.forallE_inv_stratified, TrProj.uniq, TrProj.wf}` — **identical** to
   `inferType.WF`'s own cone, and identical to `isDefEqUnitLike_never_true`'s.  Every one of
   the three enters through `inferType.WF`'s single appeal to `TrExprS.uniq`/`IsDefEq.uniq`
   (unique typing, whose `.proj` case is `TrProj.uniq`).  Nothing in this proof adds a hole,
   and in particular the `Prop` half of the obligation costs **no** structure-eta content.

   That is also the answer to "did the newly-proved unique-typing facts change anything here":
   yes.  `IsDefEq.uniq`'s own cone is now the single hole `IsDefEqU.forallE_inv_stratified`
   (measured), where it used to be the whole injectivity family — so the `Prop` half of this
   obligation went from *blocked behind unique typing* to *one named hole away*.

**What remains, exactly.**  The residue is the case where the unit-like structure lives in
`Type`.  There `t` and `s` are two inhabitants of a type with one closed inhabitant, and no
sequence of the 13 `VEnv.IsDefEq` constructors relates them: `beta`/`eta` need a λ, `extra`
needs a `const`-headed pattern (ι fires only at a constructor application, and the terms here
are arbitrary), and `proofIrrel` needs the `Prop` this branch does not have.  That is the
missing `structEta` rule, and it is *all* that is missing for `isDefEqUnitLike` — no `TrProj`,
no injectivity, no unique typing. -/
theorem isDefEqUnitLike.WF_prop {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hprop : ∀ A, c.HasType e₁' A → c.HasType A (.sort .zero)) :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold isDefEqUnitLike
  refine (inferType.WF he₁).bind fun ty _ _ ⟨ty', _, _, hty, hT⟩ => ?_
  refine (whnf.WF hty).bind fun tType _ _ ⟨_, _, htT, hdefeq⟩ => ?_
  split <;> [skip; exact .pure nofun]
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  refine (M.WF.liftExcept hget).lift.bind fun ci₂ _ _ _ => ?_
  split <;> [skip; exact .pure nofun]
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, _, _, _, hS⟩ => ?_
  refine (isDefEqCore.WF htT ‹_›).mono fun _ _ _ h hb => ?_
  exact ⟨_, .proofIrrel (hprop _ hT) hT
    (hS.defeqU_r c.Ewf c.Δwf (hdefeq.symm.trans c.Ewf c.Δwf (h hb)).symm)⟩

/-- `WF_prop` in the form one actually has it: **`e₁'` is a proof**, i.e. it inhabits *some*
proposition, rather than *every* type it inhabits being a proposition.

The two are equivalent only through **unique typing**, and that is the one place where this
round's change to `Theory/Typing/{Injectivity,UniqSort}.lean` is felt here: `IsDefEq.uniqU` is
what turns "some type of `e₁'` is a `Prop`" into "the inferred type of `e₁'` is a `Prop`".

**Read the cone before using this.**  `IsDefEq.uniqU` runs through `IsDefEqU.sort_inv`, which
is *proved* but whose axiom cone still contains `sorryAx` via
`IsDefEqU.forallE_inv_stratified`.  This corollary's cone is the same three holes as
`WF_prop`'s, so the extra hypothesis-weakening is free here; the two are kept separate anyway,
because `WF_prop`'s statement is the one that does not presuppose unique typing and so is the
one to use if the `inferType.WF` plumbing is ever re-based off `inferType.WF'`. -/
theorem isDefEqUnitLike.WF_proof {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hA : c.HasType e₁' A) (hAp : c.HasType A (.sort .zero)) :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' :=
  isDefEqUnitLike.WF_prop he₁ he₂ fun _ hB =>
    hAp.defeqU_l c.Ewf c.Δwf (hA.uniqU c.Ewf c.Δwf hB)

/-- **The `IsStructure` bridge, at `isDefEqUnitLike`'s gate.**

`docs/handoff-eta.md` §5 named the single missing step as "supply `c.venv.IsStructure I D T C`
from `c.env.isNonRecStructure I = true`".  This is that step, stated at the exact gate
`isDefEqUnitLike` tests, with the typing side conditions `VEnv.StructEta` needs bundled in —
they come from the same place (the block's declaration) and there is no cheaper source for
them today.

**It is a hypothesis, and it has to be** — but *not* for the reason an earlier round gave.
That reason ("`AddIndConsts`' shape predicates and `TrConstant` constrain a constant's name,
level count and type and nothing else, so the six fields the eta checks read are free") is
**obsolete**: `IndShape`/`CtorShape` landed in `AddInductStages`, `numIndices`, `ctors`,
`numFields`, `numParams` and `induct` are now pinned, and `R10.Wit.isNonRecStructure_one_sided`
shows the one surviving free field (`isRec`) can only make the checker *refuse* eta.

The real obstruction is one level down, in `VEnv.IsStructure` itself: its `types` field says
`D.types = [T]`, and `Lean.isNonRecStructure` accepts members of *mutual* non-recursive blocks,
for which that is false.  Lean's own kernel both accepts `.proj` on such a member and performs
structure eta on it (`MutNonRec.kernelProjChecks`'s `#eval`, `Verify/StructureBridge.lean`).
The field is nevertheless not weakenable as it stands — `projCore` supplies one motive and one
minor premise where such a block's recursor binds two of each (`MutNonRec.projCore_arity_wrong`)
— so the repair is a generalisation of `projCore`, and this bridge stays a hypothesis until it
lands.

Every binder is pinned: `tType`/`tType'` by the translation, `I`/`ls` by the head equation,
`cn` by `v.ctors = [cn]`, `v`/`w` by the two lookups.  The conclusion's `D T C us ps` are
existential. -/
def UnitLikeBridge (c : VContext) : Prop :=
  ∀ {tType : Expr} {tType' : VExpr} {I cn : Name} {ls : List Level}
    {v : InductiveVal} {w : ConstructorVal},
    c.TrExprS tType tType' → tType.getAppFn = .const I ls →
    c.env.find? I = some (.inductInfo v) →
    v.isRec = false → v.ctors = [cn] → v.numIndices = 0 →
    c.env.find? cn = some (.ctorInfo w) → w.numFields = 0 →
    ∃ D T C us ps, tType' = (VExpr.const I us).mkApp ps ∧
      c.venv.IsStructure I D T C ∧ T.indices = [] ∧ C.fields = [] ∧
      us.length = D.uvars ∧ (∀ l ∈ us, l.WF c.lparams.length) ∧ ps.length = D.np ∧
      c.venv.HasArgs c.lparams.length c.vlctx.toCtx (D.params.map (VExpr.instL us)) ps

/-- **`isDefEqUnitLike.WF`, modulo the two things the spec and the refinement layer are
missing** — and nothing else.

`WF_prop` above handles the `Prop` case with no new rule.  This is the *whole* statement,
`Prop` case included, from
* `c.venv.StructEta` — structure eta (`Theory/Inductive/StructureEta.lean`), the rule the
  thirteen `IsDefEq` constructors do not give; and
* `UnitLikeBridge c` — the `AddInduct` bridge.

Nothing else is assumed, and the proof enters the real `.inductInfo`/`.ctorInfo` arm rather
than using `TrEnv.not_inductInfo`, so it survives the `AddInduct` flip verbatim.  When both
hypotheses become theorems, `isDefEqUnitLike.WF` is this lemma applied to them.

The route is `StructEta.unitLike`: at zero fields the η-expansion is the closed term
`C.mk ps` for *both* inhabitants, so the two `HasType`s the checker establishes at a common
type give `e₁' ≡ e₂'` by `trans`.  No `TrProj`, no projection machinery, no injectivity. -/
theorem isDefEqUnitLike.WF_of_structEta {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hSE : c.venv.StructEta) (hbr : UnitLikeBridge c) :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  have hget : ∀ {name}, (c.env.get name).WF fun ci => c.env.find? name = some ci := by
    intro name; simp [Kernel.Environment.get]; split <;> [refine .pure ‹_›; exact .throw]
  unfold isDefEqUnitLike
  refine (inferType.WF he₁).bind fun ty _ _ ⟨ty', _, _, hty, hT⟩ => ?_
  refine (whnf.WF hty).bind fun tType _ _ ⟨_, _, htT, hdefeq⟩ => ?_
  split <;> [skip; exact .pure nofun]
  rename_i I ls heq
  refine .getEnv <| (M.WF.liftExcept hget).lift.bind fun ci _ _ hci => ?_
  split <;> [skip; exact .pure nofun]
  refine (M.WF.liftExcept hget).lift.bind fun ci₂ _ _ hcc => ?_
  split <;> [skip; exact .pure nofun]
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, _, _, _, hS⟩ => ?_
  refine (isDefEqCore.WF htT ‹_›).mono fun _ _ _ h hb => ?_
  obtain ⟨D, T, C, us, ps, hEq, hIS, hidx, hnf, hus, huswf, hps, hpsA⟩ :=
    hbr htT heq hci rfl rfl rfl hcc rfl
  subst hEq
  exact ⟨_, hSE.unitLike hIS hidx hnf hus huswf hps hpsA
    (hT.defeqU_r c.Ewf c.Δwf hdefeq.symm) (hS.defeqU_r c.Ewf c.Δwf (h hb).symm)⟩

/-- Still `sorry`, deliberately.  `(isDefEqUnitLike_never_true he₁).mono
fun _ _ _ h hb => absurd (h ▸ hb) nofun` closes it today; that close is vacuous and is
discarded when `AddInduct` lands.  `WF_of_structEta` above is the non-vacuous version: this
statement is exactly that one with its two hypotheses removed, and neither is provable in this
tree (`Theory/Inductive/StructureEta.lean`, `Verify/StructureBridge.lean` say why).
See `isDefEqUnitLike_never_true`.

**Status 2026-08-31 (checked, not attempted).**  Same reading as `tryEtaStructCore.WF`:
`WF_of_structEta`, `WF_prop` and `WF_proof` are `sorry`-free, so the residual is exactly
`c.venv.StructEta` and `UnitLikeBridge`, and the latter waits on the `VEnv.IsStructure.decl`
strengthening in flight elsewhere.  Not attempted this round (scope boundary). -/
theorem isDefEqUnitLike.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := sorry

theorem lazyDeltaProjReduction.finish.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS (.proj n₁ i e₁) e₁') (he₂ : c.TrExprS (.proj n₂ i e₂) e₂') :
    (finish i e₁ e₂).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
  unfold finish
  refine (reduceProjCore.WF he₁).bind fun _ _ _ h1 => ?_; extract_lets F
  have hF {s} : (F ⟨⟩).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
    have .proj a1 a2 := he₁; have .proj b1 b2 := he₂
    refine (isDefEqCore.WF a1 b1).mono fun _ _ _ h hb => ?_
    exact a2.uniq c.Ewf (.refl c.Δwf.toCtx) b2 (h hb)
  split <;> [have ⟨a1, _, a2, a3⟩ := h1 _ rfl; exact .pureBind hF]
  refine (reduceProjCore.WF he₂).bind fun _ _ _ h2 => ?_
  split <;> [have ⟨b1, _, b2, b3⟩ := h2 _ rfl; exact .pureBind hF]
  exact (isDefEqCore.WF a2 b2).mono fun _ _ _ h hb =>
    a3.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf b3

theorem lazyDeltaProjReduction.loop.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS (.proj n₁ i e₁) e₁') (he₂ : c.TrExprS (.proj n₂ i e₂) e₂') :
    (loop i e₁ e₂ n).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
  induction n generalizing s e₁ e₂ e₁' e₂' with | zero => exact .throw | succ n ih
  unfold loop; have .proj a1 a2 := he₁; have .proj b1 b2 := he₂
  refine (lazyDeltaReductionStep.WF a1 b1).bind fun _ _ _ h => ?_; split
  · have ⟨_, ⟨_, c1, c2⟩, ⟨_, d1, d2⟩⟩ := h
    have ⟨_, e1⟩ := a2.defeqDFC c.Ewf (.refl c.Δwf.toCtx) c2.symm
    have ⟨_, e2⟩ := b2.defeqDFC c.Ewf (.refl c.Δwf.toCtx) d2.symm
    refine (ih (.proj c1 e1) (.proj d1 e2)).mono fun _ _ _ h hb => ?_
    have f1 := e1.uniq c.Ewf (.refl c.Δwf.toCtx) a2 c2
    have f2 := e2.uniq c.Ewf (.refl c.Δwf.toCtx) b2 d2
    exact f1.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf f2
  · exact .pure fun _ => a2.uniq c.Ewf (.refl c.Δwf.toCtx) b2 h
  all_goals
    have ⟨⟨_, c1, c2⟩, ⟨_, d1, d2⟩⟩ := h
    have ⟨_, e1⟩ := a2.defeqDFC c.Ewf (.refl c.Δwf.toCtx) c2.symm
    have ⟨_, e2⟩ := b2.defeqDFC c.Ewf (.refl c.Δwf.toCtx) d2.symm
    refine (finish.WF (.proj c1 e1) (.proj d1 e2)).mono fun _ _ _ h hb => ?_
    have f1 := e1.uniq c.Ewf (.refl c.Δwf.toCtx) a2 c2
    have f2 := e2.uniq c.Ewf (.refl c.Δwf.toCtx) b2 d2
    exact f1.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf f2

theorem isDefEqCore'.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqCore' e₁ e₂) fun b _ => b = true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqCore'; extract_lets F1
  refine (quickIsDefEq.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun hb => h (by simpa using hb); skip]
  refine .readThe ?_
  suffices ∀ {s}, RecM.WF c s (F1 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split <;> [rename_i h1; exact this]
    refine (whnf.WF he₁).bind fun _ _ _ ⟨_, _, a1, a2⟩ => ?_
    split <;> [rename_i h2; exact this]
    refine .pure fun _ => ?_
    simp [Expr.isConstOf] at h1 h2
    split at h1 <;> simp at h1; cases h1.2; split at h2 <;> simp at h2; cases h2
    let .const b1 b2 b3 := he₂
    let .const c1 c2 c3 := a1
    cases c.hasPrimitives.boolTrue b1
    cases c.hasPrimitives.boolTrue c1
    simp at b3 c3; subst b3 c3; simp at b2 c2; subst b2 c2
    exact a2.symm
  intro; unfold F1
  refine (whnfCore.WF he₁).bind fun _ _ _ ⟨_, e₁', a1, a2⟩ => ?_
  refine (whnfCore.WF he₂).bind fun _ _ _ ⟨_, e₂', b1, b2⟩ => ?_
  extract_lets F2
  refine .mono (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h hb =>
    a2.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf b2
  suffices ∀ {s}, RecM.WF c s (F2 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split <;> [skip; exact this]
    refine (quickIsDefEq.WF a1 b1).bind fun _ _ _ h => ?_
    split <;> [skip; exact this]
    exact .pure fun hb => h (by simpa using hb)
  intro; unfold F2
  refine (isDefEqProofIrrel.WF a1 b1).bind fun _ _ _ h => ?_
  split
  · exact .pure fun hb => h (by simpa using hb)
  refine (lazyDeltaReduction.loop.WF a1 b1).readThe.bind fun _ _ _ h => ?_; split
  · cases h.1
  · exact .pure fun _ => h
  · exact .pure nofun
  have ⟨⟨e₁', c1, c4⟩, ⟨e₂', d1, d4⟩⟩ := h
  refine .mono (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h hb =>
    c4.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf d4
  extract_lets F3
  suffices ∀ {s}, RecM.WF c s (F3 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split
    · split <;> [rename_i h2; exact this]
      refine .pure fun _ => ?_
      simp at h2; cases h2.1
      have .const c1 c2 c3 := c1; have .const d1 d2 d3 := d1
      cases d1.symm.trans c1
      have := VEnv.IsDefEq.constDF c1
        (Γ := c.vlctx.toCtx) (.of_mapM_ofLevel c2) (.of_mapM_ofLevel d2)
        ((List.mapM_eq_some.1 c2).length_eq.symm.trans c3)
        (Level.isEquivList_wf h2.2 c2 d2)
      exact this.toU
    · split <;> [rename_i h; exact this]
      simp at h; subst h
      exact .pure fun _ => c1.uniq c.Ewf (.refl c.Ewf c.Δwf) d1
    · split <;> [rename_i h2; exact this]; simp at h2; subst h2
      refine (lazyDeltaProjReduction.loop.WF c1 d1).bind fun _ _ _ h => ?_
      split <;> [refine .pure fun _ => h ‹_›; exact this]
    · exact this
  intro; unfold F3
  refine (whnfCore.WF c1).bind fun _ _ _ ⟨_, e₁'', c5, c6⟩ => ?_
  refine (whnfCore.WF d1).bind fun _ _ _ ⟨_, e₂'', d5, d6⟩ => ?_
  split
  · exact (isDefEqCore.WF c5 d5).mono fun _ _ _ h hb =>
      c6.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf d6
  refine (isDefEqApp.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryEtaExpansion.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryEtaStruct.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryStringLitExpansion.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun hb => h (by simpa using hb); skip]
  refine (isDefEqUnitLike.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  exact .pure nofun
