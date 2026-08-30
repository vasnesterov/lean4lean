import Lean4Lean.Theory.Inductive.StructureClosed

/-!
# The generalised projection term: padded motive and minor blocks

`VInductDecl'.projCore` (`Theory/Inductive/Structure.lean`) hands the recursor exactly
**one** motive and **one** minor premise, while `VInductDecl'.recType` binds `D.nm` motives
and `D.nmin` minors.  That is why `VEnv.IsStructure.types` has to say `D.types = [T]`, and
why weakening it to `T ∈ D.types` is *refuted* (`MutNonRec.projCore_arity_wrong`,
`Verify/StructureBridge.lean`): the weakened form admits blocks at which `projTerm` is a
recursor under-applied by `D.nm + D.nmin - 2` arguments.

This file builds the repair `docs/handoff-eta.md` §3 specifies: `projCoreG`, which supplies a
**full** motive block and a **full** minor block, so its spine saturates the recursor at every
block, not only at singleton ones.  `IsStructureG` is the correspondingly widened shape
predicate.

Nothing here edits `projCore`, `IsStructure`, or `TrProj`; the swap is a separate step, and
`projCoreG_eq_projCore` below is what makes it a *generalisation* rather than a different
term.

## The padding, and its one non-obvious ingredient

A motive for a type `T_k` of the block other than the projected one must inhabit
`∀ ι_k, T_k ι_k → Sort ℓ` where `ℓ` is the **projected field's** level — not the block's.
A closed inhabitant of `Sort ℓ` does not exist uniformly, so the padding has to borrow one
from the context.  `handoff-eta.md` §3 proposed the projected field's own type,
`instAll (A_i.instL us) (ps ++ [proj 0 e, …, proj (i-1) e])`.

**This file uses a cheaper one**: `X := mot.mkApp (ιs ++ [e])`, the *real* motive applied to
the index spine and the major premise.  It is the same type up to β, it is built from data
`projCore` already has in scope (so `projArgs` stays structural in `i` with no second
projection list), and — the point — the existing chain already types it: it is precisely the
term `projCore_hasType`'s `hconv` premise is about.

The padding is then `fun ι_k x_k => X → X`, in `Sort (imax ℓ ℓ)`, and `VLevel.imax_self`
gives `imax ℓ ℓ ≈ ℓ`.  A minor for a constructor of `T_k` binds its fields *and* its
induction hypotheses and returns `fun z => z`; binding the induction hypotheses is what also
lifts the `noRec` narrowing, so one change covers both fields.
-/

namespace Lean4Lean

open VExpr

namespace VInductDecl'

/-- The binder telescope of minor premise `q`, i.e. `minorType`'s `mkPi` telescope.  It lives
over `params ++ motives ++ minors<q`, so `np + D.nm + q` binders. -/
def minorBinders (D : VInductDecl') (q : Nat) (C : VIndCtor) : List VExpr :=
  liftTele (D.nm + q) (D.atRecTele (C.fields.map (·.type))) ++ D.ihTypes q C

/-- `minorType`'s body: the motive of the constructor's own type, applied to the result
indices and to the constructor applied to its fields. -/
def minorBody (D : VInductDecl') (q t : Nat) (C : VIndCtor) : VExpr :=
  (VExpr.bvar ((D.ihTypes q C).length + C.fields.length + q + (D.nm - 1 - t))).mkApp <|
    C.args.map (fun a => shift (D.nm + q) (D.ihTypes q C).length C.fields.length (D.atRec a)) ++
    [D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
      (bvars (D.ihTypes q C).length C.fields.length)]

theorem minorType_eq_mkPi (D : VInductDecl') (q t : Nat) (C : VIndCtor) :
    D.minorType q t C = mkPi (D.minorBinders q C) (D.minorBody q t C) := rfl

theorem length_minorBinders (D : VInductDecl') (q : Nat) (C : VIndCtor) :
    (D.minorBinders q C).length = C.fields.length + (D.ihTypes q C).length := by
  simp [minorBinders, VExpr.length_liftTele, atRecTele]

/-- The padding motive for a block member other than the projected type: `fun ι x => X → X`,
where `X` is the projected field's type (see the module docstring). -/
def padMotive (D : VInductDecl') (T' : VIndType) (us : List VLevel) (ps : List VExpr) (X : VExpr) : VExpr :=
  let ni := T'.indices.length
  mkLams (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps) <|
    .lam ((VExpr.const T'.name us).mkApp (ps.map (·.liftN ni) ++ bvars 0 ni)) <|
      .forallE (X.liftN (ni+1)) (X.liftN (ni+2))

/-- The motive block: the real motive at the projected type's index `j`, padding elsewhere. -/
def padMotives (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel) (ps is : List VExpr)
    (i j : Nat) (earlier : List VExpr) (e : VExpr) : List VExpr :=
  let mot := T.projMotive C us ps is i earlier
  let X := mot.mkApp (is ++ [e])
  (List.range D.nm).map fun k =>
    if k = j then mot else D.padMotive (D.types.getD k default) us ps X

theorem length_padMotives (D : VInductDecl') (T C us ps is i j earlier e) :
    (D.padMotives T C us ps is i j earlier e).length = D.nm := by simp [padMotives]

/-- The padding minor for a constructor of a block member other than the projected type:
`fun fields ihs z => z`. -/
def padMinor (D : VInductDecl') (lvls : List VLevel) (spine : List VExpr) (X : VExpr)
    (q : Nat) (C' : VIndCtor) : VExpr :=
  let Θ := VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine
  mkLams Θ (.lam (X.liftN Θ.length) (.bvar 0))

/-- The real minor for the projected constructor, **generalised to bind the induction
hypotheses**: `fun f₀ … f_{n-1} ih₀ … ih_{r-1} => fᵢ`.  With no recursive fields this is
`projMinor`; with recursive fields it is what `projCore`'s minor should have been, and is why
`VEnv.IsStructure.noRec` is not needed here. -/
def realMinor (D : VInductDecl') (lvls : List VLevel) (spine : List VExpr)
    (i q : Nat) (C' : VIndCtor) : VExpr :=
  let Θ := VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine
  mkLams Θ (.bvar (Θ.length - 1 - i))

/-- The minor block, built left to right: minor `q`'s declared telescope is stated over
`params ++ motives ++ minors<q`, so each entry is instantiated at the spine the earlier ones
extend. -/
def padMinorsAux (D : VInductDecl') (lvls : List VLevel) (ps mots : List VExpr) (X : VExpr) (i j : Nat) :
    List (Nat × VIndCtor) → Nat → List VExpr → List VExpr
  | [], _, acc => acc
  | (t, C') :: rest, q, acc =>
      let spine := ps ++ mots ++ acc
      let m := if t = j then D.realMinor lvls spine i q C' else D.padMinor lvls spine X q C'
      padMinorsAux D lvls ps mots X i j rest (q+1) (acc ++ [m])

theorem length_padMinorsAux (D : VInductDecl') (lvls ps mots X i j) :
    ∀ (l : List (Nat × VIndCtor)) (q : Nat) (acc : List VExpr),
      (D.padMinorsAux lvls ps mots X i j l q acc).length = acc.length + l.length
  | [], _, _ => by simp [padMinorsAux]
  | (_, _) :: rest, q, acc => by
    rw [padMinorsAux, length_padMinorsAux D lvls ps mots X i j rest (q+1)]
    simp; omega

def padMinors (D : VInductDecl') (lvls : List VLevel) (ps mots : List VExpr) (X : VExpr) (i j : Nat) :
    List VExpr :=
  D.padMinorsAux lvls ps mots X i j D.ctorsAll 0 []

theorem length_padMinors (D : VInductDecl') (lvls ps mots X i j) :
    (D.padMinors lvls ps mots X i j).length = D.nmin := by
  simp [padMinors, length_padMinorsAux]

/-- **The generalised projection core.**  Same as `projCore`, except that the motive and
minor blocks are full-length. -/
def projCoreG (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (ps is : List VExpr) (i j : Nat) (earlier : List VExpr) (e : VExpr) : VExpr :=
  let lvls := D.projLvls C us i
  let mot := T.projMotive C us ps is i earlier
  let X := mot.mkApp (is ++ [e])
  let mots := D.padMotives T C us ps is i j earlier e
  let mins := D.padMinors lvls ps mots X i j
  (VExpr.const (Lean.mkRecName T.name) lvls).mkApp (ps ++ mots ++ mins ++ is ++ [e])

/-- The earlier projections of the major-premise binder, generalised.  **Keep structural**:
both recursive calls are at `i`, exactly as in `projArgs`. -/
def projArgsG (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (ps is : List VExpr) (j : Nat) : Nat → List VExpr
  | 0 => []
  | i+1 =>
    projArgsG D T C us ps is j i ++
      [D.projCoreG T C us ps is i j
        (projArgsG D T C us (ps.map (·.liftN (is.length+1))) (bvars 1 is.length) j i) (.bvar 0)]

def projTermG (D : VInductDecl') (T : VIndType) (C : VIndCtor) (us : List VLevel)
    (ps is : List VExpr) (i j : Nat) (e : VExpr) : VExpr :=
  D.projCoreG T C us ps is i j
    (D.projArgsG T C us (ps.map (·.liftN (is.length+1))) (bvars 1 is.length) j i) e

/-! ## Compatibility: `projCoreG` **is** `projCore` at a narrow block

This is what makes the change a generalisation rather than a substitution.  At a block with
one type, one constructor and no recursive fields — exactly `VEnv.IsStructure`'s hypotheses —
the generalised term is the old one on the nose. -/

/-- The minor block's telescope, at a narrow block, is the field telescope `projMinor` binds. -/
theorem minorTele_narrow (D : VInductDecl') (C : VIndCtor) {us : List VLevel}
    {lvls : List VLevel} {ps : List VExpr} {mot : VExpr}
    (hnm : D.nm = 1) (hrec : C.recFields = [])
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    VExpr.instAllTele ((D.minorBinders 0 C).map (VExpr.instL lvls)) (ps ++ [mot])
      = VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps := by
  simp only [VInductDecl'.minorBinders, VInductDecl'.ihTypes, hrec, hnm, List.zipIdx_nil,
    List.map_nil, List.append_nil, Nat.add_zero, VInductDecl'.atRecTele,
    List.map_map, Function.comp_def, VExpr.instL_liftTele, VExpr.instL_instL, hself]
  exact VExpr.instAllTele_liftTele_snoc

theorem padMotives_narrow (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps is : List VExpr) (i : Nat) (earlier : List VExpr) (e : VExpr)
    (hnm : D.nm = 1) :
    D.padMotives T C us ps is i 0 earlier e = [T.projMotive C us ps is i earlier] := by
  simp [VInductDecl'.padMotives, hnm]

theorem padMinors_narrow (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    {us lvls : List VLevel} {ps : List VExpr} {X mot : VExpr} {i : Nat}
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    D.padMinors lvls ps [mot] X i 0 = [C.projMinor us ps i] := by
  have hnm : D.nm = 1 := by simp [VInductDecl'.nm, htypes]
  have hall : D.ctorsAll = [(0, C)] := by
    simp [VInductDecl'.ctorsAll, htypes, hctors]
  rw [VInductDecl'.padMinors, hall]
  simp only [VInductDecl'.padMinorsAux, if_pos rfl, VInductDecl'.realMinor,
    List.nil_append, List.append_nil, VIndCtor.projMinor]
  rw [minorTele_narrow D C hnm hrec hself]
  simp

/-- **`projCoreG` at a narrow block is `projCore`.** -/
theorem projCoreG_eq_projCore (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps is : List VExpr) (i : Nat) (earlier : List VExpr) (e : VExpr)
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) :
    D.projCoreG T C us ps is i 0 earlier e = D.projCore T C us ps is i earlier e := by
  have hnm : D.nm = 1 := by simp [VInductDecl'.nm, htypes]
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  rw [D.projCore_eq T C us ps is i earlier e]
  simp only [VInductDecl'.projCoreG]
  rw [padMotives_narrow D T C us ps is i earlier e hnm,
    padMinors_narrow D T C htypes hctors hrec hself]
  simp [List.append_assoc]

theorem projArgsG_eq_projArgs (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel)
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) :
    ∀ (i : Nat) (ps is : List VExpr),
      D.projArgsG T C us ps is 0 i = D.projArgs T C us ps is i
  | 0, _, _ => rfl
  | i+1, ps, is => by
    rw [VInductDecl'.projArgsG, VInductDecl'.projArgs,
      projArgsG_eq_projArgs D T C us htypes hctors hrec hus i ps is,
      projArgsG_eq_projArgs D T C us htypes hctors hrec hus i _ _,
      projCoreG_eq_projCore D T C us ps is i _ _ htypes hctors hrec hus]

/-- **`projTermG` at a narrow block is `projTerm`.**  So every `rfl` validation of
`projTerm` against Lean's own elaborator (`Theory/Inductive/StructureExamples.lean`) is a
validation of `projTermG` too. -/
theorem projTermG_eq_projTerm (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) (ps is : List VExpr) (i : Nat) (e : VExpr)
    (htypes : D.types = [T]) (hctors : T.ctors = [C]) (hrec : C.recFields = [])
    (hus : us.length = D.uvars) :
    D.projTermG T C us ps is i 0 e = D.projTerm T C us ps is i e := by
  rw [VInductDecl'.projTermG, VInductDecl'.projTerm,
    projArgsG_eq_projArgs D T C us htypes hctors hrec hus i _ _,
    projCoreG_eq_projCore D T C us ps is i _ _ htypes hctors hrec hus]

/-! ## The refutation, re-run

`MutNonRec.projCore_arity_wrong` (`Verify/StructureBridge.lean`) refutes the weakening of
`IsStructure.types` by exhibiting a block at which `projCore`'s spine has length
`D.np + 2 + |ιs| + 1` while `recType` demands `D.recArity T = D.np + D.nm + D.nmin +
T.indices.length + 1`, and `recArity_eq_projCore_iff` says the two agree **iff**
`D.nm + D.nmin = 2`.

`length_projCoreG_spine` below is the same measurement for `projCoreG`, and it is
`D.recArity T` **unconditionally** — no side condition, no `nm + nmin = 2`.  So the witness
that refutes the weakening does not apply to the generalisation: the quantity it exhibits a
mismatch in is now an identity. -/

theorem length_projCoreG_spine (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) {ps is earlier : List VExpr} {i j : Nat} {e : VExpr}
    (hps : ps.length = D.np) :
    (ps ++ D.padMotives T C us ps is i j earlier e ++
        D.padMinors (D.projLvls C us i) ps (D.padMotives T C us ps is i j earlier e)
          ((T.projMotive C us ps is i earlier).mkApp (is ++ [e])) i j ++ is ++ [e]).length
      = D.np + D.nm + D.nmin + is.length + 1 := by
  simp [hps, length_padMotives, length_padMinors]; omega

/-- **The generalised spine saturates the recursor at every block.** -/
theorem recArity_eq_projCoreG (D : VInductDecl') (T : VIndType) (C : VIndCtor)
    (us : List VLevel) {ps is earlier : List VExpr} {i j : Nat} {e : VExpr}
    (hps : ps.length = D.np) (his : is.length = T.indices.length) :
    (ps ++ D.padMotives T C us ps is i j earlier e ++
        D.padMinors (D.projLvls C us i) ps (D.padMotives T C us ps is i j earlier e)
          ((T.projMotive C us ps is i earlier).mkApp (is ++ [e])) i j ++ is ++ [e]).length
      = D.recArity T := by
  rw [length_projCoreG_spine D T C us hps, VInductDecl'.recArity, his]

end VInductDecl'

/-! ## The padding motive is well-typed

`VInductDecl'.motiveType_isType` (`Theory/Inductive/Lemmas.lean`) is already general in the
motive index and in the prefix context, so the declared type of *every* motive is available;
what has to be generalised are the two `Theory/Inductive/StructureClosed.lean` steps that
specialise it to index `0`. -/

section
variable {env : VEnv} {U : Nat} {S : Lean.Name} {D : VInductDecl'} {T T' : VIndType}
  {C : VIndCtor} {us : List VLevel}

open VInductDecl' in
/-- `motiveType_instL_instAll` at an arbitrary motive index, with the earlier motives
supplied.  The `liftTele t` in `motiveType` is exactly what the `ms` block cancels. -/
theorem motiveType_instL_instAll_gen (D : VInductDecl') (T' : VIndType) (C : VIndCtor)
    {us : List VLevel} {ps ms : List VExpr} {i t : Nat}
    (hT : D.types.getD t default = T')
    (hus : us.length = D.uvars) (hps : ps.length = D.np) (hms : ms.length = t) :
    VExpr.instAll ((D.motiveType t).instL (D.projLvls C us i)) (ps ++ ms)
      = VExpr.mkPi (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps)
          (.forallE ((VExpr.const T'.name us).mkApp
              (ps.map (·.liftN T'.indices.length) ++ VExpr.bvars 0 T'.indices.length))
            (.sort (D.elimLvl.inst (D.projLvls C us i)))) := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  simp only [VInductDecl'.motiveType, hT, VInductDecl'.atRecTele,
    VExpr.instL_mkPi, VExpr.instL_liftTele, VInductDecl'.tyApp', VExpr.instL_mkApp, VExpr.instL,
    VExpr.map_instL_bvars, List.map_append, VExpr.instAll_mkPi, VExpr.instAll_forallE,
    VExpr.instAll_sort, VExpr.instAll_mkApp, VExpr.instAll_const,
    List.map_map, Function.comp_def, VExpr.instL_instL, hself,
    VExpr.length_liftTele, List.length_map, Nat.zero_add, Nat.add_zero]
  rw [VExpr.instAllTele_liftTele_append (n := t) hms]
  rw [VExpr.map_instAll_bvars_top (by omega) (by simp [hps, hms]; omega),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add _)),
    List.take_left' hps]

/-- The declared type of motive `t`, at the use site, is a type. -/
theorem motiveG_declType_isType (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) {t : Nat} (ht : t ≤ D.nm) {T'' : VIndType}
    (hT : D.types[t]? = some T'') {i : Nat} {Γ ps ms : List VExpr}
    (hspine : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      (ps ++ ms)) :
    env.IsType U Γ (VExpr.instAll ((D.motiveType t).instL (D.projLvls C us i)) (ps ++ ms)) := by
  have hR := hI.toRecCtx
  obtain ⟨u, hmot⟩ := VInductDecl'.motiveType_isType hR hT
    (M := ((List.range t).map D.motiveType).reverse) (by simp)
    (VInductDecl'.onCtxMotivesTake hR t ht)
  have h1 := VEnv.HasType.instL (ls := D.projLvls C us i) (U' := U)
    (VInductDecl'.projLvls_wf h7 i) hmot
  simp only [List.map_append, List.map_reverse, VExpr.instL] at h1
  rw [← List.reverse_append] at h1
  have hOn : OnCtx (((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
      ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i))).reverse)
      (env.IsType U) := by
    have := OnCtx.instL (env := env) (ls := D.projLvls C us i) (U' := U)
      (VInductDecl'.projLvls_wf h7 i) (VInductDecl'.onCtxMotivesTake hR t ht)
    rw [← List.reverse_append, List.map_reverse, List.map_append] at this
    exact this
  have h2 := VEnv.IsDefEq.weakR henv (OnCtx.ctxClosed henv hOn) h1 Γ
  have h4 := VEnv.HasType.instAll henv hspine h2
  rw [VExpr.instAll_sort] at h4
  exact ⟨_, h4⟩

/-- The padding motive's own binder context, at an arbitrary block member. -/
theorem padMotiveCtx_wf (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat} (ht : t ≤ D.nm)
    (hT : D.types[t]? = some T') {i : Nat} {Γ ps ms : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np) (hms : ms.length = t)
    (hspine : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      (ps ++ ms)) :
    OnCtx ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse ++ Γ)
        (env.IsType U) ∧
      env.IsType U ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse ++ Γ)
        ((VExpr.const T'.name us).mkApp
          (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)) := by
  have hIT := motiveG_declType_isType (C := C) henv hI h7 ht hT hspine
  rw [motiveType_instL_instAll_gen D T' C
    (by rw [List.getD_eq_getElem?_getD, hT]; rfl) hus hps hms] at hIT
  obtain ⟨hOn, hfa⟩ := VEnv.IsType.mkPi_inv henv hΓ hIT
  exact ⟨hOn, (hfa.forallE_inv henv).1⟩

/-- **The padding motive inhabits the recursor's motive binder.**

The only ingredient beyond the ambient bookkeeping is `X`, an inhabitant-free type at the
*elimination* level: `X → X` is then in `Sort (imax ℓ ℓ)`, and `VLevel.imax_self` closes the
gap to `Sort ℓ`.  Note what is **not** needed here: F17.  `X` is required at the elimination
level directly, and the two-branch F17 argument is what types `X` itself at the call site —
it is already paid for by `projMotiveBody_hasType`. -/
theorem padMotive_hasType (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat} (ht : t ≤ D.nm)
    (hT : D.types[t]? = some T') {i : Nat} {Γ ps ms : List VExpr} {X : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np) (hms : ms.length = t)
    (hspine : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      (ps ++ ms))
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i)))) :
    env.HasType U Γ (D.padMotive T' us ps X)
      (VExpr.instAll ((D.motiveType t).instL (D.projLvls C us i)) (ps ++ ms)) := by
  obtain ⟨hOn, uc, hAty⟩ := padMotiveCtx_wf henv hI h7 hus ht hT hΓ hps hms hspine
  have hlenΔ : (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).length
      = T'.indices.length := by simp
  have hW1 : Ctx.LiftN (T'.indices.length + 1) 0 Γ
      ((VExpr.const T'.name us).mkApp
          (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)
        :: ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse ++ Γ)) := by
    have := Ctx.LiftN.zero (Γ := Γ) (n := T'.indices.length + 1)
      ((VExpr.const T'.name us).mkApp
          (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)
        :: (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse) (by simp)
    simpa using this
  have hX1 := VEnv.HasType.weakN henv hW1 hX
  simp only [VExpr.liftN] at hX1
  have hW2 : Ctx.LiftN (T'.indices.length + 2) 0 Γ
      (X.liftN (T'.indices.length + 1) ::
        (VExpr.const T'.name us).mkApp
          (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)
        :: ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse ++ Γ)) := by
    have := Ctx.LiftN.zero (Γ := Γ) (n := T'.indices.length + 2)
      (X.liftN (T'.indices.length + 1) ::
        (VExpr.const T'.name us).mkApp
          (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)
        :: (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse) (by simp)
    simpa using this
  have hX2 := VEnv.HasType.weakN henv hW2 hX
  simp only [VExpr.liftN] at hX2
  have hℓwf : (D.elimLvl.inst (D.projLvls C us i)).WF U :=
    VLevel.WF.inst (VInductDecl'.projLvls_wf (C := C) h7 i)
  have hbody := VEnv.IsDefEq.defeqDF
      (VEnv.IsDefEq.sortDF (l := .imax (D.elimLvl.inst (D.projLvls C us i))
          (D.elimLvl.inst (D.projLvls C us i)))
        (l' := D.elimLvl.inst (D.projLvls C us i))
        ⟨hℓwf, hℓwf⟩ hℓwf VLevel.imax_self)
      (VEnv.HasType.forallE hX1 hX2)
  rw [motiveType_instL_instAll_gen D T' C
    (by rw [List.getD_eq_getElem?_getD, hT]; rfl) hus hps hms]
  show env.HasType U Γ (VExpr.mkLams _ (.lam _ (.forallE _ _))) _
  exact VEnv.HasType.mkLams hOn (VEnv.HasType.lam hAty hbody)

/-- **The padding motive's β-normal form.**  Applied to *any* spine of the right length, the
padding motive's body collapses to `X → X`: it ignores every argument.  This is the
computation the `hbeta` premise of `padMinor_hasType` needs, with the motive-lookup step
still to be supplied. -/
theorem padMotive_body_instAll {X : VExpr} {as : List VExpr} {ni : Nat}
    (h : as.length = ni + 1) :
    VExpr.instAll (.forallE (X.liftN (ni+1)) (X.liftN (ni+2))) as 0
      = .forallE X (X.liftN 1) := by
  rw [VExpr.instAll_forallE, Nat.zero_add]
  congr 1
  · rw [← h]; exact VExpr.instAll_liftN as X 0
  · rw [show ni+2 = 1+(ni+1) from by omega,
      ← VExpr.liftN'_liftN' (e := X) (n1 := 1) (n2 := ni+1) (k1 := 0) (k2 := 1)
        (Nat.zero_le _) (Nat.le_refl _), ← h]
    exact VExpr.instAll_liftN as (X.liftN 1) 1

/-! ### The padding minor

`padMinor` binds the constructor's fields **and its induction hypotheses** — that is the half
of the generalisation that lifts the `noRec` narrowing — and returns `fun z => z`.  Its
telescope is not computed: it is *defined* as the instantiation of `minorType`'s own binder
block, so `instAll_mkPi` splits the declared type into exactly the telescope `padMinor` binds
and a body, with no analogue of `minorType_instL_instAll` needed for the telescope.

What is left open is stated as the `hbeta` premise: the declared body is the motive of the
constructor's own type applied to the result indices and the constructor, and at a *padding*
motive that application β-reduces to `X → X`.  `VEnv.IsDefEq.betaMkLams` is the tool; what
does not exist yet is the computation identifying the head `.bvar` of `minorBody` with the
`t`-th entry of the motive block after `instAll`. -/

theorem padMinor_hasType (henv : env.Ordered)
    {lvls : List VLevel} {q t : Nat} {C' : VIndCtor} {Γ spine : List VExpr} {X : VExpr}
    {ℓ : VLevel}
    (hΓ : OnCtx Γ (env.IsType U))
    (hdecl : env.IsType U Γ (VExpr.instAll ((D.minorType q t C').instL lvls) spine))
    (hX : env.HasType U Γ X (.sort ℓ))
    (hbeta : ∃ u, env.IsDefEq U
        ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine).reverse ++ Γ)
        (VExpr.instAll ((D.minorBody q t C').instL lvls) spine
          ((D.minorBinders q C').map (VExpr.instL lvls)).length)
        (.forallE (X.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)
          ((X.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length).liftN 1))
        (.sort u)) :
    env.HasType U Γ (D.padMinor lvls spine X q C')
      (VExpr.instAll ((D.minorType q t C').instL lvls) spine) := by
  have hsplit : VExpr.instAll ((D.minorType q t C').instL lvls) spine
      = VExpr.mkPi (VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine)
          (VExpr.instAll ((D.minorBody q t C').instL lvls) spine
            ((D.minorBinders q C').map (VExpr.instL lvls)).length) := by
    rw [D.minorType_eq_mkPi q t C', VExpr.instL_mkPi, VExpr.instAll_mkPi, Nat.zero_add]
  have hlenΘ :
      (VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine).length
        = ((D.minorBinders q C').map (VExpr.instL lvls)).length := by simp
  rw [hsplit] at hdecl ⊢
  obtain ⟨hOn, hbodyT⟩ := VEnv.IsType.mkPi_inv henv hΓ hdecl
  have hW : Ctx.LiftN ((D.minorBinders q C').map (VExpr.instL lvls)).length 0 Γ
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine).reverse ++ Γ) :=
    Ctx.LiftN.zero (Γ := Γ)
      (VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine).reverse (by simp)
  have hX' := VEnv.HasType.weakN henv hW hX
  simp only [VExpr.liftN] at hX'
  have hid := VEnv.HasType.lam hX' (VEnv.HasType.bvar (Lookup.zero ..))
  obtain ⟨u, hbeta⟩ := hbeta
  have hbody := VEnv.IsDefEq.defeqDF hbeta.symm hid
  show env.HasType U Γ (VExpr.mkLams
      (VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine)
      (.lam (X.liftN
        (VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls)) spine).length)
        (.bvar 0))) _
  rw [hlenΘ]
  exact VEnv.HasType.mkLams hOn hbody

end

/-! ## `FieldUsed` does not depend on the type index

`TrProj`'s F17 clause is stated with `C.FieldUsed D 0 k` — the type index hard-coded to `0`,
because `IsStructure.types` forces `T` to be `D.types[0]`.  Widening `types` raises the
question whether that `0` silently becomes the wrong index (the "statement about the wrong
thing" failure mode).  **It does not**: `FieldUsed` reads only the de Bruijn structure of
`C.canonResult D j`, and the only thing `j` changes there is the head constant's *name*,
which `Skips'` ignores.  So the clause transports verbatim. -/

theorem VExpr.skips'_mkApp : ∀ {as : List VExpr} {f : VExpr} {n k : Nat},
    VExpr.Skips' n (f.mkApp as) k ↔ VExpr.Skips' n f k ∧ ∀ a ∈ as, VExpr.Skips' n a k
  | [], _, _, _ => by simp [VExpr.mkApp]
  | a :: as, f, n, k => by
    rw [VExpr.mkApp, VExpr.skips'_mkApp (as := as)]
    simp [VExpr.Skips', and_assoc]

theorem VExpr.skips'_mkPi_congr {n : Nat} : ∀ {As : List VExpr} {B B' : VExpr} {k : Nat},
    (∀ m, VExpr.Skips' n B m ↔ VExpr.Skips' n B' m) →
    (VExpr.Skips' n (mkPi As B) k ↔ VExpr.Skips' n (mkPi As B') k)
  | [], _, _, _, h => h _
  | _ :: As, B, B', k, h => by
    simp only [VExpr.mkPi, VExpr.Skips']
    exact and_congr_right fun _ => VExpr.skips'_mkPi_congr (As := As) h

/-- **The type index is invisible to `FieldUsed`.** -/
theorem VIndCtor.fieldUsed_index_irrel (C : VIndCtor) (D : VInductDecl') (j j' k : Nat) :
    C.FieldUsed D j k ↔ C.FieldUsed D j' k := by
  refine not_congr (VExpr.skips'_mkPi_congr fun m => ?_)
  simp only [VIndCtor.canonResult, VInductDecl'.tyApp, VExpr.skips'_mkApp, VExpr.Skips']

/-! ## The widened shape predicate

`VEnv.IsStructure` narrows what the kernel accepts in two fields (both recorded at its
docstring, both machine-checked against Lean's own kernel by `MutNonRec.kernelProjChecks`,
`Verify/StructureBridge.lean`):

* `types : D.types = [T]` — `infer_proj` never checks that the block is a singleton, and the
  eta gate performs structure eta at a member of a two-type block;
* `noRec : C.recFields = []` — `infer_proj` never reads `InductiveVal.isRec`.

`IsStructureG` drops both.  `ctors` stays: it is genuinely forced, by `infer_proj` and by
`is_structure_like` alike. -/

structure VEnv.IsStructureG (env : VEnv) (S : Lean.Name) (D : VInductDecl') (j : Nat)
    (T : VIndType) (C : VIndCtor) : Prop where
  /-- `T` is *a* type of the block, at index `j` — not necessarily the only one. -/
  types : D.types[j]? = some T
  name : T.name = S
  /-- Forced by the kernel: `infer_proj` fails unless `I_val.ctors` is a singleton. -/
  ctors : T.ctors = [C]
  decl : ∃ env₀ env₁, D.WF env₀ ∧ env₀.addInduct' D = some env₁ ∧ env₁ ≤ env

namespace VEnv.IsStructureG

variable {env env' : VEnv} {S : Lean.Name} {D : VInductDecl'} {j : Nat}
  {T : VIndType} {C : VIndCtor}

theorem mono (h : env ≤ env') (H : env.IsStructureG S D j T C) : env'.IsStructureG S D j T C :=
  { H with decl := let ⟨_, _, h1, h2, h3⟩ := H.decl; ⟨_, _, h1, h2, h3.trans h⟩ }

theorem lt_nm (H : env.IsStructureG S D j T C) : j < D.nm :=
  List.getElem?_eq_some_iff.1 H.types |>.1

end VEnv.IsStructureG

/-- The narrow predicate is the wide one at index `0`. -/
theorem VEnv.IsStructure.toG {env : VEnv} {S : Lean.Name} {D : VInductDecl'}
    {T : VIndType} {C : VIndCtor} (H : env.IsStructure S D T C) :
    env.IsStructureG S D 0 T C where
  types := by rw [H.types]; rfl
  name := H.name
  ctors := H.ctors
  decl := H.decl

end Lean4Lean
