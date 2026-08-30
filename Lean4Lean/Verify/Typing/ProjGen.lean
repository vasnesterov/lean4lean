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

/-! ## A weakening below the substitution window

`VExpr.liftN_instAll` (`Theory/Inductive/TelescopeLift.lean`) commutes a weakening whose cut
sits *at* the substitution window's lower edge.  The induction hypotheses of a minor premise
sit strictly **below** the fields, so the weakening they induce has cut `0` while the window
starts at `nr + nf`; that is this lemma.  (`liftN_instAll` is the case `j = k`.) -/
theorem VExpr.instAll_liftN_below {n : Nat} :
    ∀ {as : List VExpr} {X : VExpr} {j k : Nat}, j ≤ k →
      VExpr.instAll (X.liftN n j) as (n + k) = (VExpr.instAll X as k).liftN n j
  | [], _, _, _, _ => rfl
  | a :: as, X, j, k, h => by
    rw [VExpr.instAll_cons, VExpr.instAll_cons,
      show n + k + as.length = n + (k + as.length) from by omega,
      ← VExpr.liftN_instN_lo n X a (k + as.length) j (by omega),
      instAll_liftN_below (as := as) (X := X.inst a (k + as.length)) (j := j) (k := k) h]

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

/-- The number of binders `minorType q t C` puts between the motive block and its body.
Kept as a name because it is the `instAll` cut of every computation below. -/
theorem length_minorBinders_map (D : VInductDecl') (q : Nat) (C : VIndCtor)
    (lvls : List VLevel) :
    ((D.minorBinders q C).map (VExpr.instL lvls)).length
      = (D.ihTypes q C).length + C.fields.length := by
  rw [List.length_map, length_minorBinders]; omega

/-- The spine `minorBody` hands to the motive, after the block substitution: the
constructor's result indices and the constructor applied to its own fields. -/
def minorBodyArgs (D : VInductDecl') (lvls : List VLevel) (q : Nat) (C : VIndCtor)
    (spine : List VExpr) : List VExpr :=
  (C.args.map (fun a => shift (D.nm + q) (D.ihTypes q C).length C.fields.length (D.atRec a)) ++
    [D.ctorApp' C ((D.ihTypes q C).length + C.fields.length + (D.nm + q))
      (bvars (D.ihTypes q C).length C.fields.length)]).map
    (fun a => VExpr.instAll (a.instL lvls) spine
      ((D.minorBinders q C).map (VExpr.instL lvls)).length)

theorem length_minorBodyArgs (D : VInductDecl') (lvls : List VLevel) (q : Nat) (C : VIndCtor)
    (spine : List VExpr) :
    (D.minorBodyArgs lvls q C spine).length = C.args.length + 1 := by
  simp [minorBodyArgs]

/-- **The head of `minorBody`, after the block substitution, is motive `t`.**

This is the index computation the generalisation turns on, and the only place the motive
block's *position* in the recursor's spine is used.  In the spine `ps ++ mots ++ mins<q` of
length `np + nm + q`, under the `nr + nf` binders of the minor, `minorBody`'s head
`.bvar (nr+nf+q+(nm-1-t))` resolves to spine element `np + t`, i.e. `mots[t]` — weakened
past the minor's own binders.

**Consequence** (and it is what makes `padMinorsAux`' accumulator harmless in the proofs):
neither `minorType`'s telescope nor its body refers to the `mins<q` block at all; `acc`
enters only through its *length*. -/
theorem minorBody_instAll_spine (D : VInductDecl') {lvls : List VLevel} {q t : Nat}
    {C : VIndCtor}
    {ps mots acc : List VExpr} {P : VExpr}
    (hget : mots[t]? = some P) (hps : ps.length = D.np) (hmots : mots.length = D.nm)
    (hacc : acc.length = q) (htlt : t < D.nm) :
    VExpr.instAll ((D.minorBody q t C).instL lvls) (ps ++ mots ++ acc)
        ((D.minorBinders q C).map (VExpr.instL lvls)).length
      = (P.liftN ((D.minorBinders q C).map (VExpr.instL lvls)).length).mkApp
          (D.minorBodyArgs lvls q C (ps ++ mots ++ acc)) := by
  have hk := D.length_minorBinders_map q C lvls
  have hspine : (ps ++ mots ++ acc)[D.np + t]? = some P := by
    rw [List.append_assoc, List.getElem?_append_right (by omega), hps, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
    exact hget
  rw [minorBody, VExpr.instL_mkApp, VExpr.instL, VExpr.instAll_mkApp, minorBodyArgs,
    List.map_map]
  congr 1
  exact VExpr.instAll_bvar_get hspine (by simp [hk, hps, hmots, hacc]; omega)

/-- **The minor's binder telescope splits, at any constructor.**  The motive block and the
earlier minors are discarded by `minorType`'s own `liftTele (nm + q)` on the constructor's
stored field types, so the first block is the field telescope at the use site; the
**induction-hypothesis** block survives, instantiated at the same spine but under the `nf`
field binders.

`minorTele_norec` below is the `recFields = []` instance, where the second block is empty.
It is the *only* thing `hrec` was buying. -/
theorem minorTele_gen (D : VInductDecl') {lvls us : List VLevel} {q : Nat} {C : VIndCtor}
    {ps mots acc : List VExpr}
    (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) (ps ++ mots ++ acc)
      = VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps
        ++ VExpr.instAllTele ((D.ihTypes q C).map (VExpr.instL lvls)) (ps ++ mots ++ acc)
            C.fields.length := by
  have hlen : (mots ++ acc).length = D.nm + q := by simp [hmots, hacc]
  have hL : ((VExpr.liftTele (D.nm + q)
      (D.atRecTele (C.fields.map (·.type)))).map (VExpr.instL lvls)).length
      = C.fields.length := by simp [VExpr.length_liftTele, atRecTele]
  rw [minorBinders, List.map_append, VExpr.instAllTele_append, Nat.zero_add, hL]
  congr 1
  rw [List.append_assoc, atRecTele]
  simp only [List.map_map, Function.comp_def, VExpr.instL_liftTele, VExpr.instL_instL, hself]
  rw [← hlen, VExpr.instAllTele_liftTele_append rfl]

/-- **The motive's spine, at any constructor**: the same two terms `ctorArgs_hasArgs` and
`ctorApp_hasType` already type, **weakened past the induction-hypothesis binders**.

That weakening is the whole content of the recursive case, and it is not cosmetic: at a
constructor with one recursive field the constructor's own field moves from `.bvar 0` to
`.bvar 1`, because the induction hypothesis now sits below it (`MutRec.minorBodyArgs_at_rmk`
in `ProjGenWitness.lean` fires this, and its negative control shows the `nr = 0` reading is
rejected).  `minorBodyArgs_norec` below is the `recFields = []` instance, where
`liftN 0` is the identity. -/
theorem minorBodyArgs_gen (D : VInductDecl') {lvls us : List VLevel} {q : Nat}
    {C : VIndCtor} {ps mots acc : List VExpr}
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    D.minorBodyArgs lvls q C (ps ++ mots ++ acc)
      = ((C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
        ++ [(VExpr.const C.name us).mkApp
              (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)]).map
          (·.liftN (D.ihTypes q C).length) := by
  have hk : ((D.minorBinders q C).map (VExpr.instL lvls)).length
      = (D.ihTypes q C).length + C.fields.length := D.length_minorBinders_map q C lvls
  have hlen : (mots ++ acc).length = D.nm + q := by simp [hmots, hacc]
  have hassoc : ps ++ mots ++ acc = ps ++ (mots ++ acc) := by rw [List.append_assoc]
  rw [minorBodyArgs, hk, List.map_append, List.map_map, List.map_cons, List.map_nil,
    List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · refine List.map_congr_left fun a _ => ?_
    show VExpr.instAll ((VExpr.shift (D.nm + q) (D.ihTypes q C).length C.fields.length
        (D.atRec a)).instL lvls) (ps ++ mots ++ acc)
        ((D.ihTypes q C).length + C.fields.length) = _
    rw [VExpr.shift, Nat.add_zero, VInductDecl'.atRec, VExpr.instL_liftN, VExpr.instL_liftN,
      VExpr.instL_instL, hself,
      VExpr.instAll_liftN_below (Nat.zero_le _), hassoc, ← hlen,
      VExpr.instAll_liftN_append rfl]
    rfl
  · show [VExpr.instAll ((D.ctorApp' C ((D.ihTypes q C).length + C.fields.length
        + (D.nm + q)) (bvars (D.ihTypes q C).length C.fields.length)).instL lvls)
        (ps ++ mots ++ acc) ((D.ihTypes q C).length + C.fields.length)] = _
    rw [VInductDecl'.ctorApp', VExpr.instL_mkApp, VExpr.instL, hself, List.map_append,
      VExpr.map_instL_bvars, VExpr.map_instL_bvars, VExpr.instAll_mkApp, VExpr.instAll_const,
      List.map_append,
      VExpr.map_instAll_bvars_top (by omega) (by simp [hps, hlen]; omega),
      VExpr.map_instAll_bvars_lt (Nat.le_refl _),
      hassoc, List.take_left' hps, VExpr.liftN_mkApp, VExpr.liftN, List.map_append,
      VExpr.map_liftN_bvars_lo (Nat.zero_le _), Nat.add_zero]
    simp only [List.map_map, Function.comp_def, VExpr.liftN_liftN]
    rw [Nat.add_comm C.fields.length (D.ihTypes q C).length]

/-- **At a non-recursive constructor the motive's spine is what the existing chain already
types.**  Both entries collapse to the terms `ctorArgs_hasArgs` and `ctorApp_hasType`
(`Theory/Inductive/StructureClosed.lean`) prove typed at index `0`: the motive block and the
earlier minors are discarded by the `liftN (D.nm + q)` that `minorType` puts on the
constructor's stored data, and the parameter block is read off the top of the substitution
window.

So for a non-recursive block, `padMinor_hasType'`'s remaining `hbs` premise is exactly those
two lemmas **at an arbitrary block index**, and nothing else. -/
theorem minorBodyArgs_norec (D : VInductDecl') {lvls us : List VLevel} {q : Nat}
    {C : VIndCtor} {ps mots acc : List VExpr}
    (hrec : C.recFields = []) (hps : ps.length = D.np)
    (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    D.minorBodyArgs lvls q C (ps ++ mots ++ acc)
      = (C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
        ++ [(VExpr.const C.name us).mkApp
              (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)] := by
  have hih : D.ihTypes q C = [] := by simp [ihTypes, hrec]
  rw [D.minorBodyArgs_gen hps hmots hacc hself, hih]
  simp [VExpr.liftN_zero]

/-- **The padding minor's binder telescope, at a non-recursive constructor.**  The
generalisation of `minorTele_narrow` below from `nm = 1, q = 0` to an arbitrary position in
the block: the motive block and the earlier minors are discarded by `minorType`'s own
`liftTele (nm + q)`, so what is left is the field telescope at the use site. -/
theorem minorTele_norec (D : VInductDecl') {lvls us : List VLevel} {q : Nat} {C : VIndCtor}
    {ps mots acc : List VExpr}
    (hrec : C.recFields = []) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) (ps ++ mots ++ acc)
      = VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps := by
  have hih : D.ihTypes q C = [] := by simp [ihTypes, hrec]
  rw [D.minorTele_gen hmots hacc hself, hih]
  simp

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

/-- The motive block at the projected index **is** the real motive. -/
theorem padMotives_getElem_eq (D : VInductDecl') (T C us ps is i j earlier e)
    (hj : j < D.nm) :
    (D.padMotives T C us ps is i j earlier e)[j]? = some (T.projMotive C us ps is i earlier) := by
  rw [padMotives]
  simp [List.getElem?_map, List.getElem?_range, hj]

/-- …and at every other index it is a *padding* motive.  This is what makes `padMinor_beta`'s
`hget` premise satisfiable, i.e. what stops that lemma from being vacuous. -/
theorem padMotives_getElem_ne (D : VInductDecl') (T C us ps is i j earlier e)
    {k : Nat} (hk : k < D.nm) (hne : k ≠ j) :
    (D.padMotives T C us ps is i j earlier e)[k]?
      = some (D.padMotive (D.types.getD k default) us ps
          ((T.projMotive C us ps is i earlier).mkApp (is ++ [e]))) := by
  rw [padMotives]
  simp [List.getElem?_map, List.getElem?_range, hk, hne]

/-- **The padding motive commutes with a weakening of its data.**  `padMotive`'s only free
variables come from `ps` and `X`; the `ClosedTele` premise is what stops an index entry from
reaching past them (see the refutation recorded at `VInductDecl'.ProjClosed`). -/
theorem padMotive_liftN (D : VInductDecl') (T' : VIndType) (us : List VLevel)
    {ps : List VExpr} {X : VExpr} {n : Nat}
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length) :
    (D.padMotive T' us ps X).liftN n
      = D.padMotive T' us (ps.map (·.liftN n)) (X.liftN n) := by
  have hpmap : ∀ m : Nat,
      (ps.map (·.liftN (T'.indices.length + m))).map (·.liftN n (T'.indices.length + m))
        = (ps.map (·.liftN n)).map (·.liftN (T'.indices.length + m)) := by
    intro m
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_def]
    rw [VExpr.liftN'_liftN' (Nat.zero_le _) (Nat.le_add_right _ _), VExpr.liftN_liftN,
      Nat.add_comm]
  simp only [padMotive]
  rw [VExpr.liftN_mkLams, VExpr.liftTele_instAllTele₀ hcl, VExpr.length_instAllTele,
    List.length_map, Nat.zero_add]
  refine congrArg _ ?_
  simp only [VExpr.liftN]
  congr 1
  · rw [VExpr.liftN_mkApp, VExpr.liftN, List.map_append, VExpr.map_liftN_bvars_hi (by omega)]
    congr 2
    simpa using hpmap 0
  · congr 1
    · rw [VExpr.liftN'_liftN' (Nat.zero_le _) (Nat.le_of_eq (Nat.add_zero _)),
        VExpr.liftN_liftN, Nat.add_comm]
    · rw [show T'.indices.length + 1 + 1 = T'.indices.length + 2 from by omega,
        VExpr.liftN'_liftN' (Nat.zero_le _) (Nat.le_of_eq (Nat.add_zero _)),
        VExpr.liftN_liftN, Nat.add_comm]


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

/-- The padding motive's **body**, typed under its own two binder blocks.

Split out of `padMotive_hasType` because `padMotive_app_beta` needs exactly this and nothing
else about the motive: `VEnv.IsDefEq.betaMkLams` asks for the *body*'s typing, not the
abstraction's.  Note how few hypotheses it takes — the block index `t`, the parameter spine
and the motive prefix play no role at all.

The only ingredient beyond the ambient bookkeeping is `X`, a type at the *elimination*
level: `X → X` is then in `Sort (imax ℓ ℓ)`, and `VLevel.imax_self` closes the gap to
`Sort ℓ`.  Note what is **not** needed here: F17.  `X` is required at the elimination level
directly, and the two-branch F17 argument is what types `X` itself at the call site — it is
already paid for by `projMotiveBody_hasType`. -/
theorem padMotive_body_hasType (henv : env.Ordered)
    (h7 : ∀ l ∈ us, l.WF U) {i : Nat} {Γ ps : List VExpr} {X : VExpr}
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i)))) :
    env.HasType U
      ((VExpr.const T'.name us).mkApp
          (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)
        :: ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse ++ Γ))
      (.forallE (X.liftN (T'.indices.length+1)) (X.liftN (T'.indices.length+2)))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
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
  exact VEnv.IsDefEq.defeqDF
      (VEnv.IsDefEq.sortDF (l := .imax (D.elimLvl.inst (D.projLvls C us i))
          (D.elimLvl.inst (D.projLvls C us i)))
        (l' := D.elimLvl.inst (D.projLvls C us i))
        ⟨hℓwf, hℓwf⟩ hℓwf VLevel.imax_self)
      (VEnv.HasType.forallE hX1 hX2)

/-- **The padding motive inhabits the recursor's motive binder.** -/
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
  have hbody := padMotive_body_hasType (T' := T') (C := C) (ps := ps) henv h7 hX
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

/-- **The padding motive applied to a saturating spine β-reduces to `X → X`.**

This is the semantic half of the collapse: `padMotive_body_instAll` is the syntax, this is
the `IsDefEq`.  The spine is the constructor's result indices together with the constructor
application — exactly the arguments `minorBody` supplies — and the only thing used about
them is that they inhabit the motive's own binder telescope.

The `hbs` premise is the honest residual handed to the consumer: it is the generalisation to
an arbitrary block member of `ctorArgs_hasArgs` and `ctorApp_hasType`
(`Theory/Inductive/StructureClosed.lean`), which prove exactly this at index `0`. -/
theorem padMotive_app_beta (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat} (ht : t ≤ D.nm)
    (hT : D.types[t]? = some T') {i : Nat} {Γ ps ms bs : List VExpr} {X : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hps : ps.length = D.np) (hms : ms.length = t)
    (hspine : env.HasArgs U Γ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      (ps ++ ms))
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hbs : env.HasArgs U Γ
      (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps
        ++ [(VExpr.const T'.name us).mkApp
              (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)]) bs) :
    env.IsDefEq U Γ ((D.padMotive T' us ps X).mkApp bs)
      (.forallE X (X.liftN 1)) (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  obtain ⟨hOn, uc, hAty⟩ := padMotiveCtx_wf henv hI h7 hus ht hT hΓ hps hms hspine
  have hbody := padMotive_body_hasType (T' := T') (C := C) (ps := ps) henv h7 hX
  have hlen : bs.length = T'.indices.length + 1 := by
    have := hbs.length_eq; simp at this; omega
  have hrev : (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps
        ++ [(VExpr.const T'.name us).mkApp
              (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)]).reverse ++ Γ
      = (VExpr.const T'.name us).mkApp
          (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)
        :: ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps).reverse ++ Γ) := by simp
  have hOnAs : OnCtx ((VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps
        ++ [(VExpr.const T'.name us).mkApp
              (ps.map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length)]).reverse ++ Γ)
      (env.IsType U) := by rw [hrev]; exact ⟨hOn, uc, hAty⟩
  have key := VEnv.IsDefEq.betaMkLams henv hOnAs hbs (by rw [hrev]; exact hbody)
  rw [VExpr.mkLams_append, VExpr.instAll_sort, padMotive_body_instAll hlen] at key
  exact key

/-- **The `hbeta` premise of `padMinor_hasType`, discharged.**

Three pieces composed: `minorBody_instAll_spine` identifies the declared body's head with
the motive block's `t`-th entry, `padMotive_liftN` moves that entry under the minor's own
binders, and `padMotive_app_beta` β-reduces it.  The context `Δ` is arbitrary — the
computation does not care that the caller instantiates it at the minor's own telescope.

What the caller still owes is `hbs`: the constructor's result indices and the constructor
applied to its fields, typed against the padding motive's binder telescope.  That is the
block-index generalisation of `ctorArgs_hasArgs`/`ctorApp_hasType`
(`Theory/Inductive/StructureClosed.lean`), which prove exactly it at index `0`, and it is
the only residual left of this step. -/
theorem padMinor_beta (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat} (ht : t ≤ D.nm)
    (hT : D.types[t]? = some T') (htlt : t < D.nm)
    {i q : Nat} {C' : VIndCtor} {lvls : List VLevel}
    {Δ ps mots acc ms : List VExpr} {X : VExpr}
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length)
    (hget : mots[t]? = some (D.padMotive T' us ps X))
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hΔ : OnCtx Δ (env.IsType U))
    (hms : ms.length = t)
    (hspine : env.HasArgs U Δ
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)) ++ ms))
    (hX : env.HasType U Δ
      (X.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)
      (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hbs : env.HasArgs U Δ
      (VExpr.instAllTele (T'.indices.map (VExpr.instL us))
          (ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length))
        ++ [(VExpr.const T'.name us).mkApp
              ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)).map
                  (·.liftN T'.indices.length)
                ++ bvars 0 T'.indices.length)])
      (D.minorBodyArgs lvls q C' (ps ++ mots ++ acc))) :
    env.IsDefEq U Δ
      (VExpr.instAll ((D.minorBody q t C').instL lvls) (ps ++ mots ++ acc)
        ((D.minorBinders q C').map (VExpr.instL lvls)).length)
      (.forallE (X.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)
        ((X.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length).liftN 1))
      (.sort (D.elimLvl.inst (D.projLvls C us i))) := by
  rw [D.minorBody_instAll_spine hget hps hmots hacc htlt,
    D.padMotive_liftN T' us hcl]
  exact padMotive_app_beta (C := C) henv hI h7 hus ht hT hΔ (by simpa using hps) hms
    hspine hX hbs

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

/-- **`padMinor_hasType` with its `hbeta` premise discharged.**

This is the residual of `docs/handoff-projections.md` §0.5 closed.  What is left is `hbs`
alone — the constructor's result indices and the constructor applied to its fields, typed
against the padding motive's binder telescope, under the minor's own binders.  Everything
about the *padding* is now proved; `hbs` is about the **constructor**, and is the
block-index generalisation of `ctorArgs_hasArgs`/`ctorApp_hasType`.

Note `hΓ'` and the weakened `X` are not premises: the first comes out of `hdecl` by
`IsType.mkPi_inv`, the second by weakening `hX`. -/
theorem padMinor_hasType' (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat} (ht : t ≤ D.nm)
    (hT : D.types[t]? = some T') (htlt : t < D.nm)
    {i q : Nat} {C' : VIndCtor} {lvls : List VLevel}
    {Γ ps mots acc ms : List VExpr} {X : VExpr}
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length)
    (hget : mots[t]? = some (D.padMotive T' us ps X))
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hms : ms.length = t)
    (hΓ : OnCtx Γ (env.IsType U))
    (hdecl : env.IsType U Γ
      (VExpr.instAll ((D.minorType q t C').instL lvls) (ps ++ mots ++ acc)))
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hspine : env.HasArgs U
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ)
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)) ++ ms))
    (hbs : env.HasArgs U
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ)
      (VExpr.instAllTele (T'.indices.map (VExpr.instL us))
          (ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length))
        ++ [(VExpr.const T'.name us).mkApp
              ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)).map
                  (·.liftN T'.indices.length)
                ++ bvars 0 T'.indices.length)])
      (D.minorBodyArgs lvls q C' (ps ++ mots ++ acc))) :
    env.HasType U Γ (D.padMinor lvls (ps ++ mots ++ acc) X q C')
      (VExpr.instAll ((D.minorType q t C').instL lvls) (ps ++ mots ++ acc)) := by
  have hW : Ctx.LiftN ((D.minorBinders q C').map (VExpr.instL lvls)).length 0 Γ
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ) :=
    Ctx.LiftN.zero (Γ := Γ)
      (VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse (by simp)
  obtain ⟨hOn, -⟩ := VEnv.IsType.mkPi_inv henv hΓ
    (by rwa [D.minorType_eq_mkPi q t C', VExpr.instL_mkPi, VExpr.instAll_mkPi,
      Nat.zero_add] at hdecl)
  have hbeta := padMinor_beta (C := C) henv hI h7 hus ht hT htlt hcl hget hps hmots hacc hOn
    hms hspine (VEnv.HasType.weakN henv hW hX) hbs
  exact padMinor_hasType (D := D) henv hΓ hdecl hX ⟨_, hbeta⟩

/-! ### The constructor's spine, at an arbitrary block member

`ctorArgs_hasArgs` and `ctorApp_hasType` (`Theory/Inductive/StructureClosed.lean`) prove
exactly this at `VEnv.IsStructure`'s index `0`.  Their proofs use `H : IsStructure` **only**
through `H.types0`, `H.memCtor`, `H.memCtorsAll` and `H.typesD`; `VInductDecl'.RecCtx.ctors`
and `VInductDecl'.ctorApp'_hasType` are already general in the block index.  So the
generalisation is the substitution of those four, and nothing else. -/

/-- `ctorArgs_hasArgs` at an arbitrary block member. -/
theorem ctorArgs_hasArgs_gen (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) {t : Nat} {T' : VIndType} {C' : VIndCtor}
    (hT : D.types[t]? = some T') (hC : C' ∈ T'.ctors)
    {Γ ps : List VExpr}
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasArgs U
      ((VExpr.instAllTele (C'.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.liftTele C'.fields.length
        (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps))
      (C'.args.map fun a => VExpr.instAll (a.instL us) ps C'.fields.length) := by
  have hR := hI.toRecCtx
  have hCwf : VIndCtor.WF env D t T' C' := hR.ctors t T' hT C' hC
  have hOn0 : OnCtx (((C'.fields.map (·.type)).reverse ++ D.params.reverse).map (VExpr.instL us))
      (env.IsType U) := OnCtx.instL h7 (hCwf.onCtxAllFields henv)
  have h1 := VEnv.HasArgs.instL (U' := U) (ls := us) h7 hCwf.args_ty
  simp only [List.map_append, List.map_reverse, VExpr.instL_liftTele, List.map_map,
    Function.comp_def] at h1 hOn0
  rw [← List.reverse_append] at h1 hOn0
  have h2 := VEnv.HasArgs.weakR (Γ := Γ) henv (OnCtx.ctxClosed henv hOn0) h1
  have h3 := VEnv.HasArgs.instAllUnder henv hpsA h2
  rw [List.length_map, VExpr.instAllTele_liftTele₀ (n := C'.fields.length)
      (As := T'.indices.map (VExpr.instL us)) (as := ps)] at h3
  simpa [List.map_map, Function.comp_def] using h3

/-- `ctorApp_hasType` at an arbitrary block member. -/
theorem ctorApp_hasType_gen (henv : env.Ordered) (hI : D.IotaCtx env)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {t : Nat} {T' : VIndType} {C' : VIndCtor}
    (hT : D.types[t]? = some T') (hC : C' ∈ T'.ctors) (hCall : (t, C') ∈ D.ctorsAll)
    {Γ ps : List VExpr} (hps : ps.length = D.np)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasType U
      ((VExpr.instAllTele (C'.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      ((VExpr.const C'.name us).mkApp
        (ps.map (·.liftN C'.fields.length) ++ bvars 0 C'.fields.length))
      ((VExpr.const T'.name us).mkApp (ps.map (·.liftN C'.fields.length)
        ++ C'.args.map fun a => VExpr.instAll (a.instL us) ps C'.fields.length)) := by
  have hTD : D.types.getD t default = T' := by rw [List.getD_eq_getElem?_getD, hT]; rfl
  have hR := hI.toRecCtx
  have hCwf : VIndCtor.WF env D t T' C' := hR.ctors t T' hT C' hC
  have h0 := VInductDecl'.ctorApp'_hasType hR hT hC hCall
    (m := 0) (Δ := []) rfl (by simpa using hR.onCtxParams)
  simp only [VExpr.liftTele_zero, List.nil_append, VExpr.liftN_zero, Nat.add_zero] at h0
  have hOn0 : OnCtx (((C'.fields.map (·.type)).reverse ++ D.params.reverse).map (VExpr.instL us))
      (env.IsType U) := OnCtx.instL h7 (hCwf.onCtxAllFields henv)
  simp only [List.map_append, List.map_reverse, List.map_map, Function.comp_def] at hOn0
  rw [← List.reverse_append] at hOn0
  have h1 := VEnv.HasType.instL (U' := U) (ls := D.projLvls C' us 0)
    (VInductDecl'.projLvls_wf h7 0) h0
  rw [List.map_append, List.map_reverse, List.map_reverse,
    VInductDecl'.atRecTele_instL (C := C') h3 0, VInductDecl'.atRecTele_instL (C := C') h3 0,
    ← List.reverse_append, VInductDecl'.atRec_instL (C := C') h3 0] at h1
  simp only [VInductDecl'.ctorApp', VExpr.instL_mkApp, VExpr.instL, VExpr.map_instL_bvars,
    List.map_append, VInductDecl'.selfLvls_projLvls (C := C') h3 0,
    VIndCtor.canonResult, VInductDecl'.tyApp, hTD, VInductDecl'.ownLvls,
    VLevel.params_inst h3, List.map_map, Function.comp_def] at h1
  have h2 := VEnv.IsDefEq.weakR henv (OnCtx.ctxClosed henv hOn0) h1 Γ
  have h3' := VEnv.HasType.instAllUnder henv hpsA h2
  rw [List.length_map] at h3'
  rw [VExpr.instAll_mkApp, VExpr.instAll_const, VExpr.instAll_mkApp, VExpr.instAll_const,
    List.map_append, List.map_append,
    VExpr.map_instAll_bvars_top (Nat.le_refl _) (by simp [hps]),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add _)),
    List.take_of_length_le (by simp [hps])] at h3'
  simpa [List.map_map, Function.comp_def] using h3'

/-- The padding motive's **last** binder — the major premise `T' ps ιs` — with the index
spine substituted.  This is what `VEnv.HasArgs.concat` asks for, and it is exactly
`ctorApp_hasType_gen`'s type. -/
theorem tyBinder_instAll {T' : VIndType} {us : List VLevel} {ps args : List VExpr} {n : Nat}
    (hlen : args.length = T'.indices.length) :
    VExpr.instAll ((VExpr.const T'.name us).mkApp
        ((ps.map (·.liftN n)).map (·.liftN T'.indices.length) ++ bvars 0 T'.indices.length))
      args 0
      = (VExpr.const T'.name us).mkApp (ps.map (·.liftN n) ++ args) := by
  rw [VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    VExpr.map_instAll_bvars_top (Nat.le_refl _) (by omega),
    List.take_of_length_le (by omega)]
  simp only [List.map_map, Function.comp_def, VExpr.liftN_zero]
  congr 1
  congr 1
  · refine List.map_congr_left fun p _ => ?_
    rw [← hlen]
    exact VExpr.instAll_liftN args (p.liftN n) 0
  · simp

/-- **`padMinor_hasType'`'s last premise, discharged at *any* constructor.**

This is item 1 of `docs/handoff-projections.md` §0.4: the padding minor at a **recursive**
constructor.  There is no `C'.recFields = []` hypothesis, and the three pieces are the
general ones:

* `minorTele_gen` splits the minor's telescope into the field block and the
  induction-hypothesis block, so the ambient context is
  `ihΘ.reverse ++ fΘ.reverse ++ Γ` rather than `fΘ.reverse ++ Γ`;
* `minorBodyArgs_gen` says the motive's spine is the non-recursive one weakened by `nr`;
* the two `ctorArgs_hasArgs_gen`/`ctorApp_hasType_gen` facts are moved across that extra
  block by `HasArgs.weakN` at `Ctx.LiftN nr 0` — a **left** (inner) weakening, which is why
  `HasArgs.weakR` is not the tool: `weakR` extends the context on the outside and does not
  shift any index.

The induction-hypothesis telescope itself is never typed here, and does not need to be: the
padding minor binds the ihs and ignores them, so all that is used about `ihΘ` is its
*length*.  `padMinor_hbs_norec` below is the `recFields = []` instance. -/
theorem padMinor_hbs_gen (henv : env.Ordered) (hI : D.IotaCtx env)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {t q : Nat} {T' : VIndType} {C' : VIndCtor} {lvls : List VLevel}
    (hT : D.types[t]? = some T') (hC : C' ∈ T'.ctors) (hCall : (t, C') ∈ D.ctorsAll)
    {Γ ps mots acc : List VExpr}
    (hps : ps.length = D.np)
    (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us)
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasArgs U
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ)
      (VExpr.instAllTele (T'.indices.map (VExpr.instL us))
          (ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length))
        ++ [(VExpr.const T'.name us).mkApp
              ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)).map
                  (·.liftN T'.indices.length)
                ++ bvars 0 T'.indices.length)])
      (D.minorBodyArgs lvls q C' (ps ++ mots ++ acc)) := by
  have hk : ((D.minorBinders q C').map (VExpr.instL lvls)).length
      = (D.ihTypes q C').length + C'.fields.length := D.length_minorBinders_map q C' lvls
  have hal : C'.args.length = T'.indices.length :=
    (hI.toRecCtx.ctors t T' hT C' hC).args_len
  have base : env.HasArgs U
      ((VExpr.instAllTele (C'.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.liftTele C'.fields.length
          (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps)
        ++ [(VExpr.const T'.name us).mkApp
              ((ps.map (·.liftN C'.fields.length)).map (·.liftN T'.indices.length)
                ++ bvars 0 T'.indices.length)])
      ((C'.args.map fun a => VExpr.instAll (a.instL us) ps C'.fields.length)
        ++ [(VExpr.const C'.name us).mkApp
              (ps.map (·.liftN C'.fields.length) ++ bvars 0 C'.fields.length)]) := by
    refine VEnv.HasArgs.concat (ctorArgs_hasArgs_gen henv hI h7 hT hC hpsA) ?_
    rw [tyBinder_instAll (T' := T') (by simpa using hal)]
    exact ctorApp_hasType_gen henv hI h3 h7 hT hC hCall hps hpsA
  have hW : Ctx.LiftN (D.ihTypes q C').length 0
      ((VExpr.instAllTele (C'.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      ((VExpr.instAllTele ((D.ihTypes q C').map (VExpr.instL lvls)) (ps ++ mots ++ acc)
          C'.fields.length).reverse
        ++ ((VExpr.instAllTele (C'.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)) :=
    Ctx.LiftN.zero _ (by simp)
  have hwk := VEnv.HasArgs.weakN henv hW base
  have hni : (VExpr.liftTele C'.fields.length
      (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps)).length
      = T'.indices.length := by simp [VExpr.length_liftTele]
  have eqTele : VExpr.liftTele (D.ihTypes q C').length
      (VExpr.liftTele C'.fields.length
          (VExpr.instAllTele (T'.indices.map (VExpr.instL us)) ps)
        ++ [(VExpr.const T'.name us).mkApp
              ((ps.map (·.liftN C'.fields.length)).map (·.liftN T'.indices.length)
                ++ bvars 0 T'.indices.length)])
      = VExpr.instAllTele (T'.indices.map (VExpr.instL us))
          (ps.map (·.liftN ((D.ihTypes q C').length + C'.fields.length)))
        ++ [(VExpr.const T'.name us).mkApp
              ((ps.map (·.liftN ((D.ihTypes q C').length + C'.fields.length))).map
                  (·.liftN T'.indices.length)
                ++ bvars 0 T'.indices.length)] := by
    rw [VExpr.liftTele_append, VExpr.liftTele_liftTele (Nat.le_refl 0) (Nat.zero_le _),
      Nat.zero_add, hni]
    congr 1
    · rw [← VExpr.liftTele_instAllTele₀ hcl, Nat.add_comm]
    · show [_] = _
      rw [VExpr.liftN_mkApp, VExpr.liftN, List.map_append,
        VExpr.map_liftN_bvars_hi (show 0 + T'.indices.length ≤ T'.indices.length by omega)]
      have hp : ∀ p : VExpr,
          VExpr.liftN (D.ihTypes q C').length
            (VExpr.liftN T'.indices.length (VExpr.liftN C'.fields.length p)) T'.indices.length
          = VExpr.liftN T'.indices.length
              (VExpr.liftN ((D.ihTypes q C').length + C'.fields.length) p) := fun p => by
        rw [VExpr.liftN'_liftN' (Nat.zero_le T'.indices.length) (by omega),
          VExpr.liftN_liftN, VExpr.liftN_liftN]
        congr 1
        omega
      simp only [List.map_map, Function.comp_def, hp]
  rw [D.minorTele_gen hmots hacc hself, List.reverse_append, List.append_assoc,
    D.minorBodyArgs_gen hps hmots hacc hself, hk, ← eqTele]
  exact hwk

/-- **`padMinor_hasType'`'s last premise, discharged at a non-recursive constructor.**

Three named pieces and nothing else: `minorTele_norec` identifies the context,
`minorBodyArgs_norec` the values, and `ctorArgs_hasArgs_gen`/`ctorApp_hasType_gen` type them.
So for a non-recursive block the padding minor is fully proved; what a **recursive** one
still needs is the same three with the induction-hypothesis binders in the way. -/
theorem padMinor_hbs_norec (henv : env.Ordered) (hI : D.IotaCtx env)
    (h3 : us.length = D.uvars) (h7 : ∀ l ∈ us, l.WF U)
    {t q : Nat} {T' : VIndType} {C' : VIndCtor} {lvls : List VLevel}
    (hT : D.types[t]? = some T') (hC : C' ∈ T'.ctors) (hCall : (t, C') ∈ D.ctorsAll)
    {Γ ps mots acc : List VExpr}
    (hrec : C'.recFields = []) (hps : ps.length = D.np)
    (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us)
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length)
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps) :
    env.HasArgs U
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ)
      (VExpr.instAllTele (T'.indices.map (VExpr.instL us))
          (ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length))
        ++ [(VExpr.const T'.name us).mkApp
              ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)).map
                  (·.liftN T'.indices.length)
                ++ bvars 0 T'.indices.length)])
      (D.minorBodyArgs lvls q C' (ps ++ mots ++ acc)) :=
  padMinor_hbs_gen henv hI h3 h7 hT hC hCall hps hmots hacc hself hcl hpsA

/-- **The padding minor is well-typed, at *any* constructor of any block member.**

`padMinor_hasType_norec` with `hrec` removed — the padding minor's whole typing obligation,
recursive constructors included.  Nothing above `hbs` ever needed `recFields = []`:
`padMinor_hasType`, `padMinor_beta` and `padMinor_hasType'` are all stated over
`minorBinders`, which already contains the induction-hypothesis block.

**Scope, precisely.**  This lifts `noRec` for the **padding** minors — the constructors of
block members other than the projected one, whose minor is `fun fields ihs z => z`.  The
projected constructor's own minor is `realMinor`, and it still has no typing lemma at all
(item 2 of `docs/handoff-projections.md` §0.4); `VEnv.IsStructure.noRec` therefore cannot be
dropped yet. -/
theorem padMinor_hasType_gen (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat} (ht : t ≤ D.nm)
    (hT : D.types[t]? = some T') (htlt : t < D.nm)
    {i q : Nat} {C' : VIndCtor} {lvls : List VLevel}
    (hC : C' ∈ T'.ctors) (hCall : (t, C') ∈ D.ctorsAll)
    {Γ ps mots acc ms : List VExpr} {X : VExpr}
    (hself : D.selfLvls.map (VLevel.inst lvls) = us)
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length)
    (hget : mots[t]? = some (D.padMotive T' us ps X))
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hms : ms.length = t)
    (hΓ : OnCtx Γ (env.IsType U))
    (hdecl : env.IsType U Γ
      (VExpr.instAll ((D.minorType q t C').instL lvls) (ps ++ mots ++ acc)))
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hspine : env.HasArgs U
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ)
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)) ++ ms)) :
    env.HasType U Γ (D.padMinor lvls (ps ++ mots ++ acc) X q C')
      (VExpr.instAll ((D.minorType q t C').instL lvls) (ps ++ mots ++ acc)) :=
  padMinor_hasType' (C := C) henv hI h7 hus ht hT htlt hcl hget hps hmots hacc hms hΓ hdecl
    hX hspine
    (padMinor_hbs_gen henv hI hus h7 hT hC hCall hps hmots hacc hself hcl hpsA)

/-- **The padding minor is well-typed, at a non-recursive constructor of any block member.**

This is `docs/handoff-projections.md` §0.5's residual closed, and the whole of `padMinor`'s
typing obligation for a non-recursive block.  The premises that remain are ambient
bookkeeping the consumer already holds: the parameter spine, the declared type, `X`'s typing,
and the motive-prefix spine moved under the minor's own binders.

The only thing a **recursive** constructor changes is that `C'.recFields ≠ []` puts the
induction-hypothesis binders between the fields and the body; `minorTele_norec`,
`minorBodyArgs_norec` and `padMinor_hbs_norec` are the three lemmas that then have to carry a
`liftN nr` through. -/
theorem padMinor_hasType_norec (henv : env.Ordered) (hI : D.IotaCtx env)
    (h7 : ∀ l ∈ us, l.WF U) (hus : us.length = D.uvars) {t : Nat} (ht : t ≤ D.nm)
    (hT : D.types[t]? = some T') (htlt : t < D.nm)
    {i q : Nat} {C' : VIndCtor} {lvls : List VLevel}
    (hC : C' ∈ T'.ctors) (hCall : (t, C') ∈ D.ctorsAll) (hrec : C'.recFields = [])
    {Γ ps mots acc ms : List VExpr} {X : VExpr}
    (hself : D.selfLvls.map (VLevel.inst lvls) = us)
    (hcl : VExpr.ClosedTele (T'.indices.map (VExpr.instL us)) ps.length)
    (hget : mots[t]? = some (D.padMotive T' us ps X))
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hms : ms.length = t)
    (hΓ : OnCtx Γ (env.IsType U))
    (hdecl : env.IsType U Γ
      (VExpr.instAll ((D.minorType q t C').instL lvls) (ps ++ mots ++ acc)))
    (hX : env.HasType U Γ X (.sort (D.elimLvl.inst (D.projLvls C us i))))
    (hpsA : env.HasArgs U Γ (D.params.map (VExpr.instL us)) ps)
    (hspine : env.HasArgs U
      ((VExpr.instAllTele ((D.minorBinders q C').map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ)
      ((D.atRecTele D.params).map (VExpr.instL (D.projLvls C us i))
        ++ ((List.range t).map D.motiveType).map (VExpr.instL (D.projLvls C us i)))
      ((ps.map (·.liftN ((D.minorBinders q C').map (VExpr.instL lvls)).length)) ++ ms)) :
    env.HasType U Γ (D.padMinor lvls (ps ++ mots ++ acc) X q C')
      (VExpr.instAll ((D.minorType q t C').instL lvls) (ps ++ mots ++ acc)) :=
  padMinor_hasType_gen (C := C) henv hI h7 hus ht hT htlt hC hCall hself hcl hget hps hmots
    hacc hms hΓ hdecl hX hpsA hspine

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
