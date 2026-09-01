import Lean4Lean.Verify.Typing.ProjGenBeta
import Lean4Lean.Theory.Inductive.IotaGen

/-!
# The real minor premise, at an arbitrary block member and with recursive fields

`VIndCtor.projMinor` binds the constructor's **fields** and returns field `i`;
`VInductDecl'.realMinor` (`ProjGen.lean`) binds the fields *and the induction hypotheses*
and returns the same field, now at de Bruijn index `nf + nr - 1 - i`.  That extra `nr` is
what `docs/handoff-projections.md` §0.7 item 1(c) calls "the field-variable lookup through
the ih block".

**The ih block factors out by weakening.**  `minorTele_gen` splits the minor's binder
telescope as `ΘF ++ ΘI` with `ΘF` *exactly* the field telescope `projMinor` binds — so the
minor's own context is the narrow one with `nr` further binders on top — and
`minorBodyArgs_gen` says the declared body's spine is the narrow spine weakened by `nr`.
Both sides of the judgement are therefore `liftN nr 0` of the narrow ones, and
`VEnv.HasType.weakN` carries the narrow statement across.

So ingredient (c) is **not** a re-run of `projMinor_hasType`'s strong induction with a
bigger telescope: the `nr` generalisation is a weakening, and the residual is the *block
index* generalisation of the ι-law/swap chain, which is a different axis.  See
`realMinor_hasType_gen` and the correction recorded at `docs/handoff-projections.md` §0*.1.

What is left is `realMinor_hasType_gen'`'s `hiota` premise, and it mentions neither `nr` nor
`q` nor `ihTypes` — see `docs/handoff-projections.md` §0*.7 item 1.

## `realMinor_app`, added 2026-09-01

`docs/handoff-projections.md` §0**.7 item 2 named `realMinor_app` as open and it was: the
name occurred nowhere in the tree as a declaration.  (§0**.1's left column calls the same
row `projMinor_app`, which **is** proved, in `Theory/Inductive/StructureClosed.lean` — the
row is about its *real-minor* counterpart.)  It is now below, together with
`projMinor_app_of_realMinor_app`, the collapse test that recovers `projMinor_app`'s statement
hypothesis for hypothesis at `C.recFields = []`.

It needed no induction and no `IsStructure`: the ih block is simply the tail of the spine
that `instAll_bvar_get` walks past, so the field lookup is the same one `projMinor_app` does
at a longer substitution.  Axioms `[propext, Quot.sound]`, cone 2088, **no holes** — the same
set as `projMinor_app`'s (cone 2034).

The import of `Theory/Inductive/IotaGen.lean` above is deliberate and is not used by any
proof in this file yet: it is what puts that file — the general ι law, this cluster's other
open lemma — inside `Lean4Lean/Experimental/ConeJoin.lean`'s closure, which this module
already sits in.  Without it both census instruments would be blind to a new leaf.
-/

namespace Lean4Lean

open VExpr

variable {env : VEnv} {U : Nat} {D : VInductDecl'} {T : VIndType} {C : VIndCtor}
  {us : List VLevel}

namespace VInductDecl'

/-- **The field-variable lookup itself**, at an arbitrary block member.

`projMinor_hasType`'s `hrgt` (`Verify/Typing/Lemmas.lean`) at `ProjClosedG` instead of
`ProjClosed`: variable `nf - 1 - i` of the field telescope has field `i`'s stored type with
the parameters and the *earlier field variables* substituted.  No `IsStructure`, no
`Ordered`, no induction — it is `Lookup.tele_getElem` plus the closedness bound. -/
theorem realMinor_field_hasType (H : D.ProjClosedG) {j : Nat}
    (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors) {i : Nat} (hi : i < C.fields.length)
    {Γ ps : List VExpr} (hps : ps.length = D.np) :
    env.HasType U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (.bvar (C.fields.length - 1 - i))
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m))) := by
  have hbv : ((List.range i).map fun m => (VExpr.bvar (C.fields.length - 1 - m)))
      = bvars (C.fields.length - i) i := by
    rw [VExpr.bvars_eq_map_range]
    refine List.map_congr_left fun m hm => ?_
    simp only [List.mem_range] at hm
    congr 1
    omega
  rw [hbv, VExpr.instAll_split_bvars (by omega)
    (by simpa [hps, Nat.add_comm] using H.ftype_closedN hTj hC hi)]
  have hb := Lookup.tele_getElem
    (As := VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps) (Γ := Γ) (i := i)
    (by simp [hi])
  rw [VExpr.length_instAllTele, List.length_map, instAllTele_getD (by simp [hi]),
    Nat.zero_add, fields_getD_map hi] at hb
  exact .bvar hb

/-- **The real minor is typed by its narrow core, weakened past the induction hypotheses.**

`hcore` is the narrow judgement: in the *field* telescope's own context, the field variable
`.bvar (nf - 1 - i)` has the declared body's narrow form, motive `P` weakened past the
fields and applied to the constructor's result indices and the constructor itself.  That is
literally the goal `projMinor_hasType` reaches after `HasType.mkLams`, and everything the
induction hypotheses contribute is discharged here.

No `IsStructure`, no `noRec`: `q`, `j` and the recursive fields are all arbitrary. -/
theorem realMinor_hasType_gen (henv : env.Ordered)
    {lvls : List VLevel} {i q j : Nat} {P : VExpr} {Γ ps mots acc : List VExpr}
    (hself : D.selfLvls.map (VLevel.inst lvls) = us)
    (hget : mots[j]? = some P)
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hjlt : j < D.nm) (hi : i < C.fields.length)
    (hΓ : OnCtx Γ (env.IsType U))
    (hdecl : env.IsType U Γ
      (VExpr.instAll ((D.minorType q j C).instL lvls) (ps ++ mots ++ acc)))
    (hcore : env.HasType U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (.bvar (C.fields.length - 1 - i))
      ((P.liftN C.fields.length).mkApp
        ((C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
          ++ [(VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)]))) :
    env.HasType U Γ (D.realMinor lvls (ps ++ mots ++ acc) i q C)
      (VExpr.instAll ((D.minorType q j C).instL lvls) (ps ++ mots ++ acc)) := by
  have hK : ((D.minorBinders q C).map (VExpr.instL lvls)).length
      = (D.ihTypes q C).length + C.fields.length := D.length_minorBinders_map q C lvls
  have hΘ := D.minorTele_gen (lvls := lvls) (us := us) (q := q) (C := C) (ps := ps)
    (mots := mots) (acc := acc) hmots hacc hself
  have hsplit : VExpr.instAll ((D.minorType q j C).instL lvls) (ps ++ mots ++ acc)
      = VExpr.mkPi
          (VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls))
            (ps ++ mots ++ acc))
          (VExpr.instAll ((D.minorBody q j C).instL lvls) (ps ++ mots ++ acc)
            ((D.minorBinders q C).map (VExpr.instL lvls)).length) := by
    rw [D.minorType_eq_mkPi q j C, VExpr.instL_mkPi, VExpr.instAll_mkPi, Nat.zero_add]
  rw [hsplit] at hdecl ⊢
  obtain ⟨hOn, -⟩ := VEnv.IsType.mkPi_inv henv hΓ hdecl
  rw [D.minorBody_instAll_spine hget hps hmots hacc hjlt,
    D.minorBodyArgs_gen hps hmots hacc hself]
  show env.HasType U Γ (VExpr.mkLams
      (VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) (ps ++ mots ++ acc))
      (.bvar ((VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).length - 1 - i))) _
  refine VEnv.HasType.mkLams hOn ?_
  -- the minor's context is the field telescope's context with the ih block on top
  have hlenI : (VExpr.instAllTele ((D.ihTypes q C).map (VExpr.instL lvls))
      (ps ++ mots ++ acc) C.fields.length).reverse.length = (D.ihTypes q C).length := by
    simp
  have hctx : (VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ
      = (VExpr.instAllTele ((D.ihTypes q C).map (VExpr.instL lvls))
          (ps ++ mots ++ acc) C.fields.length).reverse
        ++ ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ) := by
    rw [hΘ, List.reverse_append, List.append_assoc]
  have hW : Ctx.LiftN (D.ihTypes q C).length 0
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      ((VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).reverse ++ Γ) := by
    rw [hctx]
    exact Ctx.LiftN.zero _ hlenI
  have hw := VEnv.HasType.weakN henv hW hcore
  rw [VExpr.liftN_mkApp, VExpr.liftN_liftN] at hw
  have hbvar : VExpr.liftN (D.ihTypes q C).length (VExpr.bvar (C.fields.length - 1 - i))
      = VExpr.bvar ((VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls))
          (ps ++ mots ++ acc)).length - 1 - i) := by
    have : (VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls))
        (ps ++ mots ++ acc)).length = (D.ihTypes q C).length + C.fields.length := by
      rw [VExpr.length_instAllTele, hK]
    rw [this]
    simp only [VExpr.liftN, liftVar_base']
    congr 1
    omega
  rw [hbvar] at hw
  have hP : VExpr.liftN (C.fields.length + (D.ihTypes q C).length) P
      = VExpr.liftN ((D.minorBinders q C).map (VExpr.instL lvls)).length P := by
    rw [hK, Nat.add_comm]
  rw [hP] at hw
  exact hw

/-- **`realMinor_hasType_gen` with the field-variable lookup discharged.**

What is left is a single defeq at the *conclusion*: the field's stored type, with the
parameters and the earlier **field variables** substituted, against the declared body — the
real motive weakened past the fields and applied to the constructor's result indices and the
constructor itself.  That is exactly the ι-law/swap step of `projMinor_hasType`
(`Verify/Typing/Lemmas.lean`, its `hbetaQ`/`hcong`), and it is a statement about the *block
index*, not about the induction hypotheses: `nr` does not occur in it. -/
theorem realMinor_hasType_gen' (henv : env.Ordered) (H : D.ProjClosedG)
    {lvls : List VLevel} {i q j : Nat} {P : VExpr} {ℓ : VLevel} {Γ ps mots acc : List VExpr}
    (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us)
    (hget : mots[j]? = some P)
    (hps : ps.length = D.np) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hjlt : j < D.nm) (hi : i < C.fields.length)
    (hΓ : OnCtx Γ (env.IsType U))
    (hdecl : env.IsType U Γ
      (VExpr.instAll ((D.minorType q j C).instL lvls) (ps ++ mots ++ acc)))
    (hiota : env.IsDefEq U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m)))
      ((P.liftN C.fields.length).mkApp
        ((C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
          ++ [(VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)]))
      (.sort ℓ)) :
    env.HasType U Γ (D.realMinor lvls (ps ++ mots ++ acc) i q C)
      (VExpr.instAll ((D.minorType q j C).instL lvls) (ps ++ mots ++ acc)) :=
  D.realMinor_hasType_gen henv hself hget hps hmots hacc hjlt hi hΓ hdecl
    (VEnv.IsDefEq.defeqDF hiota (D.realMinor_field_hasType H hTj hC hi hps))

/-! ## Compatibility, and the consumer -/

/-- At a non-recursive constructor the real minor **is** `projMinor` — the ih block is empty
and the body's index collapses.  The analogue of `minorTele_narrow`, and what makes
`realMinor_hasType_gen` a generalisation of `projMinor_hasType`'s conclusion rather than a
different statement. -/
theorem realMinor_norec {lvls : List VLevel} {i q : Nat} {ps mots acc : List VExpr}
    (hrec : C.recFields = []) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us) :
    D.realMinor lvls (ps ++ mots ++ acc) i q C = C.projMinor us ps i := by
  show VExpr.mkLams (VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls))
      (ps ++ mots ++ acc)) _ = _
  rw [D.minorTele_norec hrec hmots hacc hself, VIndCtor.projMinor]
  simp

/-- **The consumer, written out.**  `projCoreG`'s minor block puts `realMinor` at the
projected constructor's position, with `lvls = D.projLvls C us i` and the motive block
`D.padMotives`; `hget`, `hmots` and `hself` are all discharged there, so none of them can be
an assumption the block builder is unable to meet.

Written before the statement above was trusted: the sibling `padMinor_hasType'` carries
`hcl`/`hms`/`hspine` premises that this cut cannot supply in the same form, and copying them
across by analogy would have been unusable here. -/
theorem realMinor_hasType_atPadMotives (henv : env.Ordered) (H : D.ProjClosedG)
    {i q j : Nat} {ℓ : VLevel} {Γ ps is acc earlier : List VExpr} {e : VExpr}
    (hTj : D.types[j]? = some T) (hC : C ∈ T.ctors)
    (hus : us.length = D.uvars)
    (hps : ps.length = D.np) (hacc : acc.length = q)
    (hjlt : j < D.nm) (hi : i < C.fields.length)
    (hΓ : OnCtx Γ (env.IsType U))
    (hdecl : env.IsType U Γ
      (VExpr.instAll ((D.minorType q j C).instL (D.projLvls C us i))
        (ps ++ D.padMotives T C us ps is i j earlier e ++ acc)))
    (hiota : env.IsDefEq U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (VExpr.instAll ((C.fields.getD i default).type.instL us)
        (ps.map (·.liftN C.fields.length)
          ++ (List.range i).map fun m => VExpr.bvar (C.fields.length - 1 - m)))
      (((T.projMotive C us ps is i earlier).liftN C.fields.length).mkApp
        ((C.args.map fun a => VExpr.instAll (a.instL us) ps C.fields.length)
          ++ [(VExpr.const C.name us).mkApp
                (ps.map (·.liftN C.fields.length) ++ bvars 0 C.fields.length)]))
      (.sort ℓ)) :
    env.HasType U Γ
      (D.realMinor (D.projLvls C us i)
        (ps ++ D.padMotives T C us ps is i j earlier e ++ acc) i q C)
      (VExpr.instAll ((D.minorType q j C).instL (D.projLvls C us i))
        (ps ++ D.padMotives T C us ps is i j earlier e ++ acc)) := by
  have hself : D.selfLvls.map (VLevel.inst (D.projLvls C us i)) = us := by
    rw [VInductDecl'.projLvls]; exact D.selfLvls_inst _ hus
  exact D.realMinor_hasType_gen' henv H hTj hC hself
    (D.padMotives_getElem_eq T C us ps is i j earlier e hjlt) hps
    (D.length_padMotives T C us ps is i j earlier e) hacc hjlt hi hΓ hdecl hiota


end VInductDecl'


/-- **`projMinor_app` for the real minor**: the minor premise
`fun f₀ … f_{nf-1} ih₀ … ih_{nr-1} => fᵢ` applied to a fields-and-ih spine β-reduces to field
`i`. -/
theorem VInductDecl'.realMinor_app (henv : env.Ordered)
    {lvls : List VLevel} {i q : Nat} {Γ spine fs ihs : List VExpr} {B : VExpr}
    (hi : i < C.fields.length) (hfs : fs.length = C.fields.length)
    (hOn : OnCtx
      ((VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) spine).reverse ++ Γ)
      (env.IsType U))
    (hA : env.HasArgs U Γ
      (VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) spine) (fs ++ ihs))
    (hb : env.HasType U
      ((VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) spine).reverse ++ Γ)
      (.bvar ((VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) spine).length
        - 1 - i)) B) :
    env.IsDefEq U Γ ((D.realMinor lvls spine i q C).mkApp (fs ++ ihs)) (fs.getD i default)
      (VExpr.instAll B (fs ++ ihs)) := by
  have hΘ : (VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) spine).length
      = (D.ihTypes q C).length + C.fields.length := by
    rw [VExpr.length_instAllTele, D.length_minorBinders_map q C lvls]
  have hlen : (fs ++ ihs).length
      = (VExpr.instAllTele ((D.minorBinders q C).map (VExpr.instL lvls)) spine).length :=
    hA.length_eq.symm
  have hget : (fs ++ ihs)[i]? = some (fs.getD i default) := by
    rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < fs.length by omega)]
  have h := VEnv.IsDefEq.betaMkLams henv hOn hA hb
  rw [VExpr.instAll_bvar_get hget (by omega)] at h
  simpa [VInductDecl'.realMinor] using h

/-- **Collapse test: `projMinor_app` is `realMinor_app` at no recursive fields.**
`projMinor_app`'s statement (`Theory/Inductive/StructureClosed.lean`), hypothesis for
hypothesis, derived from `realMinor_app` with `ihs = []`. -/
theorem VInductDecl'.projMinor_app_of_realMinor_app {env : VEnv} {U : Nat}
    {D : VInductDecl'} {C : VIndCtor} (henv : env.Ordered)
    {us lvls : List VLevel} {i q : Nat} {Γ ps mots acc fs : List VExpr} {B : VExpr}
    (hrec : C.recFields = []) (hmots : mots.length = D.nm) (hacc : acc.length = q)
    (hself : D.selfLvls.map (VLevel.inst lvls) = us)
    (hi : i < C.fields.length) (hfs : fs.length = C.fields.length)
    (hOn : OnCtx
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (env.IsType U))
    (hA : env.HasArgs U Γ (VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps) fs)
    (hb : env.HasType U
      ((VExpr.instAllTele (C.fields.map fun F => F.type.instL us) ps).reverse ++ Γ)
      (.bvar (C.fields.length - 1 - i)) B) :
    env.IsDefEq U Γ ((C.projMinor us ps i).mkApp fs) (fs.getD i default)
      (VExpr.instAll B fs) := by
  have hT := D.minorTele_norec (us := us) (ps := ps) (C := C) hrec hmots hacc hself
  have hih : D.ihTypes q C = [] := by simp [VInductDecl'.ihTypes, hrec]
  have h := D.realMinor_app (lvls := lvls) (spine := ps ++ mots ++ acc) (ihs := [])
    (Γ := Γ) (B := B) henv hi hfs (by rw [hT]; exact hOn) (by rw [hT]; simpa using hA)
    (by rw [hT]; simpa [VExpr.length_instAllTele, D.length_minorBinders_map q C lvls, hih]
          using hb)
  rw [D.realMinor_norec (us := us) hrec hmots hacc hself] at h
  simpa using h


end Lean4Lean
