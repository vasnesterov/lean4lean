import Lean4Lean.Theory.Inductive.Lemmas

/-!
# The recursor applied to a concrete spine, at an arbitrary universe instantiation

`VInductDecl'.recApp_hasType'` (`Theory/Inductive/Lemmas.lean`) types a recursor application
whose parameter/motive/minor blocks are arbitrary terms rather than canonical-context
`bvars`, but it lives entirely inside the recursor's own universe world: the head carries
`VLevel.params D.recUvars`, the ambient universe count *is* `D.recUvars`, and the telescopes
are read at `D.selfLvls`.

A refinement-layer consumer does not live there.  `VInductDecl'.projCore`
(`Theory/Inductive/Structure.lean`) builds

```
S.rec.{ℓ, us} ps mot minor ι e
```

at the *use site's* levels `us`, in an ambient context `Γ` at some unrelated `U`.  Its
`hspine` obligation therefore has to be stated against the recursor's telescopes moved to
`ls`, not against `D.motives`/`D.minors` at `selfLvls` — which is unstateable for such a
consumer.

`recApp_hasType''` below is that version.  It is *simpler* than the primed one, not harder:
`HasType.const` delivers the head at any `Γ` and any `U` directly, so the `const0` +
weakening + closedness dance disappears, and the recursor's codomain contains only `bvar`s,
so `instL` fixes it outright.

This file exists rather than an edit to `Theory/Inductive/Lemmas.lean` because that file is
imported by two streams and has been the build contention point; nothing here needs to be
there.
-/

namespace Lean4Lean

open VExpr (mkPi mkLams mkApp bvars liftTele instTele shift shiftTele instAll instAllTele)

namespace VInductDecl'
variable {env : VEnv} {D : VInductDecl'}

/-- `VInductDecl'.tyApp'` with the head constant's level list left free.  `tyApp'` is the
instance at `D.selfLvls`; a use site needs it at `D.selfLvls.map (·.inst ls)`. -/
def tyAppL (D : VInductDecl') (nm : Lean.Name) (lvls : List VLevel) (K : Nat)
    (args : List VExpr) : VExpr :=
  (VExpr.const nm lvls).mkApp (bvars K D.np ++ args)

theorem tyApp'_eq_tyAppL (D : VInductDecl') (j K : Nat) (args : List VExpr) :
    D.tyApp' j K args = D.tyAppL (D.types.getD j default).name D.selfLvls K args := rfl

theorem tyAppL_instL (D : VInductDecl') (nm : Lean.Name) (lvls : List VLevel) (K : Nat)
    (args : List VExpr) {ls : List VLevel} :
    (D.tyAppL nm lvls K args).instL ls
      = D.tyAppL nm (lvls.map (VLevel.inst ls)) K (args.map (VExpr.instL ls)) := by
  simp [VInductDecl'.tyAppL, VExpr.instL]

/-- The level-generic form of `tyApp'_instAll_spine`: the major premise's type, once the
parameter/motive/minor block and then the index terms have been substituted. -/
theorem tyAppL_instAll_spine (D : VInductDecl') {nm : Lean.Name} {lvls : List VLevel}
    {ni : Nat} {ps rest ιs : List VExpr}
    (hps : ps.length = D.np) (hrest : rest.length = D.nm + D.nmin) (hlen : ιs.length = ni) :
    VExpr.instAll
        (VExpr.instAll (D.tyAppL nm lvls (ni + D.nmin + D.nm) (bvars 0 ni)) (ps ++ rest) ni)
        ιs 0
      = (VExpr.const nm lvls).mkApp (ps ++ ιs) := by
  have hcancel : ∀ x : VExpr, VExpr.instAll (x.liftN ni 0) ιs 0 = x := by
    intro x; rw [← hlen]; exact VExpr.instAll_liftN ιs x 0
  rw [VInductDecl'.tyAppL, VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    VExpr.map_instAll_bvars_top (by omega)
      (by rw [List.length_append, hps, hrest]; omega),
    VExpr.map_instAll_bvars_lt (Nat.le_of_eq (Nat.zero_add ni)),
    List.take_left' hps, VExpr.instAll_mkApp, VExpr.instAll_const, List.map_append,
    List.map_map, VExpr.map_instAll_bvars' hlen]
  simp only [Function.comp_def, hcancel, List.map_id']

/-- **The recursor applied to a concrete spine, at an arbitrary universe instantiation.**

Everything a consumer must supply is stated at *its* levels `ls` and *its* ambient universe
count `U`:

* `hspine` — the parameters, motives and minors instantiate the recursor's first three
  telescope blocks, moved to `ls`.  This is where "this term inhabits the motive's binder
  type" enters; the spec side only says those binder types *are* types
  (`motiveType_isType`, `minorType_isType`).
* `hidx` — the index terms, against the index telescope with the spine already substituted.
  For a block with no indices (every `structure`) this is `HasArgs U Γ [] []`, i.e. `.nil`.
* `he` — the major premise inhabits `I_u.{ls'} ps ιs`, where `ls'` is the block's own level
  list moved to `ls`.

The environment interface is `D.IotaCtx env`, which `addInduct'` produces
(`VInductDecl'.WF.iotaCtx`).

Note there is no `mkLams` to peel here: `projCore` emits the recursor already applied, so
the caller's only residual obligation is re-associating `ps ++ [mot, minor] ++ is ++ [e]`
into the shape below. -/
theorem recApp_hasType'' (hI : D.IotaCtx env) {u U : Nat} {T' : VIndType}
    (hT' : D.types[u]? = some T') (hu : u < D.nm)
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlslen : ls.length = D.recUvars)
    {Γ ps ms mins ιs : List VExpr} {e mot : VExpr}
    (hps : ps.length = D.np) (hms : ms.length = D.nm) (hmins : mins.length = D.nmin)
    (hspine : env.HasArgs U Γ
      (((D.atRecTele D.params).map (VExpr.instL ls) ++ D.motives.map (VExpr.instL ls))
        ++ D.minors.map (VExpr.instL ls))
      (ps ++ (ms ++ mins)))
    (hmot : ms[u]? = some mot)
    (hlen : ιs.length = T'.indices.length)
    (hidx : env.HasArgs U Γ
      (VExpr.instAllTele
        (liftTele (D.nm + D.nmin) ((D.atRecTele T'.indices).map (VExpr.instL ls)))
        (ps ++ (ms ++ mins)) 0) ιs)
    (he : env.HasType U Γ e
      ((VExpr.const T'.name (D.selfLvls.map (VLevel.inst ls))).mkApp (ps ++ ιs))) :
    env.HasType U Γ
      ((VExpr.const (Lean.mkRecName T'.name) ls).mkApp (ps ++ (ms ++ mins) ++ (ιs ++ [e])))
      (mot.mkApp (ιs ++ [e])) := by
  -- the head, directly at `Γ` and `U`
  have hrec0 := VEnv.HasType.const (Γ := Γ) (hI.recConsts u T' hT') hls (by simpa using hlslen)
  rw [VInductDecl'.recType, getD_types hT'] at hrec0
  -- distribute `instL ls`, and split the telescope after the minors
  have hrec1 : env.HasType U Γ (.const (Lean.mkRecName T'.name) ls)
      (mkPi (((D.atRecTele D.params).map (VExpr.instL ls) ++ D.motives.map (VExpr.instL ls))
          ++ D.minors.map (VExpr.instL ls))
        (mkPi (liftTele (D.nm + D.nmin) ((D.atRecTele T'.indices).map (VExpr.instL ls))
            ++ [D.tyAppL T'.name (D.selfLvls.map (VLevel.inst ls))
                (T'.indices.length + D.nmin + D.nm) (bvars 0 T'.indices.length)])
          ((VExpr.bvar (1 + T'.indices.length + D.nmin + (D.nm - 1 - u))).mkApp
            (bvars 1 T'.indices.length ++ [VExpr.bvar 0])))) := by
    simp only [VExpr.instL_mkPi, List.map_append, VExpr.instL_liftTele, VExpr.mkPi_append,
      VExpr.mkPi_cons, VExpr.mkPi_nil, VExpr.instL, VInductDecl'.tyApp'_eq_tyAppL,
      VInductDecl'.tyAppL_instL, VExpr.instL_mkApp, VExpr.map_instL_bvars, List.map_cons,
      List.map_nil, getD_types hT'] at hrec0 ⊢
    exact hrec0
  have h1 := VEnv.HasType.mkApp' hspine hrec1
  rw [VExpr.instAll_mkPi, VExpr.instAllTele_append, VExpr.length_liftTele, List.length_map,
    VInductDecl'.length_atRecTele, Nat.zero_add, List.length_append, VExpr.length_liftTele,
    List.length_map, VInductDecl'.length_atRecTele, List.length_cons, List.length_nil] at h1
  -- the major premise, at the substituted domain
  have he' : env.HasType U Γ e
      (VExpr.instAll (VExpr.instAll
        (D.tyAppL T'.name (D.selfLvls.map (VLevel.inst ls))
          (T'.indices.length + D.nmin + D.nm) (bvars 0 T'.indices.length))
        (ps ++ (ms ++ mins)) T'.indices.length) ιs 0) := by
    rw [D.tyAppL_instAll_spine hps (by rw [List.length_append, hms, hmins]) hlen]
    exact he
  have hfinal := VEnv.HasType.mkApp' (VEnv.HasArgs.concat hidx he') h1
  rw [← VExpr.mkApp_append] at hfinal
  simp only [Nat.zero_add] at hfinal
  -- the codomain: `instL` fixes it (only `bvar`s), so this is `recApp_hasType'` verbatim
  have hz : (ιs ++ [e]).length = T'.indices.length + 1 := by
    rw [List.length_append, hlen]; rfl
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
end Lean4Lean
