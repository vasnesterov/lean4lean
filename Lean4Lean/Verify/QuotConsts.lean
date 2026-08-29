import Lean4Lean.Verify.InductFlip
import Lean4Lean.Theory.Typing.Meta

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ## 1. The four stored types, as closed literals -/

/-- `α → α → Prop`, with `α` the outermost binder. -/
def rTypeE : Expr :=
  .forallE `a (.bvar 0) (.forallE `a (.bvar 1) (.sort .zero) .default) .default

def quotTypeE : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r rTypeE (.sort (.param `u)) .default) .implicit

def quotMkTypeE : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r rTypeE
      (.forallE `a (.bvar 1)
        (.app (.app (.const ``Quot [.param `u]) (.bvar 2)) (.bvar 1)) .default) .default)
    .implicit

def quotLiftTypeE : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r rTypeE
      (.forallE `β (.sort (.param `v))
        (.forallE `f (.forallE `a (.bvar 2) (.bvar 1) .default)
          (.forallE `a
            (.forallE `a (.bvar 3)
              (.forallE `b (.bvar 4)
                (.forallE `a (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const ``Eq [.param `v]) (.bvar 4))
                    (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1))) .default)
                .default) .default)
            (.forallE `a (.app (.app (.const ``Quot [.param `u]) (.bvar 4)) (.bvar 3))
              (.bvar 3) .default) .default)
          .default) .implicit) .implicit) .implicit

def quotIndTypeE : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r rTypeE
      (.forallE `β
        (.forallE `a (.app (.app (.const ``Quot [.param `u]) (.bvar 1)) (.bvar 0))
          (.sort .zero) .default)
        (.forallE `mk
          (.forallE `a (.bvar 2)
            (.app (.bvar 1)
              (.app (.app (.app (.const ``Quot.mk [.param `u]) (.bvar 3)) (.bvar 2)) (.bvar 0)))
            .default)
          (.forallE `q (.app (.app (.const ``Quot [.param `u]) (.bvar 3)) (.bvar 2))
            (.app (.bvar 2) (.bvar 0)) .implicit) .default) .implicit) .implicit) .implicit


/-- The four `ConstantInfo`s `addQuot` installs. -/
def quotCI : ConstantInfo :=
  .quotInfo { name := ``Quot, kind := .type, levelParams := [`u], type := quotTypeE }
def quotMkCI : ConstantInfo :=
  .quotInfo { name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := quotMkTypeE }
def quotLiftCI : ConstantInfo :=
  .quotInfo { name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := quotLiftTypeE }
def quotIndCI : ConstantInfo :=
  .quotInfo { name := ``Quot.ind, kind := .ind, levelParams := [`u], type := quotIndTypeE }

/-! ## 2. `TrExprS` for the four stored types -/

syntax "tr_tac" : tactic
macro_rules | `(tactic| tr_tac) => `(tactic|
  first
  | exact TrExprS.sort rfl
  | exact TrExprS.bvar rfl
  | exact TrExprS.const (by assumption) rfl rfl
  | refine TrExprS.forallE ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ ?_ <;>
      [skip; type_tac; skip; type_tac; tr_tac; tr_tac]
  | refine TrExprS.app (A := ?_) (B := ?_) ?_ ?_ ?_ ?_ <;>
      [skip; skip; type_tac; type_tac; tr_tac; tr_tac]
)

theorem trExprS_quotType {venv : VEnv} :
    TrExprS venv [`u] [] quotTypeE quotConst.type := by
  simp only [quotTypeE, rTypeE, quotConst]
  refine TrExprS.forallE ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ ?_ <;>
    [skip; type_tac; skip; type_tac; tr_tac; skip]
  refine TrExprS.forallE ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ ?_ <;>
    [skip; type_tac; skip; type_tac; tr_tac; tr_tac]

theorem trExprS_quotMkType {venv : VEnv}
    (hQuot : venv.constants ``Quot = some quotConst) :
    TrExprS venv [`u] [] quotMkTypeE quotMkConst.type := by
  simp only [quotMkTypeE, rTypeE, quotMkConst]
  tr_tac

theorem trExprS_quotLiftType {venv : VEnv}
    (hQuot : venv.constants ``Quot = some quotConst)
    (hEq : venv.constants ``Eq = some eqConst) :
    TrExprS venv [`u, `v] [] quotLiftTypeE quotLiftConst.type := by
  simp only [quotLiftTypeE, rTypeE, quotLiftConst]
  tr_tac

theorem trExprS_quotIndType {venv : VEnv}
    (hQuot : venv.constants ``Quot = some quotConst)
    (hQuotMk : venv.constants ``Quot.mk = some quotMkConst) :
    TrExprS venv [`u] [] quotIndTypeE quotIndConst.type := by
  simp only [quotIndTypeE, rTypeE, quotIndConst]
  tr_tac


/-! ## 3. `mkForall` over the local contexts `addQuot` builds -/

open Lean4Lean.LocalContext in
/-- `mkForall` over a list of `cdecl`-bound free variables, as a `foldr`.  This is
`mkBinding_eq` composed with `mkBindingList_eq_fold`; `mkForall_single`
(`Verify/InductFlip.lean`) is its one-binder instance. -/
theorem _root_.Lean4Lean.LocalContext.mkForall_list {lctx : LocalContext} {xs : List FVarId}
    {b : Expr} (hb : b.looseBVarRange' = 0) (hnd : xs.Nodup)
    (hlc : ∀ x ∈ xs, ∀ d, lctx.find? x = some d →
      d.type.looseBVarRange' = 0 ∧ ∀ v ∈ d.value? true, v.looseBVarRange' = 0)
    (hex : ∀ x ∈ xs, ∃ d, lctx.find? x = some d) :
    lctx.mkForall ⟨xs.map (.fvar ·)⟩ b =
      xs.foldr (fun a e => mkBindingList1 false lctx [] a (e.abstract1 a)) b := by
  show mkBinding false lctx ⟨xs.map (.fvar ·)⟩ b = _
  rw [mkBinding_eq hb hnd hlc, mkBindingList_eq_fold hex hnd]

theorem _root_.Lean4Lean.LocalContext.find?_mkLocalDecl {lctx : LocalContext} {fv fv' : FVarId}
    {n ty bi k} (hwf : lctx.WF) (hn : lctx.find? fv' = none) :
    (lctx.mkLocalDecl fv' n ty bi k).find? fv =
      if fv == fv' then some (.cdecl lctx.decls.size fv' n ty bi k) else lctx.find? fv := by
  rw [(hwf.mkLocalDecl hn).find?_eq_find?_toList,
    LocalContext.mkLocalDecl_toList, List.find?_cons,
    hwf.find?_eq_find?_toList]
  simp [Lean.LocalDecl.fvarId]
  split <;> simp_all


/-- One `withLocalDecl` binder, as data: free variable, user name, type, binder info. -/
abbrev BinderData := FVarId × Name × Expr × BinderInfo

/-- The local context produced by a chain of `withLocalDecl`s, innermost first. -/
def ofDecls : List BinderData → LocalContext
  | [] => {}
  | d :: ds => (ofDecls ds).mkLocalDecl d.1 d.2.1 d.2.2.1 d.2.2.2

theorem ofDecls_wf_find?_none : ∀ {ds : List BinderData}, (ds.map (·.1)).Nodup →
    (ofDecls ds).WF ∧ ∀ fv, fv ∉ ds.map (·.1) → (ofDecls ds).find? fv = none
  | [], _ => ⟨LocalContext.wf_empty, fun _ _ => LocalContext.find?_empty⟩
  | d :: ds, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨ih1, ih2⟩ := ofDecls_wf_find?_none hnd.2
    have hd := ih2 d.1 hnd.1
    refine ⟨ih1.mkLocalDecl hd, fun fv hfv => ?_⟩
    rw [List.map_cons, List.mem_cons] at hfv
    show (ofDecls (d :: ds)).find? fv = none
    rw [ofDecls, LocalContext.find?_mkLocalDecl ih1 hd,
      if_neg (by simpa using fun h => hfv (.inl h))]
    exact ih2 fv fun h => hfv (.inr h)

theorem ofDecls_wf {ds : List BinderData} (hnd : (ds.map (·.1)).Nodup) : (ofDecls ds).WF :=
  (ofDecls_wf_find?_none hnd).1

theorem find?_ofDecls : ∀ {ds : List BinderData}, (ds.map (·.1)).Nodup →
    ∀ {d : BinderData}, d ∈ ds →
    ∃ i, (ofDecls ds).find? d.1 = some (.cdecl i d.1 d.2.1 d.2.2.1 d.2.2.2 .default)
  | [], _, _, h => nomatch h
  | d₀ :: ds, hnd, d, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨ih1, ih2⟩ := ofDecls_wf_find?_none hnd.2
    have hd := ih2 d₀.1 hnd.1
    show ∃ i, (ofDecls (d₀ :: ds)).find? d.1 = some _
    rw [ofDecls, LocalContext.find?_mkLocalDecl ih1 hd]
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨(ofDecls ds).decls.size, by simp⟩
    · rw [if_neg (by
        simp only [beq_iff_eq]
        intro he
        exact hnd.1 (he ▸ List.mem_map.2 ⟨d, h, rfl⟩))]
      exact find?_ofDecls hnd.2 h

open Lean.LocalContext in
/-- **The `mkForall` a `withLocalDecl` chain computes**, as a `foldr` over the abstracted
binders.  `xs` is the (ordered, duplicate-free) sublist of the context's binders that is being
abstracted; every binder type in the context must be closed, which they are because each is
built from earlier free variables and constants. -/
theorem mkForall_ofDecls {ds xs : List BinderData} {b : Expr}
    (hnd : (ds.map (·.1)).Nodup) (hxnd : (xs.map (·.1)).Nodup) (hsub : ∀ x ∈ xs, x ∈ ds)
    (hb : b.looseBVarRange' = 0) (hcl : ∀ d ∈ ds, d.2.2.1.looseBVarRange' = 0) :
    (ofDecls ds).mkForall ⟨xs.map (fun d => .fvar d.1)⟩ b =
      xs.foldr (fun d e => .forallE d.2.1 d.2.2.1 (e.abstract1 d.1) d.2.2.2) b := by
  have key : ∀ x ∈ xs.map (·.1), ∀ dd, (ofDecls ds).find? x = some dd →
      dd.type.looseBVarRange' = 0 ∧ ∀ v ∈ dd.value? true, v.looseBVarRange' = 0 := by
    rintro _ hx dd hdd
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi⟩ := find?_ofDecls hnd (hsub d hd)
    rw [hi] at hdd; cases hdd
    exact ⟨hcl d (hsub d hd), by simp [Lean.LocalDecl.value?]⟩
  rw [show (⟨xs.map (fun d => Expr.fvar d.1)⟩ : Array Expr) =
    ⟨(xs.map (·.1)).map (.fvar ·)⟩ by simp]
  rw [LocalContext.mkForall_list hb hxnd key
    (fun x hx => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, hi⟩ := find?_ofDecls hnd (hsub d hd)
      exact ⟨_, hi⟩)]
  clear key hb
  induction xs with
  | nil => rfl
  | cons d xs ih =>
    rw [List.map_cons, List.nodup_cons] at hxnd
    obtain ⟨i, hi⟩ := find?_ofDecls hnd (hsub d (.head _))
    rw [List.map_cons, List.foldr_cons, List.foldr_cons,
      ih hxnd.2 fun x hx => hsub x (.tail _ hx)]
    simp [LocalContext.mkBindingList1, hi]


/-- `mkForall_ofDecls` in the shape the array literals in `addQuot` present. -/
theorem mkForall_ofDecls' {ds xs : List BinderData} {arr : Array Expr} {b : Expr}
    (harr : arr = ⟨xs.map (fun d => .fvar d.1)⟩)
    (hnd : (ds.map (·.1)).Nodup) (hxnd : (xs.map (·.1)).Nodup) (hsub : ∀ x ∈ xs, x ∈ ds)
    (hb : b.looseBVarRange' = 0) (hcl : ∀ d ∈ ds, d.2.2.1.looseBVarRange' = 0) :
    (ofDecls ds).mkForall arr b =
      xs.foldr (fun d e => .forallE d.2.1 d.2.2.1 (e.abstract1 d.1) d.2.2.2) b :=
  harr ▸ mkForall_ofDecls hnd hxnd hsub hb hcl

/-! ### 3.1 The four concrete `mkForall`s -/

/-- The local context in force when `addQuot` builds `Quot`'s type. -/
def quotLCtx1 (α r : FVarId) : LocalContext :=
  (({} : LocalContext).mkLocalDecl α `α (.sort (.param `u)) .implicit).mkLocalDecl r `r
    ((Expr.fvar α).arrow ((Expr.fvar α).arrow .prop))

/-- …and `Quot.mk`'s. -/
def quotLCtx2 (α r a : FVarId) : LocalContext :=
  (quotLCtx1 α r).mkLocalDecl a `a (.fvar α)

set_option linter.unusedSimpArgs false in
theorem mkForall_quotType {α r : FVarId} (h : ¬ (r = α)) :
    (quotLCtx1 α r).mkForall
      #[.fvar α, .fvar r] (.sort (.param `u)) = quotTypeE := by
  rw [show quotLCtx1 α r =
    ofDecls [(r, `r, (Expr.fvar α).arrow ((Expr.fvar α).arrow .prop), .default),
             (α, `α, .sort (.param `u), .implicit)] from rfl,
    show (#[.fvar α, .fvar r] : Array Expr) =
      ⟨([(α, `α, Expr.sort (.param `u), BinderInfo.implicit),
         (r, `r, (Expr.fvar α).arrow ((Expr.fvar α).arrow .prop), BinderInfo.default)]
        : List BinderData).map (fun d => .fvar d.1)⟩ from rfl,
    mkForall_ofDecls (by simp [h]) (by simp [Ne.symm h]) (by simp) rfl
      (by simp [Expr.arrow, Expr.prop, Expr.looseBVarRange'])]
  simp [quotTypeE, rTypeE, Expr.abstract1, Expr.arrow, Expr.prop]


set_option linter.unusedSimpArgs false in
theorem mkForall_quotMkType {α r a : FVarId} (h : ([α, r, a] : List FVarId).Nodup) :
    (quotLCtx2 α r a).mkForall
      #[.fvar α, .fvar r, .fvar a]
      (mkApp2 (.const ``Quot [.param `u]) (.fvar α) (.fvar r)) = quotMkTypeE := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    or_false, not_or] at h
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := h
  rw [show quotLCtx2 α r a =
    ofDecls [(a, `a, Expr.fvar α, .default),
             (r, `r, (Expr.fvar α).arrow ((Expr.fvar α).arrow .prop), .default),
             (α, `α, .sort (.param `u), .implicit)] from rfl,
    show (#[.fvar α, .fvar r, .fvar a] : Array Expr) =
      ⟨([(α, `α, Expr.sort (.param `u), BinderInfo.implicit),
         (r, `r, (Expr.fvar α).arrow ((Expr.fvar α).arrow .prop), BinderInfo.default),
         (a, `a, Expr.fvar α, BinderInfo.default)] : List BinderData).map
        (fun d => .fvar d.1)⟩ from rfl,
    mkForall_ofDecls (by simp [Ne.symm h1, Ne.symm h2, Ne.symm h3])
      (by simp [h1, h2, h3]) (by simp) (by simp [Expr.looseBVarRange'])
      (by simp [Expr.arrow, Expr.prop, Expr.looseBVarRange'])]
  simp [quotMkTypeE, rTypeE, Expr.abstract1, Expr.arrow, Expr.prop, mkApp2,
    Ne.symm h1, Ne.symm h2, Ne.symm h3]


/-- The local context in force when `addQuot` builds `Quot.lift`'s type. -/
def liftLCtx (α r a β f b : FVarId) : LocalContext :=
  ((((({} : LocalContext).mkLocalDecl α `α (.sort (.param `u)) .implicit).mkLocalDecl r `r
    ((Expr.fvar α).arrow ((Expr.fvar α).arrow .prop)) .implicit).mkLocalDecl a `a
    (.fvar α)).mkLocalDecl β `β (.sort (.param `v)) .implicit).mkLocalDecl f `f
    ((Expr.fvar α).arrow (Expr.fvar β)) |>.mkLocalDecl b `b (.fvar α)

def liftDecls (α r a β f b : FVarId) : List BinderData :=
  [(b, `b, Expr.fvar α, .default),
   (f, `f, (Expr.fvar α).arrow (Expr.fvar β), .default),
   (β, `β, Expr.sort (.param `v), .implicit),
   (a, `a, Expr.fvar α, .default),
   (r, `r, (Expr.fvar α).arrow ((Expr.fvar α).arrow .prop), .implicit),
   (α, `α, Expr.sort (.param `u), .implicit)]

theorem liftLCtx_eq {α r a β f b : FVarId} :
    liftLCtx α r a β f b = ofDecls (liftDecls α r a β f b) := rfl

set_option linter.unusedSimpArgs false in
theorem mkForall_quotLiftType {α r a β f b : FVarId}
    (h : ([α, r, a, β, f, b] : List FVarId).Nodup) :
    (liftLCtx α r a β f b).mkForall #[.fvar α, .fvar r, .fvar β, .fvar f]
      (.arrow ((liftLCtx α r a β f b).mkForall #[.fvar a, .fvar b]
          (.arrow (mkApp2 (.fvar r) (.fvar a) (.fvar b))
            (mkApp3 (.const ``Eq [.param `v]) (.fvar β)
              (.app (.fvar f) (.fvar a)) (.app (.fvar f) (.fvar b)))))
        (.arrow (mkApp2 (.const ``Quot [.param `u]) (.fvar α) (.fvar r)) (.fvar β)))
      = quotLiftTypeE := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil] at h
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15, -⟩ := h
  rw [liftLCtx_eq,
    mkForall_ofDecls' (arr := #[.fvar a, .fvar b])
      (xs := [(a, `a, Expr.fvar α, .default), (b, `b, Expr.fvar α, .default)]) rfl
      (by simp [liftDecls, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15]) (by simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15]) (by simp [liftDecls])
      (by simp [Expr.arrow, mkApp2, mkApp3, Expr.looseBVarRange'])
      (by simp [liftDecls, Expr.arrow, Expr.prop, Expr.looseBVarRange'])]
  rw [mkForall_ofDecls' (arr := #[.fvar α, .fvar r, .fvar β, .fvar f])
      (xs := [(α, `α, Expr.sort (.param `u), .implicit),
      (r, `r, (Expr.fvar α).arrow ((Expr.fvar α).arrow .prop), .implicit),
      (β, `β, Expr.sort (.param `v), .implicit),
      (f, `f, (Expr.fvar α).arrow (Expr.fvar β), .default)])
      rfl (by simp [liftDecls, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15]) (by simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15]) (by simp [liftDecls])
      (by simp [Expr.arrow, mkApp2, mkApp3, Expr.abstract1, Expr.looseBVarRange', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15])
      (by simp [liftDecls, Expr.arrow, Expr.prop, Expr.looseBVarRange'])]
  simp [quotLiftTypeE, rTypeE, Expr.abstract1, Expr.arrow, Expr.prop, mkApp2, mkApp3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h15]


/-- The local context in force when `addQuot` builds `Quot.ind`'s minor premise, and (with `q`
added) its type. -/
def indDecls0 (α r a β : FVarId) : List BinderData :=
  [(β, `β, ((mkApp2 (Expr.const ``Quot [.param `u]) (.fvar α) (.fvar r)).arrow .prop), .implicit),
   (a, `a, Expr.fvar α, .default),
   (r, `r, (Expr.fvar α).arrow ((Expr.fvar α).arrow .prop), .implicit),
   (α, `α, Expr.sort (.param `u), .implicit)]

def indDecls (α r a β q : FVarId) : List BinderData :=
  (q, `q, mkApp2 (Expr.const ``Quot [.param `u]) (.fvar α) (.fvar r), .implicit)
    :: indDecls0 α r a β

def indLCtx0 (α r a β : FVarId) : LocalContext :=
  ((({} : LocalContext).mkLocalDecl α `α (.sort (.param `u)) .implicit).mkLocalDecl r `r
    ((Expr.fvar α).arrow ((Expr.fvar α).arrow .prop)) .implicit).mkLocalDecl a `a
    (.fvar α) |>.mkLocalDecl β `β
    ((mkApp2 (Expr.const ``Quot [.param `u]) (.fvar α) (.fvar r)).arrow .prop) .implicit

def indLCtx (α r a β q : FVarId) : LocalContext :=
  (indLCtx0 α r a β).mkLocalDecl q `q
    (mkApp2 (Expr.const ``Quot [.param `u]) (.fvar α) (.fvar r)) .implicit

theorem indLCtx0_eq {α r a β : FVarId} : indLCtx0 α r a β = ofDecls (indDecls0 α r a β) := rfl
theorem indLCtx_eq {α r a β q : FVarId} :
    indLCtx α r a β q = ofDecls (indDecls α r a β q) := rfl

set_option linter.unusedSimpArgs false in
theorem mkForall_quotIndType {α r a β q : FVarId}
    (h : ([α, r, a, β, q] : List FVarId).Nodup) :
    (indLCtx α r a β q).mkForall #[.fvar α, .fvar r, .fvar β]
      (.forallE `mk
        ((indLCtx0 α r a β).mkForall #[.fvar a]
          (.app (.fvar β)
            (mkApp3 (.const ``Quot.mk [.param `u]) (.fvar α) (.fvar r) (.fvar a))))
        ((indLCtx α r a β q).mkForall #[.fvar q] (.app (.fvar β) (.fvar q))) .default)
      = quotIndTypeE := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := h
  rw [indLCtx0_eq, indLCtx_eq,
    mkForall_ofDecls' (arr := #[.fvar a]) (xs := [(a, `a, Expr.fvar α, .default)]) rfl
      (by simp [indDecls0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10]) (by simp) (by simp [indDecls0])
      (by simp [Expr.arrow, mkApp2, mkApp3, Expr.looseBVarRange'])
      (by simp [indDecls0, Expr.arrow, Expr.prop, mkApp2, Expr.looseBVarRange']),
    mkForall_ofDecls' (arr := #[.fvar q]) (xs := [(q, `q,
        mkApp2 (Expr.const ``Quot [.param `u]) (.fvar α) (.fvar r), .implicit)]) rfl
      (by simp [indDecls, indDecls0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10]) (by simp) (by simp [indDecls, indDecls0])
      (by simp [Expr.looseBVarRange'])
      (by simp [indDecls, indDecls0, Expr.arrow, Expr.prop, mkApp2, Expr.looseBVarRange']),
    mkForall_ofDecls' (arr := #[.fvar α, .fvar r, .fvar β])
      (xs := [(α, `α, Expr.sort (.param `u), .implicit),
        (r, `r, (Expr.fvar α).arrow ((Expr.fvar α).arrow .prop), .implicit),
        (β, `β, ((mkApp2 (Expr.const ``Quot [.param `u]) (.fvar α) (.fvar r)).arrow .prop),
          .implicit)]) rfl
      (by simp [indDecls, indDecls0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10]) (by simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10]) (by simp [indDecls, indDecls0])
      (by simp [Expr.arrow, mkApp2, mkApp3, Expr.abstract1, Expr.looseBVarRange', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10])
      (by simp [indDecls, indDecls0, Expr.arrow, Expr.prop, mkApp2, Expr.looseBVarRange'])]
  simp [quotIndTypeE, rTypeE, Expr.abstract1, Expr.arrow, Expr.prop, mkApp2, mkApp3, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10]


/-! ## 4. What the executable `Environment.addQuot` computes -/

/-- The `n`-th free variable `addQuot`'s `withLocalDecl`s allocate.  The `ExprBuildT`
`NameGenerator` starts at `{ namePrefix := `_uniq, idx := 1 }` and each `withFreshId` hands
the continuation `ngen.curr` and runs it at `ngen.next`, so the ids are `_uniq.1`, `_uniq.2`,
… in order of nesting -- and are *reused* across sibling blocks, which is harmless because
each `mkForall` reads the local context in force at its own point. -/
def qfv (n : Nat) : FVarId := ⟨.num `_uniq n⟩

@[simp] theorem qfv_inj {m n : Nat} : qfv m = qfv n ↔ m = n := by
  simp [qfv, Lean.FVarId.mk.injEq, Lean.Name.num.injEq]

theorem mkForall_quotType_c :
    (quotLCtx1 (qfv 1) (qfv 2)).mkForall #[.fvar (qfv 1), .fvar (qfv 2)] (.sort (.param `u))
      = quotTypeE := mkForall_quotType (by simp)

theorem mkForall_quotMkType_c :
    (quotLCtx2 (qfv 1) (qfv 2) (qfv 3)).mkForall
      #[.fvar (qfv 1), .fvar (qfv 2), .fvar (qfv 3)]
      (mkApp2 (.const ``Quot [.param `u]) (.fvar (qfv 1)) (.fvar (qfv 2)))
      = quotMkTypeE := mkForall_quotMkType (by simp)

theorem mkForall_quotLiftType_c :
    (liftLCtx (qfv 1) (qfv 2) (qfv 3) (qfv 4) (qfv 5) (qfv 6)).mkForall
      #[.fvar (qfv 1), .fvar (qfv 2), .fvar (qfv 4), .fvar (qfv 5)]
      (.arrow ((liftLCtx (qfv 1) (qfv 2) (qfv 3) (qfv 4) (qfv 5) (qfv 6)).mkForall
          #[.fvar (qfv 3), .fvar (qfv 6)]
          (.arrow (mkApp2 (.fvar (qfv 2)) (.fvar (qfv 3)) (.fvar (qfv 6)))
            (mkApp3 (.const ``Eq [.param `v]) (.fvar (qfv 4))
              (.app (.fvar (qfv 5)) (.fvar (qfv 3))) (.app (.fvar (qfv 5)) (.fvar (qfv 6))))))
        (.arrow (mkApp2 (.const ``Quot [.param `u]) (.fvar (qfv 1)) (.fvar (qfv 2)))
          (.fvar (qfv 4))))
      = quotLiftTypeE := mkForall_quotLiftType (by simp)

theorem mkForall_quotIndType_c :
    (indLCtx (qfv 1) (qfv 2) (qfv 3) (qfv 4) (qfv 5)).mkForall
      #[.fvar (qfv 1), .fvar (qfv 2), .fvar (qfv 4)]
      (.forallE `mk
        ((indLCtx0 (qfv 1) (qfv 2) (qfv 3) (qfv 4)).mkForall #[.fvar (qfv 3)]
          (.app (.fvar (qfv 4))
            (mkApp3 (.const ``Quot.mk [.param `u]) (.fvar (qfv 1)) (.fvar (qfv 2))
              (.fvar (qfv 3)))))
        ((indLCtx (qfv 1) (qfv 2) (qfv 3) (qfv 4) (qfv 5)).mkForall #[.fvar (qfv 5)]
          (.app (.fvar (qfv 4)) (.fvar (qfv 5)))) .default)
      = quotIndTypeE := mkForall_quotIndType (by simp)

/-- The stored types exactly as `addQuot` builds them, before the `mkForall`s are computed. -/
def quotTypeRaw : Expr :=
  (quotLCtx1 (qfv 1) (qfv 2)).mkForall #[.fvar (qfv 1), .fvar (qfv 2)] (.sort (.param `u))
def quotMkTypeRaw : Expr :=
  (quotLCtx2 (qfv 1) (qfv 2) (qfv 3)).mkForall #[.fvar (qfv 1), .fvar (qfv 2), .fvar (qfv 3)]
    (mkApp2 (.const ``Quot [.param `u]) (.fvar (qfv 1)) (.fvar (qfv 2)))
def quotLiftTypeRaw : Expr :=
  (liftLCtx (qfv 1) (qfv 2) (qfv 3) (qfv 4) (qfv 5) (qfv 6)).mkForall
    #[.fvar (qfv 1), .fvar (qfv 2), .fvar (qfv 4), .fvar (qfv 5)]
    (.arrow ((liftLCtx (qfv 1) (qfv 2) (qfv 3) (qfv 4) (qfv 5) (qfv 6)).mkForall
        #[.fvar (qfv 3), .fvar (qfv 6)]
        (.arrow (mkApp2 (.fvar (qfv 2)) (.fvar (qfv 3)) (.fvar (qfv 6)))
          (mkApp3 (.const ``Eq [.param `v]) (.fvar (qfv 4))
            (.app (.fvar (qfv 5)) (.fvar (qfv 3))) (.app (.fvar (qfv 5)) (.fvar (qfv 6))))))
      (.arrow (mkApp2 (.const ``Quot [.param `u]) (.fvar (qfv 1)) (.fvar (qfv 2)))
        (.fvar (qfv 4))))
def quotIndTypeRaw : Expr :=
  (indLCtx (qfv 1) (qfv 2) (qfv 3) (qfv 4) (qfv 5)).mkForall
    #[.fvar (qfv 1), .fvar (qfv 2), .fvar (qfv 4)]
    (.forallE `mk
      ((indLCtx0 (qfv 1) (qfv 2) (qfv 3) (qfv 4)).mkForall #[.fvar (qfv 3)]
        (.app (.fvar (qfv 4))
          (mkApp3 (.const ``Quot.mk [.param `u]) (.fvar (qfv 1)) (.fvar (qfv 2))
            (.fvar (qfv 3)))))
      ((indLCtx (qfv 1) (qfv 2) (qfv 3) (qfv 4) (qfv 5)).mkForall #[.fvar (qfv 5)]
        (.app (.fvar (qfv 4)) (.fvar (qfv 5)))) .default)

def quotCIRaw : ConstantInfo :=
  .quotInfo { name := ``Quot, kind := .type, levelParams := [`u], type := quotTypeRaw }
def quotMkCIRaw : ConstantInfo :=
  .quotInfo { name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := quotMkTypeRaw }
def quotLiftCIRaw : ConstantInfo :=
  .quotInfo { name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := quotLiftTypeRaw }
def quotIndCIRaw : ConstantInfo :=
  .quotInfo { name := ``Quot.ind, kind := .ind, levelParams := [`u], type := quotIndTypeRaw }

theorem quotCIRaw_eq : quotCIRaw = quotCI := by
  simp only [quotCIRaw, quotCI, quotTypeRaw, mkForall_quotType_c]
theorem quotMkCIRaw_eq : quotMkCIRaw = quotMkCI := by
  simp only [quotMkCIRaw, quotMkCI, quotMkTypeRaw, mkForall_quotMkType_c]
theorem quotLiftCIRaw_eq : quotLiftCIRaw = quotLiftCI := by
  simp only [quotLiftCIRaw, quotLiftCI, quotLiftTypeRaw, mkForall_quotLiftType_c]
theorem quotIndCIRaw_eq : quotIndCIRaw = quotIndCI := by
  simp only [quotIndCIRaw, quotIndCI, quotIndTypeRaw, mkForall_quotIndType_c]

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

/-- **`addQuot`, with the `ExprBuildT` computation carried out.**  Everything here is
definitional unfolding: `ExprBuildT.run`, the two `ReaderT`s, `withLocalDecl`'s
`NameGenerator`, and the `Except` binds.  The four stored types are still the raw `mkForall`
applications; `addQuot_eq` computes them. -/
theorem addQuot_unfold (env : Environment) :
    Environment.addQuot env =
      (if env.quotInit then pure env else do
        checkEqType env
        env.checkName ``Quot
        env.checkName ``Quot.mk
        env.checkName ``Quot.lift
        env.checkName ``Quot.ind
        pure (markQuotInit ((((env.add quotCIRaw).add quotMkCIRaw).add quotLiftCIRaw).add
          quotIndCIRaw))) := rfl

/-- **`addQuot` computed.**  On the non-initialized branch it checks `Eq`, checks the four
names are fresh, and installs exactly `quotCI`, `quotMkCI`, `quotLiftCI`, `quotIndCI`. -/
theorem addQuot_eq (env : Environment) :
    Environment.addQuot env =
      (if env.quotInit then pure env else do
        checkEqType env
        env.checkName ``Quot
        env.checkName ``Quot.mk
        env.checkName ``Quot.lift
        env.checkName ``Quot.ind
        pure (markQuotInit ((((env.add quotCI).add quotMkCI).add quotLiftCI).add quotIndCI))) := by
  rw [addQuot_unfold, quotCIRaw_eq, quotMkCIRaw_eq, quotLiftCIRaw_eq, quotIndCIRaw_eq]


/-! ## 5. The `AddQuot` construction -/

/-- `VEnv.addConst`'s successful result, as a total function. -/
def VEnv.insertConst (env : VEnv) (n : Name) (ci : VConstant) : VEnv :=
  { env with constants := fun m => if n = m then some ci else env.constants m }

theorem VEnv.addConst_eq_insertConst {env : VEnv} {n ci} (h : env.constants n = none) :
    env.addConst n ci = some (env.insertConst n ci) := by
  simp [VEnv.addConst, h, VEnv.insertConst]

@[simp] theorem VEnv.constants_insertConst {env : VEnv} {n ci m} :
    (env.insertConst n ci).constants m = if n = m then some ci else env.constants m := rfl

/-- The abstract environment `addQuot` produces. -/
def quotVEnv (venv : VEnv) : VEnv :=
  ((((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk quotMkConst).insertConst
    ``Quot.lift quotLiftConst).insertConst ``Quot.ind quotIndConst).addDefEq quotDefEq

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment in
/-- **The refinement step for `addQuot`.**  Its two non-bookkeeping inputs are exactly what
the executable checker supplies: `QuotReady` (from `checkEqType`, via
`checkEqType.WF_quotReady_closed`) and the four freshness facts (from `checkName`). -/
theorem trEnv_addQuot {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (H : TrEnv safety env venv) (hq : env.quotInit = false) (hready : venv.QuotReady)
    (n1 : env.find? ``Quot = none) (n2 : env.find? ``Quot.mk = none)
    (n3 : env.find? ``Quot.lift = none) (n4 : env.find? ``Quot.ind = none) :
    TrEnv safety (markQuotInit ((((env.add quotCI).add quotMkCI).add quotLiftCI).add quotIndCI))
      (quotVEnv venv) := by
  have mw := H.map_wf
  have m1 : env.constants.find? ``Quot = none := by rw [← mw.find?'_eq_find?]; exact n1
  have m2 : env.constants.find? ``Quot.mk = none := by rw [← mw.find?'_eq_find?]; exact n2
  have m3 : env.constants.find? ``Quot.lift = none := by rw [← mw.find?'_eq_find?]; exact n3
  have m4 : env.constants.find? ``Quot.ind = none := by rw [← mw.find?'_eq_find?]; exact n4
  have v1 : venv.constants ``Quot = none := H.constants_eq_none n1
  have v2 : venv.constants ``Quot.mk = none := H.constants_eq_none n2
  have v3 : venv.constants ``Quot.lift = none := H.constants_eq_none n3
  have v4 : venv.constants ``Quot.ind = none := H.constants_eq_none n4
  have H0 : TrEnv' safety env.constants env.quotInit venv := H
  have H' : TrEnv' safety env.constants false venv := hq ▸ H0
  show TrEnv' safety _ true _
  refine TrEnv'.quot hready ?_ H'
  refine ⟨[`u], quotTypeE, _, ⟨DefinitionSafety.le_rfl, rfl, trExprS_quotType⟩, m1,
    VEnv.addConst_eq_insertConst v1, ?_⟩
  have q1 : (venv.insertConst ``Quot quotConst).constants ``Quot = some quotConst := by simp
  refine ⟨[`u], quotMkTypeE, _, ⟨DefinitionSafety.le_rfl, rfl, trExprS_quotMkType q1⟩,
    by rw [mw.find?_insert]; simp [m2], VEnv.addConst_eq_insertConst (by simp [v2]), ?_⟩
  have q1' : ((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk
      quotMkConst).constants ``Quot = some quotConst := by simp
  have qe : ((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk
      quotMkConst).constants ``Eq = some eqConst := by simp; exact hready
  refine ⟨[`u, `v], quotLiftTypeE, _, ⟨DefinitionSafety.le_rfl, rfl, trExprS_quotLiftType q1' qe⟩,
    by rw [(mw.insert _ _ m1).find?_insert, mw.find?_insert]; simp [m3],
    VEnv.addConst_eq_insertConst (by simp [v3]), ?_⟩
  have q1'' : (((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk
      quotMkConst).insertConst ``Quot.lift quotLiftConst).constants ``Quot = some quotConst := by
    simp
  have qm'' : (((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk
      quotMkConst).insertConst ``Quot.lift quotLiftConst).constants ``Quot.mk =
      some quotMkConst := by simp
  refine ⟨[`u], quotIndTypeE, _, ⟨DefinitionSafety.le_rfl, rfl, trExprS_quotIndType q1'' qm''⟩,
    by rw [((mw.insert _ _ m1).insert _ _ (by rw [mw.find?_insert]; simp [m2])).find?_insert,
      (mw.insert _ _ m1).find?_insert, mw.find?_insert]; simp [m4],
    VEnv.addConst_eq_insertConst (by simp [v4]), rfl, rfl⟩


/-- The freshness of all four quotient names in a `VEnv`, as the four `addConst` steps see
them. -/
structure QuotFresh (venv : VEnv) : Prop where
  hq : venv.constants ``Quot = none
  hmk : venv.constants ``Quot.mk = none
  hlift : venv.constants ``Quot.lift = none
  hind : venv.constants ``Quot.ind = none

theorem QuotFresh.add1 {venv : VEnv} (h : QuotFresh venv) :
    venv.addConst ``Quot quotConst = some (venv.insertConst ``Quot quotConst) :=
  VEnv.addConst_eq_insertConst h.hq
theorem QuotFresh.add2 {venv : VEnv} (h : QuotFresh venv) :
    (venv.insertConst ``Quot quotConst).addConst ``Quot.mk quotMkConst =
      some ((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk quotMkConst) :=
  VEnv.addConst_eq_insertConst (by simp [h.hmk])
theorem QuotFresh.add3 {venv : VEnv} (h : QuotFresh venv) :
    ((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk quotMkConst).addConst
        ``Quot.lift quotLiftConst =
      some (((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk
        quotMkConst).insertConst ``Quot.lift quotLiftConst) :=
  VEnv.addConst_eq_insertConst (by simp [h.hlift])
theorem QuotFresh.add4 {venv : VEnv} (h : QuotFresh venv) :
    (((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk quotMkConst).insertConst
        ``Quot.lift quotLiftConst).addConst ``Quot.ind quotIndConst =
      some ((((venv.insertConst ``Quot quotConst).insertConst ``Quot.mk
        quotMkConst).insertConst ``Quot.lift quotLiftConst).insertConst
        ``Quot.ind quotIndConst) :=
  VEnv.addConst_eq_insertConst (by simp [h.hind])

theorem le_quotVEnv {venv : VEnv} (h : QuotFresh venv) : venv ≤ quotVEnv venv :=
  ((((VEnv.addConst_le h.add1).trans (VEnv.addConst_le h.add2)).trans
    (VEnv.addConst_le h.add3)).trans (VEnv.addConst_le h.add4)).trans VEnv.addDefEq_le

theorem quotVEnv_mono {e1 e2 : VEnv} (H : e1 ≤ e2) (h1 : QuotFresh e1) (h2 : QuotFresh e2) :
    quotVEnv e1 ≤ quotVEnv e2 :=
  VEnv.addDefEq_mono <| VEnv.addConst_mono (VEnv.addConst_mono (VEnv.addConst_mono
    (VEnv.addConst_mono H h1.add1 h2.add1) h1.add2 h2.add2) h1.add3 h2.add3) h1.add4 h2.add4

/-- The four names are not primitives, so the quotient step preserves `HasPrimitives`. -/
theorem hasPrimitives_quotVEnv {venv : VEnv} (H : venv.HasPrimitives) (h : QuotFresh venv)
    (p1 : Environment.primitives.contains ``Quot = false)
    (p2 : Environment.primitives.contains ``Quot.mk = false)
    (p3 : Environment.primitives.contains ``Quot.lift = false)
    (p4 : Environment.primitives.contains ``Quot.ind = false) :
    (quotVEnv venv).HasPrimitives :=
  ((((H.addConst p1 h.add1).addConst p2 h.add2).addConst p3 h.add3).addConst p4 h.add4).addDefEq


open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment in
/-- `safePrimitives` survives the quotient step: the four names are not primitives, so every
primitive found afterwards was already there. -/
theorem safePrimitives_quotEnv {env : Environment} (mw : env.constants.WF)
    (old : ∀ {n : Name} {ci}, env.find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (n1 : env.find? ``Quot = none) (n2 : env.find? ``Quot.mk = none)
    (n3 : env.find? ``Quot.lift = none) (n4 : env.find? ``Quot.ind = none)
    (p1 : Environment.primitives.contains ``Quot = false)
    (p2 : Environment.primitives.contains ``Quot.mk = false)
    (p3 : Environment.primitives.contains ``Quot.lift = false)
    (p4 : Environment.primitives.contains ``Quot.ind = false)
    {n : Name} {ci : ConstantInfo}
    (hfind : (markQuotInit
        ((((env.add quotCI).add quotMkCI).add quotLiftCI).add quotIndCI)).find? n = some ci)
    (hp : Environment.primitives.contains n) : ci.safety = .safe ∧ ci.levelParams = [] := by
  have c1 : env.constants.find? ``Quot = none := by rw [← mw.find?'_eq_find?]; exact n1
  have mw1 : (env.add quotCI).constants.WF := mw.insert _ _ c1
  have f2 : (env.add quotCI).find? ``Quot.mk = none :=
    Environment.find?_add_of_ne mw quotCI n1 (by decide) n2
  have f3 : (env.add quotCI).find? ``Quot.lift = none :=
    Environment.find?_add_of_ne mw quotCI n1 (by decide) n3
  have f4 : (env.add quotCI).find? ``Quot.ind = none :=
    Environment.find?_add_of_ne mw quotCI n1 (by decide) n4
  have old1 : ∀ {n : Name} {ci}, (env.add quotCI).find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [] :=
    fun h hp => safePrimitives_add' mw old quotCI n1 (fun h => absurd h (show ¬ Environment.primitives.contains quotCI.name = true by
      rw [show quotCI.name = ``Quot from rfl]; simp [p1])) h hp
  have c2 : (env.add quotCI).constants.find? ``Quot.mk = none := by
    rw [← mw1.find?'_eq_find?]; exact f2
  have mw2 : ((env.add quotCI).add quotMkCI).constants.WF := mw1.insert _ _ c2
  have g3 : ((env.add quotCI).add quotMkCI).find? ``Quot.lift = none :=
    Environment.find?_add_of_ne mw1 quotMkCI f2 (by decide) f3
  have g4 : ((env.add quotCI).add quotMkCI).find? ``Quot.ind = none :=
    Environment.find?_add_of_ne mw1 quotMkCI f2 (by decide) f4
  have old2 : ∀ {n : Name} {ci}, ((env.add quotCI).add quotMkCI).find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [] :=
    fun h hp => safePrimitives_add' mw1 old1 quotMkCI f2 (fun h => absurd h (show ¬ Environment.primitives.contains quotMkCI.name = true by
      rw [show quotMkCI.name = ``Quot.mk from rfl]; simp [p2])) h hp
  have c3 : ((env.add quotCI).add quotMkCI).constants.find? ``Quot.lift = none := by
    rw [← mw2.find?'_eq_find?]; exact g3
  have mw3 : (((env.add quotCI).add quotMkCI).add quotLiftCI).constants.WF := mw2.insert _ _ c3
  have k4 : (((env.add quotCI).add quotMkCI).add quotLiftCI).find? ``Quot.ind = none :=
    Environment.find?_add_of_ne mw2 quotLiftCI g3 (by decide) g4
  have old3 : ∀ {n : Name} {ci},
      (((env.add quotCI).add quotMkCI).add quotLiftCI).find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [] :=
    fun h hp => safePrimitives_add' mw2 old2 quotLiftCI g3 (fun h => absurd h (show ¬ Environment.primitives.contains quotLiftCI.name = true by
      rw [show quotLiftCI.name = ``Quot.lift from rfl]; simp [p3])) h hp
  exact safePrimitives_add' mw3 old3 quotIndCI k4 (fun h => absurd h (show ¬ Environment.primitives.contains quotIndCI.name = true by
      rw [show quotIndCI.name = ``Quot.ind from rfl]; simp [p4])) hfind hp


/-! ## 6. `addQuot.WF`, non-vacuously -/

/-- **The honest `addQuot.WF`.**

Contrast the current `addQuot.WF` (`Verify/Environment.lean`), whose non-initialized branch is
discharged by `False.elim` through `checkEqType.WF`'s `False`.  Nothing here is vacuous: the
`QuotReady` premise of `TrEnv'.quot` comes from `checkEqType.WF_quotReady_closed`
(`Verify/InductFlip.lean`), the four freshness premises from `checkName`, and the four
`TrExprS` obligations are discharged against the stored types the executable actually builds
(`addQuot_eq`).

`Verify/Environment.lean`'s `addQuot.WF` can now be replaced by `addQuot.WF' wf`. -/
theorem addQuot.WF' {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rw [addQuot_eq]
  split
  · exact .pure ⟨ves, wf, fun _ => VEnv.LE.rfl⟩
  rename_i hqi
  have hq : env.quotInit = false := by
    cases h : env.quotInit
    · rfl
    · exact absurd h hqi
  have mw := (wf.tr (safety := .safe)).map_wf
  refine (checkEqType.WF_quotReady_closed wf).bind fun _ hready => ?_
  refine (checkName.WF mw ``Quot false).bind fun _ h1 => ?_
  refine (checkName.WF mw ``Quot.mk false).bind fun _ h2 => ?_
  refine (checkName.WF mw ``Quot.lift false).bind fun _ h3 => ?_
  refine (checkName.WF mw ``Quot.ind false).bind fun _ h4 => ?_
  have fresh (safety : DefinitionSafety) : QuotFresh (ves.venv safety) :=
    { hq := (wf.tr (safety := safety)).constants_eq_none h1.1
      hmk := (wf.tr (safety := safety)).constants_eq_none h2.1
      hlift := (wf.tr (safety := safety)).constants_eq_none h3.1
      hind := (wf.tr (safety := safety)).constants_eq_none h4.1 }
  refine .pure ⟨⟨fun safety => quotVEnv (ves.venv safety)⟩, ?_, fun _ => le_quotVEnv (fresh _)⟩
  exact
    { tr := trEnv_addQuot wf.tr hq (hready _) h1.1 h2.1 h3.1 h4.1
      hasPrimitives := hasPrimitives_quotVEnv wf.hasPrimitives (fresh _)
        (h1.2 rfl) (h2.2 rfl) (h3.2 rfl) (h4.2 rfl)
      safePrimitives := safePrimitives_quotEnv mw wf.safePrimitives h1.1 h2.1 h3.1 h4.1
        (h1.2 rfl) (h2.2 rfl) (h3.2 rfl) (h4.2 rfl)
      mono := fun hle => quotVEnv_mono (wf.mono hle) (fresh _) (fresh _) }


/-! ## 7. Non-vacuity

Every obligation discharged above is discharged at a concrete witness here.  This matters
because the *other* half of `addQuot.WF'`'s hypotheses is currently unsatisfiable: `wf`
together with `checkEqType env = .ok ()` forces `Eq` to be an `.inductInfo` in a kernel
environment that has a `VEnvs` model, and `VEnvs.WF.no_inductInfo` (`Verify/InductFlip.lean`)
refutes that until `AddInduct` gains constructors.  So §6's *statement* is, today, live only
on the `quotInit = true` branch.

What §7 machine-checks is that nothing in the construction is vacuous on its own terms: at an
environment where `Eq` is present as an **axiom** of exactly the type `eqConst` models,
`TrEnv'.quot` fires, `AddQuot` is inhabited, and the four `AddQuot1` steps really put
`quotConst`, `quotMkConst`, `quotLiftConst`, `quotIndConst` into the model.  When the
`AddInduct` flip lands and `Eq` arrives as an inductive instead, §6 applies verbatim: nothing
below is used by §6, and nothing in §6 depends on how `Eq` got into the environment. -/

namespace QuotWit

/-- `Eq`, as an axiom of exactly the type `eqConst` models. -/
def eqAx : AxiomVal :=
  { name := ``Eq, levelParams := [`u], type := eqStoredType `u, isUnsafe := false }

def env0 : Environment := Kernel.Environment.empty `main

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

def envEq : Environment := env0.add (.axiomInfo eqAx)

def venvEq : VEnv := VEnv.empty.insertConst ``Eq eqConst

theorem constants_env0 : env0.constants = {} := rfl

theorem constants_env0_wf : env0.constants.WF where
  stage := rfl
  map₂ := rfl

theorem constants_env0_find? (n : Name) : env0.constants.find? n = none := by
  simp [constants_env0, SMap.find?]

theorem find?_env0 (n : Name) : env0.find? n = none := by
  rw [Kernel.Environment.find?, constants_env0_wf.find?'_eq_find?, constants_env0_find?]

theorem trEnv_envEq {safety : DefinitionSafety} : TrEnv safety envEq venvEq := by
  refine TrEnv'.axiom (ci := eqAx) (ci' := eqConst) ⟨DefinitionSafety.le_safe, rfl, trExprS_eqStoredType⟩
    (constants_env0_find? _) ⟨_, by type_tac⟩
    (VEnv.addConst_eq_insertConst (by rfl))
    (TrEnv'.empty constants_env0_wf constants_env0_find?)

theorem quotReady_venvEq : venvEq.QuotReady := rfl

theorem fresh1 : envEq.find? ``Quot = none :=
  Environment.find?_add_of_ne constants_env0_wf _ (find?_env0 _) (by decide) (find?_env0 _)
theorem fresh2 : envEq.find? ``Quot.mk = none :=
  Environment.find?_add_of_ne constants_env0_wf _ (find?_env0 _) (by decide) (find?_env0 _)
theorem fresh3 : envEq.find? ``Quot.lift = none :=
  Environment.find?_add_of_ne constants_env0_wf _ (find?_env0 _) (by decide) (find?_env0 _)
theorem fresh4 : envEq.find? ``Quot.ind = none :=
  Environment.find?_add_of_ne constants_env0_wf _ (find?_env0 _) (by decide) (find?_env0 _)

/-- **`trEnv_addQuot` fires at a concrete environment**, at every safety level.  So
`TrEnv'.quot` is reachable and `AddQuot` is inhabited: the §5 construction is not vacuous. -/
theorem trEnv_addQuot_wit {safety : DefinitionSafety} :
    TrEnv safety
      (markQuotInit ((((envEq.add quotCI).add quotMkCI).add quotLiftCI).add quotIndCI))
      (quotVEnv venvEq) :=
  trEnv_addQuot trEnv_envEq rfl quotReady_venvEq fresh1 fresh2 fresh3 fresh4

/-- …and the model it produces really holds the four quotient constants and the ι-rule; the
step is not a no-op. -/
theorem quotVEnv_venvEq_contents :
    (quotVEnv venvEq).constants ``Quot = some quotConst ∧
    (quotVEnv venvEq).constants ``Quot.mk = some quotMkConst ∧
    (quotVEnv venvEq).constants ``Quot.lift = some quotLiftConst ∧
    (quotVEnv venvEq).constants ``Quot.ind = some quotIndConst ∧
    (quotVEnv venvEq).constants ``Eq = some eqConst ∧
    (quotVEnv venvEq).defeqs quotDefEq :=
  ⟨rfl, rfl, rfl, rfl, rfl, .inl rfl⟩

end QuotWit

end Lean4Lean
