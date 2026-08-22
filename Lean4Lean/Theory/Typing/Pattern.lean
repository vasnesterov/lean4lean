import Lean4Lean.Theory.VExpr

namespace Lean4Lean

open VExpr

inductive Pattern where
  | const (c : Name)
  | app (f a : Pattern)
  | var (f : Pattern)

def Pattern.varN (p : Pattern) : Nat → Pattern
  | 0 => p
  | n+1 => (p.varN n).var

inductive Subpattern (p : Pattern) : Pattern → Prop where
  | refl : Subpattern p p
  | appL : Subpattern p f → Subpattern p (.app f a)
  | appR : Subpattern p a → Subpattern p (.app f a)
  | varL : Subpattern p f → Subpattern p (.var f)

theorem Subpattern.varN (h : Subpattern p f) : ∀ {n}, Subpattern p (.varN f n)
  | 0 => h
  | _+1 => .varL (.varN h)

theorem Subpattern.trans {p₁ p₂ p₃} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₃) : Subpattern p₁ p₃ := by
  induction H₂ with
  | refl => exact H₁
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | varL _ ih => exact .varL ih

theorem Subpattern.sizeOf_le {p₁ p₂} (H₁ : Subpattern p₁ p₂) : sizeOf p₁ ≤ sizeOf p₂ := by
  induction H₁ <;> simp <;> omega

theorem Subpattern.antisymm {p₁ p₂} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₁) : p₂ = p₁ := by
  cases id H₂ with
  | refl => rfl
  | _ h₂ =>
    have H₁ := H₁.sizeOf_le
    have h₂ := h₂.sizeOf_le
    simp at H₁; omega

inductive Arity (p : Pattern) : Nat → Pattern → Prop where
  | refl : Arity p 0 p
  | app : Arity p n f → Arity p (n+1) (.app f a)
  | var : Arity p n f → Arity p (n+1) (.var f)

theorem Arity.subpattern : Arity p n p' → Subpattern p p'
  | .refl => .refl
  | .app h => .appL h.subpattern
  | .var h => .varL h.subpattern

def Pattern.inter : Pattern → Pattern → Option Pattern
  | .const c, .const c' => if c = c' then some (.const c) else none
  | .app f a, .app f' a' => return .app (← f.inter f') (← a.inter a')
  | .var f, .var f' => return .var (← f.inter f')
  | .app f a, .var f' => return .app (← f.inter f') a
  | .var f, .app f' a' => return .app (← f.inter f') a'
  | _, _ => none

theorem Pattern.inter_self (p : Pattern) : p.inter p = some p := by induction p <;> simp [*, inter]

theorem Pattern.inter_comm (p q : Pattern) : p.inter q = q.inter p := by
  induction p generalizing q <;> cases q <;> simp [*, eq_comm, inter] <;> split <;> simp [*]

inductive Pattern.LE : Pattern → Pattern → Prop where
  | refl : LE p p
  | var : LE f f' → LE (.var f) (.var f')
  | app : LE f f' → LE a a' → LE (.app f a) (.app f' a')
  | app_var : LE f f' → LE (.app f a) (.var f')

def Pattern.Path : Pattern → Type
  | .const _ => Empty
  | .app f a => f.Path ⊕ a.Path
  | .var f => Option f.Path

/-- The `const` leaves of a pattern. `Matches` records the universe level list found at
each of them, not just the head's: an ι-rule's pattern is `rec.{ls} a … (c.{ls'} b …)`,
and bridging `c.{ls'} b` to `c.{ls} b` needs `ls ≈ ls'`, which was not stateable while
`Matches` kept a single `List VLevel`. Requiring `ls' = ls` syntactically instead would be
unsound for confluence: `rec.{max u v} … (c.{max v u} …)` and `rec.{max u v} … (c.{max u v} …)`
are `NormalEq`-related by `constDF`, but only the second would be a redex. -/
def Pattern.LPath : Pattern → Type
  | .const _ => Unit
  | .app f a => f.LPath ⊕ a.LPath
  | .var f => f.LPath

/-- The leftmost `const` leaf: the pattern's head. -/
def Pattern.LPath.head : (p : Pattern) → p.LPath
  | .const _ => ()
  | .app f _ => .inl (LPath.head f)
  | .var f => LPath.head f

inductive Pattern.Matches :
    (p : Pattern) → VExpr → (p.LPath → List VLevel) → (p.Path → VExpr) → Prop
  | const : Matches (.const c) (.const c ls) (fun _ => ls) nofun
  | var : Matches f f' f1 g1 → Matches (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : Matches f f' f1 g1 → Matches a a' f2 g2 →
    Matches (.app f a) (.app f' a') (Sum.elim f1 f2) (Sum.elim g1 g2)

theorem Pattern.Matches.uniq {p : Pattern} {e : VExpr} {m1 m2 m1' m2'}
    (H1 : Pattern.Matches p e m1 m2) (H2 : Pattern.Matches p e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction H1 with
  | const => let .const := H2; exact ⟨rfl, rfl⟩
  | var _ ih =>
    let .var h := H2
    obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | app _ _ ih1 ih2 =>
    let .app h1 h2 := H2
    obtain ⟨rfl, rfl⟩ := ih1 h1; obtain ⟨rfl, rfl⟩ := ih2 h2; exact ⟨rfl, rfl⟩

def Pattern.OnArgs (P : VExpr → Prop) : Pattern → Prop
  | .const .. => True
  | .var f => f.OnArgs P
  | .app f a => f.OnArgs P ∧ a.OnArgs P ∧ ∀ e m1 m2, a.Matches e m1 m2 → P e

inductive Pattern.RHS (p : Pattern) where
  /-- A closed term, instantiated at the levels found at the `const` leaf `lp`. -/
  | fixed (c : VExpr) (lp : p.LPath) (_ : c.Closed)
  | app (f a : RHS p)
  | var (e : p.Path)

inductive Pattern.Check (p : Pattern) where
  | true
  | defeq (x y : RHS p) (rest : Check p)
  /-- `(m1 x).getD i ≈ (m1 y).getD j`: the level agreement an ι-rule needs between the
  recursor's leaf and the constructor's. -/
  | level (x : p.LPath) (i : Nat) (y : p.LPath) (j : Nat) (rest : Check p)

def Pattern.RHS.apply {p : Pattern} (m1 : p.LPath → List VLevel)
    (m2 : p.Path → VExpr) : p.RHS → VExpr
  | .fixed c lp _ => c.instL (m1 lp)
  | .var path => m2 path
  | .app f a => .app (f.apply m1 m2) (a.apply m1 m2)

theorem Pattern.RHS.lift'_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).lift' ρ = (r.apply m1 fun x => (m2 x).lift' ρ) := by
  induction r <;> simp [*, apply, lift', ← instL_lift']
  rw [ClosedN.lift'_eq ‹_› (by trivial)]

theorem Pattern.RHS.liftN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).liftN n k = (r.apply m1 fun x => (m2 x).liftN n k) := by
  simp [← lift'_consN_skipN, lift'_apply]

theorem Pattern.matches_lift' {p : Pattern} {e : VExpr} {m1 m2'} :
    p.Matches (e.lift' ρ) m1 m2' ↔
    ∃ m2, p.Matches e m1 m2 ∧ ∀ x, m2' x = (m2 x).lift' ρ := by
  constructor
  · intro h; generalize eq : e.lift' ρ = e' at h
    induction h generalizing e with
    | const => cases e <;> cases eq; exact ⟨_, .const, nofun⟩
    | var _ ih =>
      cases e <;> cases eq
      have ⟨_, l1, l2⟩ := ih rfl
      refine ⟨_, .var l1, ?_⟩
      rintro (_|_) <;> solve_by_elim
    | app _ _ ih1 ih2 =>
      cases e <;> cases eq
      have ⟨_, l1, l2⟩ := ih1 rfl
      have ⟨_, r1, r2⟩ := ih2 rfl
      refine ⟨_, .app l1 r1, ?_⟩
      rintro (_|_) <;> solve_by_elim
  · intro ⟨m2, h1, h2⟩
    induction h1 with
    | const => exact (show m2' = _ by ext ⟨⟩) ▸ .const
    | var _ ih =>
      have := (ih (h2 <| some ·)).var (a' := ?_)
      rwa [(_ : m2' = _)]; ext (_|_) <;> simp [h2 none]
    | app _ _ ih1 ih2 =>
      have := (ih1 (h2 <| .inl ·)).app (ih2 (h2 <| .inr ·))
      rwa [(_ : m2' = _)]; ext (_|_) <;> rfl

theorem Pattern.matches_liftN {p : Pattern} {e : VExpr} {m1 m2'} :
    p.Matches (e.liftN n k) m1 m2' ↔ ∃ m2, p.Matches e m1 m2 ∧ ∀ x, m2' x = (m2 x).liftN n k := by
  simp only [← lift'_consN_skipN]; exact p.matches_lift'

theorem Pattern.RHS.instN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).inst e₀ k = (r.apply m1 fun x => (m2 x).inst e₀ k) := by
  induction r <;> simp [*, apply, inst]
  rw [(ClosedN.instL ‹_›).instN_eq (Nat.zero_le _)]

theorem Pattern.matches_instN {p : Pattern} {e : VExpr} {m1 m2} (H : p.Matches e m1 m2) :
    p.Matches (e.inst e₀ k) m1 fun x => (m2 x).inst e₀ k := by
  induction H with
  | const => erw [show (fun _ : Empty => _) = _ by ext ⟨⟩]; exact .const
  | var _ ih =>
    rw [(_ : (fun _ => _) = _)]; exact ih.var
    ext (_|_) <;> rfl
  | app _ _ ih1 ih2 =>
    rw [(_ : (fun _ => _) = _)]; exact ih1.app ih2
    ext (_|_) <;> rfl

theorem Pattern.matches_inter {p q : Pattern} {e : VExpr} :
    (∃ m1 m2, p.Matches e m1 m2) ∧ (∃ m1 m2, q.Matches e m1 m2) ↔
    (∃ r m1 m2, p.inter q = some r ∧ r.Matches e m1 m2) := by
  constructor
  · rintro ⟨⟨m1, m2, hp⟩, ⟨m3, m4, hq⟩⟩
    induction hp generalizing q with
    | const => let .const := hq; exact ⟨_, _, _, by simp [inter], .const⟩
    | var _ ih =>
      cases hq with
      | var hq' =>
        have ⟨_, _, _, h1, h2⟩ := ih _ _ hq'
        exact ⟨_, _, _, by simp [inter, h1], .var h2⟩
      | app hqf hqa =>
        have ⟨_, _, _, h1, h2⟩ := ih _ _ hqf
        exact ⟨_, _, _, by simp [inter, h1], .app h2 hqa⟩
    | app _ ha ihf iha =>
      cases hq with
      | var hq' =>
        have ⟨_, _, _, h1, h2⟩ := ihf _ _ hq'
        exact ⟨_, _, _, by simp [inter, h1], .app h2 ha⟩
      | app hqf hqa =>
        have ⟨_, _, _, h1, h2⟩ := ihf _ _ hqf
        have ⟨_, _, _, h3, h4⟩ := iha _ _ hqa
        exact ⟨_, _, _, by simp [inter, h1, h3], .app h2 h4⟩
  · rintro ⟨r, m1, m2, h1, h2⟩
    induction p generalizing q e r with
    | const c =>
      cases q <;> simp [inter] at h1
      obtain ⟨rfl, rfl⟩ := h1; cases h2
      exact ⟨⟨_, _, .const⟩, ⟨_, _, .const⟩⟩
    | var f ihf =>
      cases q <;> simp [inter] at h1
      · obtain ⟨_, wf, rfl⟩ := h1
        let .app hf ha := h2
        have ⟨⟨_, _, hp⟩, ⟨_, _, hq⟩⟩ := ihf _ _ _ wf hf
        exact ⟨⟨_, _, .var hp⟩, ⟨_, _, .app hq ha⟩⟩
      · obtain ⟨_, wf, rfl⟩ := h1
        let .var hf := h2
        have ⟨⟨_, _, hp⟩, ⟨_, _, hq⟩⟩ := ihf _ _ _ wf hf
        exact ⟨⟨_, _, .var hp⟩, ⟨_, _, .var hq⟩⟩
    | app f a ihf iha =>
      cases q <;> simp [inter] at h1
      · obtain ⟨_, wf, _, wa, rfl⟩ := h1
        let .app hf ha := h2
        have ⟨⟨_, _, hp⟩, ⟨_, _, hq⟩⟩ := ihf _ _ _ wf hf
        have ⟨⟨_, _, hp'⟩, ⟨_, _, hq'⟩⟩ := iha _ _ _ wa ha
        exact ⟨⟨_, _, .app hp hp'⟩, ⟨_, _, .app hq hq'⟩⟩
      · obtain ⟨_, wf, rfl⟩ := h1
        let .app hf ha := h2
        have ⟨⟨_, _, hp⟩, ⟨_, _, hq⟩⟩ := ihf _ _ _ wf hf
        exact ⟨⟨_, _, .app hp ha⟩, ⟨_, _, .var hq⟩⟩

theorem Pattern.matches_determ
    (h1 : Matches p e m1 m2) (h2 : Matches p e m1' m2') : m1 = m1' ∧ m2 = m2' := h1.uniq h2

def Pattern.Check.OK (defeq : VExpr → VExpr → Prop) {p : Pattern}
    (m1 : p.LPath → List VLevel) (m2 : p.Path → VExpr) : p.Check → Prop
  | .true => True
  | .defeq a b rest => defeq (RHS.apply m1 m2 a) (RHS.apply m1 m2 b) ∧ rest.OK defeq m1 m2
  | .level x i y j rest =>
    ((m1 x).getD i .zero ≈ (m1 y).getD j .zero) ∧ rest.OK defeq m1 m2

theorem VLevel.forall₂_getD {l l' : List VLevel}
    (h : List.Forall₂ (· ≈ ·) l l') : ∀ i, l.getD i .zero ≈ l'.getD i .zero := by
  induction h with
  | nil => intro _; exact rfl
  | cons hx _ ih => intro i; cases i with | zero => exact hx | succ i => exact ih i

/-- Transport a `Check.OK` across *both* maps. The `level` clause is not automatically
stable under a change of `m1`, so it needs its own hypothesis; the caller that needs this
(`NormalEq.parRed`'s `constDF`/`extra` case) has `List.Forall₂ (· ≈ ·)` on the level lists
and discharges it with `VLevel.forall₂_getD`. -/
theorem Pattern.Check.OK.map_levels
    {df df' : VExpr → VExpr → Prop} {p : Pattern} {ck : p.Check} {m1 m2 m1' m2'}
    (hl : ∀ x i y j, ((m1 x).getD i .zero ≈ (m1 y).getD j .zero) →
      ((m1' x).getD i .zero ≈ (m1' y).getD j .zero))
    (h : ∀ a b : p.RHS,
      df (a.apply m1 m2) (b.apply m1 m2) → df' (a.apply m1' m2') (b.apply m1' m2'))
    (H : ck.OK df m1 m2) : ck.OK df' m1' m2' := by
  induction ck <;> simp [OK, *] at H ⊢ <;> (try cases H) <;>
    refine ⟨?_, by solve_by_elim⟩ <;> solve_by_elim

/-- `m1` is held fixed: the `level` clause constrains it and is not transportable. Every
consumer (`weakN`, `instN`) only ever varies `m2`. -/
theorem Pattern.Check.OK.map
    {df df' : VExpr → VExpr → Prop} {p : Pattern} {ck : p.Check} {m1 m2 m2'}
    (h : ∀ a b : p.RHS,
      df (a.apply m1 m2) (b.apply m1 m2) → df' (a.apply m1 m2') (b.apply m1 m2'))
    (H : ck.OK df m1 m2) : ck.OK df' m1 m2' := by
  induction ck <;> simp [OK, *] at H ⊢ <;> (try cases H) <;>
    refine ⟨?_, by solve_by_elim⟩ <;> solve_by_elim

inductive SimplePattern where
  | iota (recursor : Name) (major : Nat) (constr : Name) (args : Nat)
  | defn (head : Name)

def SimplePattern.toPattern : SimplePattern → Pattern
  | .defn c => .const c
  | .iota r m c n => .app (.varN (.const r) m) (.varN (.const c) n)
