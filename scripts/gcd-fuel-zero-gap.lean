/-
**Why the variable-bound fuel bound of `Nat.gcd` / `Nat.bitwise` cannot be verified as installed.**

`Lean4Lean/Primitive.lean`'s `Nat.gcd` branch binds the recursive call's fuel bound as a
*variable* outside the `dite`:

    withCheckedLocalDecl `hrec .default
      (mkApp2 q(@LE.le Nat instLENat) (succ (mkApp u.measure (pk (mod n m) m))) fuel) fun prf =>
    unless <- checkedIsDefEq (mkApp3 u.go (succ fuel) (pk m n) h)
      (c.dite #[m, zero] n (mkApp3 u.go fuel (pk (mod n m) m) prf)) do fail

`docs/handoff-primitive-natle.md` §2 records that the proposition `prf` inhabits is false in
general, and §2 then claims: "at the literal instances the fuel induction consumes, the
proposition *is* true (`x ≠ 0 → x ≤ f → y % x + 1 ≤ f`)".

**That claim is wrong**, and this file is the refutation.  `VEnv.reflects_fuel_gcd`'s `succ f`
case calls `hgo f x y h hok` **before** the `by_cases x = 0`, so the recurrence equation has to
be instantiated at the `x = 0` states too -- and there the required proposition is `y + 1 ≤ f`,
which the induction's invariant (`x < fuel`, i.e. `0 ≤ f` when `x = 0`) does not give and which
is false at states the induction really reaches.

Since instantiating the fifth binder needs `env.HasType 0 [] w A₀` (`IsDefEqU.instN`), and `A₀`
is defeq to `natLEApp (natLit (y % x + 1)) (natLit f)`, **no witness family can close this**: at
`x = 0` the proposition is semantically false, so in a consistent environment nothing inhabits
it.  The `Condition.natLE` witness producer added in `Verify/Primitive.lean`
(`Condition.check.WF_natLE_pinned`, `∀ i f, i ≤ f → HasType (OT (natLE i f) (PR i f)) (natLE i f)`)
covers exactly the `x ≠ 0` states and cannot cover the others.

Run: `lake env lean scripts/gcd-fuel-zero-gap.lean`
-/

/-- One step of the recursion `VEnv.reflects_fuel_gcd` performs: state `(fuel, x, y)` with
`fuel = f+1` steps to `(f, y % x, x)`, and stops when `x = 0`. -/
def trace : Nat → Nat × Nat × Nat → List (Nat × Nat × Nat)
  | 0, s => [s]
  | k+1, (fuel, x, y) =>
      (fuel, x, y) :: (if x = 0 then [] else trace k (fuel - 1, y % x, x))

/-- The proposition the `hrec` binder must be instantiated with at a visited state
`(fuel, x, y)` (with `fuel = f+1`): `Nat.succ (measure (pack (n % m) m)) ≤ fuel` at
`m := x, n := y, fuel := f`, which the checked measure equation makes `Nat.succ (y % x) ≤ f`. -/
def hrecObligation (s : Nat × Nat × Nat) : Prop :=
  Nat.succ (s.2.2 % s.2.1) ≤ s.1 - 1

instance : DecidablePred hrecObligation := fun _ => Nat.decLe _ _

/-! ### 1. `Nat.gcd 0 5`: the entry state itself needs a false proposition.

`reflects_gcd_of_equations` enters the induction at `hfuel (a+1) a b`, i.e. at `(a+1, a, b)`. -/

/-- info: [(1, 0, 5)] -/
#guard_msgs in #eval trace 10 (0+1, 0, 5)

example : ¬ hrecObligation (1, 0, 5) := by decide   -- `5 % 0 + 1 = 6 ≤ 0` is false

/-! ### 2. `Nat.gcd 4 6`: the *terminal* state of the real recursion needs a false proposition. -/

/-- info: [(5, 4, 6), (4, 2, 4), (3, 0, 2)] -/
#guard_msgs in #eval trace 10 (4+1, 4, 6)

/-- info: [true, true, false] -/
#guard_msgs in #eval (trace 10 (4+1, 4, 6)).map (fun s => decide (hrecObligation s))

example : ((trace 10 (4+1, 4, 6)).any fun s => !decide (hrecObligation s)) = true := by decide

/-! ### 3. It is exactly the `x = 0` states that fail. -/

/-- For `x ≠ 0`, the induction invariant `x < f+1` *does* give the obligation.  This is the half
the `Condition.natLE` witness family closes. -/
example : ∀ x y f : Nat, x ≠ 0 → x ≤ f → Nat.succ (y % x) ≤ f := by
  intro x y f hx _
  have : y % x < x := Nat.mod_lt _ (Nat.pos_of_ne_zero hx)
  omega

/-- At `x = 0` the obligation is `y + 1 ≤ f`, and the invariant gives only `0 ≤ f`. -/
example : ¬ (∀ y f : Nat, 0 ≤ f → Nat.succ (y % 0) ≤ f) := fun h =>
  absurd (h 5 0 (Nat.zero_le _)) (by decide)

/-! ### 4. `Nat.bitwise` has the same gap, at `n = 0`.

Its binder's type is `Nat.succ (measure (pack f (n/2) (m/2))) ≤ fuel`, i.e. `n/2 + 1 ≤ f`, and
`reflects_fuel_bitwise` enters at `(a+1, a, b)` as well.  For `n ≥ 1` the invariant `n ≤ f`
suffices; at `n = 0` it asks for `1 ≤ f`, and the entry state for `Nat.bitwise g 0 b` is
`f = 0`. -/

example : ∀ n f : Nat, n ≠ 0 → n ≤ f → Nat.succ (n / 2) ≤ f := by
  intro n f hn hf
  have : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
  omega

example : ¬ (Nat.succ (0 / 2) ≤ 0) := by decide
