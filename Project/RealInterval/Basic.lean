import Mathlib.Data.Real.Basic

namespace RealInterval

-- Structure to represent a real closed interval
-- In this project, `Interval` is:
-- 1. non-empty set
-- 2. closed (includes both bounds)
-- 3. subset of ℝ
structure Interval where
  inf : ℝ  -- Lower bound of the interval
  sup : ℝ  -- Upper bound of the interval
  inf_leq_sup : inf ≤ sup  -- inf is less than or equal to sup

-- Equality of intervals
-- Two intervals are equal if their lower and upper bounds are equal
noncomputable instance : DecidableEq Interval :=
  λ x y =>
    if h : x.inf = y.inf ∧ x.sup = y.sup then
      isTrue (by cases x; cases y; cases h; congr)
    else
     isFalse (by
        intro eq
        cases x
        cases y
        injection eq with h1 h2
        apply h
        exact ⟨h1, h2⟩)

-- If two intervals have the same lower and upper bounds, they are equal
theorem eq_of_inf_sup_eq {x y : Interval}
    (h_inf : x.inf = y.inf)
    (h_sup : x.sup = y.sup) :
    x = y := by
  cases x
  cases y
  cases h_inf
  cases h_sup
  rfl

-- Reflexivity of interval equality
theorem interval_eq_refl (x : Interval) : x = x :=
  by
    cases x
    rfl

-- Symmetry of interval equality
theorem interval_eq_symm {x y : Interval} (h : x = y) : y = x :=
  by
    rw [h]

-- Transitivity of interval equality
theorem interval_eq_trans {x y z : Interval} (hxy : x = y) (hyz : y = z) : x = z :=
  by
    rw [hxy, hyz]

-- If two intervals are equal, their lower and upper bounds are equal
theorem inf_sup_eq_of_eq {x y : Interval} (h : x = y) : x.inf = y.inf ∧ x.sup = y.sup :=
  by
    cases x
    cases y
    injection h with h1 h2
    exact ⟨h1, h2⟩

-- Decidability of interval equality
theorem decidable_eq_interval (x y : Interval) : (x = y) ∨ (x ≠ y) :=
  Decidable.em (x = y)

-- Interval equality is an equivalence relation
instance : Setoid Interval :=
{
  r := (λ x y ↦ x = y),
  iseqv := ⟨
    interval_eq_refl,
    interval_eq_symm,
    interval_eq_trans
  ⟩
}

-- Interval is non-empty set
instance : Nonempty Interval :=
  ⟨{
    inf := 0,
    sup := 0,
    inf_leq_sup := by
      exact le_refl 0
  }⟩

-- Check if an interval is a singleton
def is_singleton (x : Interval) : Prop :=
  x.inf == x.sup

-- Width of an interval
-- Let x := [xᴸ, xᵁ]
-- The width of x is defined as xᵁ - xᴸ
def width (x : Interval) : ℝ :=
  x.sup - x.inf

end RealInterval
