import Project.RealInterval.Basic
-- `one_div_le_one_div_of_le` and `one_div_le_one_div_of_le_of_neg` are used in inv_intervals
import Mathlib.Algebra.Order.Field.Basic

namespace RealInterval

-- Addition of intervals
def add_intervals (x y : Interval) : Interval :=
  {
    inf := x.inf + y.inf,
    sup := x.sup + y.sup,
    inf_leq_sup := by
      exact add_le_add x.inf_leq_sup y.inf_leq_sup
  }

instance : Add Interval where
  add := add_intervals

-- Additive inverse of an interval
def neg_interval (x : Interval) : Interval :=
  {
    inf := -x.sup,
    sup := -x.inf,
    inf_leq_sup := by
      exact neg_le_neg x.inf_leq_sup
  }

instance : Neg Interval where
  neg := neg_interval

instance : Zero Interval where
  zero := {
    inf := 0,
    sup := 0,
    inf_leq_sup := by
      exact le_refl 0
  }

-- Subtraction of intervals
def sub_intervals (x y : Interval) : Interval :=
  x + -y

instance : Sub Interval where
  sub := sub_intervals

-- Multiplication of intervals
noncomputable def mul_intervals (x y : Interval) : Interval :=
  {
    inf := min (min (x.inf * y.inf) (x.inf * y.sup)) (min (x.sup * y.inf) (x.sup * y.sup)),
    sup := max (max (x.inf * y.inf) (x.inf * y.sup)) (max (x.sup * y.inf) (x.sup * y.sup)),
    inf_leq_sup := by
      -- Use the fact that min {a, b, c, d} ≤ max {a, b, c, d}
      let a := x.inf * y.inf
      let b := x.inf * y.sup
      let c := x.sup * y.inf
      let d := x.sup * y.sup
      let m₁ := min a b
      let m₂ := min c d
      let M₁ := max a b
      let M₂ := max c d
      let inf := min m₁ m₂
      let sup := max M₁ M₂
      have h₁ : inf ≤ m₁ := min_le_left _ _
      have h₂ : m₁ ≤ a := min_le_left _ _
      have h₃ : a ≤ M₁ := le_max_left _ _
      have h₄ : M₁ ≤ sup := le_max_left _ _
      exact le_trans h₁ (le_trans h₂ (le_trans h₃ h₄))
  }

-- Assign the operator * to mul_intervals
noncomputable instance : Mul Interval where
  mul := mul_intervals

-- Multiplicative inverse of an interval
noncomputable def inv_interval (x : Interval) : Interval :=
  if h₁ : 0 < x.inf then
    -- In case that `x.inf > 0`
    {
      inf := 1 / x.sup,
      sup := 1 / x.inf,
      inf_leq_sup := by
        have h_inf_pos : 0 < x.inf := h₁
        have h_div : (1 / x.sup) ≤ (1 / x.inf) := one_div_le_one_div_of_le h_inf_pos x.inf_leq_sup
        exact h_div
    }
  else if h₂ : x.sup < 0 then
    -- In case that `x.sup < 0`
    {
      inf := 1 / x.sup,
      sup := 1 / x.inf,
      inf_leq_sup := by
        have h_sup_neg : x.sup < 0 := h₂
        have neg_sup_pos : 0 < -x.sup := neg_pos.mpr h_sup_neg
        have neg_inf_leq_neg_sup : -x.sup ≤ -x.inf := neg_le_neg x.inf_leq_sup

        have h_neg_div : -(1 / x.inf) ≤ -(1 / x.sup) := by
          have h_div_neg_inf : 1 / (-x.inf) = -(1 / x.inf) := one_div_neg_eq_neg_one_div x.inf
          have h_div_neg_sup : 1 / (-x.sup) = -(1 / x.sup) := one_div_neg_eq_neg_one_div x.sup
          rw [←h_div_neg_inf, ←h_div_neg_sup]
          exact one_div_le_one_div_of_le neg_sup_pos neg_inf_leq_neg_sup

        have h_div : (1 / x.sup) ≤ (1 / x.inf) := by
          rw [←neg_neg (1 / x.sup), ←neg_neg (1 / x.inf)]
          exact neg_le_neg h_neg_div

        exact h_div
    }
  else
    -- In case that `x.inf ≤ 0 ≤ x.sup`
    -- This case is zero division, so we set the result to zero singleton interval
    {
      inf := 0,
      sup := 0,
      inf_leq_sup := by
        exact le_refl 0
    }

noncomputable instance : Inv Interval where
  inv := inv_interval

instance : One Interval where
  one := {
    inf := 1,
    sup := 1,
    inf_leq_sup := by
      exact le_refl 1
  }

end RealInterval
