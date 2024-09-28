import Project.RealInterval.Basic
-- `one_div_le_one_div_of_le` and `one_div_le_one_div_of_le_of_neg` are used in invIntervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace RealInterval

-- Addition of intervals
def addIntervals (x y : Interval) : Interval :=
  {
    inf := x.inf + y.inf,
    sup := x.sup + y.sup,
    inf_leq_sup := by
      exact add_le_add x.inf_leq_sup y.inf_leq_sup
  }

-- Assign the operator + to addIntervals
instance : Add Interval where
  add := addIntervals

-- Additive inverse of an interval
def negIntervals (x : Interval) : Interval :=
  {
    inf := -x.sup,
    sup := -x.inf,
    inf_leq_sup := by
      exact neg_le_neg x.inf_leq_sup
  }

instance : Neg Interval where
  neg := negIntervals

instance : Zero Interval where
  zero := {
    inf := 0,
    sup := 0,
    inf_leq_sup := by
      exact le_refl 0
  }

-- Subtraction of intervals
def subIntervals (x y : Interval) : Interval :=
  x + -y

instance : Sub Interval where
  sub := subIntervals

-- Multiplication of intervals
noncomputable def mulIntervals (x y : Interval) : Interval :=
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

-- Assign the operator * to mulIntervals
noncomputable instance : Mul Interval where
  mul := mulIntervals

-- Proof that 1 / a ≤ 1 / b when a ≤ b and b < 0
lemma one_div_le_one_div_of_le_of_neg {a b : ℝ} (hb : b < 0) (hab : a ≤ b) : (1 / a) ≤ (1 / b) :=
  have ha : a < 0 := lt_of_le_of_lt hab hb
  rw [← one_div_neg_eq_neg_one_div a, ← one_div_neg_eq_neg_one_div b]
  exact one_div_le_one_div_of_le_of_neg hb hab

-- Multiplicative inverse of an interval
noncomputable def invIntervals (x : Interval) : Interval :=
  if h₁ : 0 < x.inf then
    -- In case that x.inf > 0
    {
      inf := 1 / x.sup,
      sup := 1 / x.inf,
      inf_leq_sup := by
        have h_inf_pos : 0 < x.inf := h₁
        have h_sup_pos : 0 < x.sup := lt_of_lt_of_le h_inf_pos x.inf_leq_sup
        have h_div : (1 / x.sup) ≤ (1 / x.inf) := one_div_le_one_div_of_le h_inf_pos x.inf_leq_sup
        exact h_div
    }
  else if h₂ : x.sup < 0 then
    -- In case that x.sup < 0
    {
      inf := 1 / x.inf,
      sup := 1 / x.sup,
      inf_leq_sup := by
        have h_sup_neg : x.sup < 0 := h₂
        have h_inf_neg : x.inf < 0 := lt_of_le_of_lt x.inf_leq_sup h_sup_neg
        have h_neg_inf : x.inf ≤ x.sup := x.inf_leq_sup
        have h_div : (1 / x.inf) ≤ (1 / x.sup) := one_div_le_one_div_of_le_of_neg h_sup_neg h_neg_inf
        exact h_div
    }
  else
    -- In case that 0 ∈ x, the inverse is undefined
    throw $ IO.userError "Inverse is undefined when at least one of the interval bounds is 0"

end RealInterval
