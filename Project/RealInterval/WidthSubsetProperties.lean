import Project.RealInterval.RealNumberIntervalOperations
import Mathlib.Tactic.Linarith

namespace RealInterval

-- Let x and y be intervals
-- If Width(x) < Width(y) holds, then y ⊈ x
theorem width_lt_not_subset {x y : Interval} (h : width x < width y) : ¬(y ⊆ x) :=
  λ h₁ =>
    -- From the assumption y ⊆ x, we get the inequalities y.inf ≥ x.inf and y.sup ≤ x.sup
    have h_inf : y.inf ≥ x.inf := h₁.1
    have h_sup : y.sup ≤ x.sup := h₁.2
    -- Expand the inequality of widths
    have h_width : y.sup - y.inf ≤ x.sup - x.inf :=
      sub_le_sub h_sup h_inf
    -- Derive a contradiction from the assumption h and h_width
    have h_width_x_lt_width_y : width x < width y := h
    have h_width_y_leq_width_x : width y ≤ width x := h_width
    -- This leads to the contradiction width y < width y
    have h_contra : width y < width y := lt_of_le_of_lt h_width_y_leq_width_x h_width_x_lt_width_y
    -- Apply the irreflexivity of less-than to derive the contradiction
    lt_irrefl (width y) h_contra

-- Let x and y be intervals
-- If Width(x) ≤ Width(y) holds, then y ⊄ x
theorem width_le_not_subset {x y : Interval} (h : width x ≤ width y) : ¬(y ⊂ x) :=
  λ h₁ =>
    -- `h₁: y ⊂ x`, which means `y ⊆ x` and `y ≠ x`
    have h_subset : y ⊆ x := h₁.1
    have h_bneq : ¬(y == x) := h₁.2
    -- From `y ⊆ x`, we have `x.inf ≤ y.inf` and `y.sup ≤ x.sup`
    have h_inf : x.inf ≤ y.inf := h_subset.1
    have h_sup : y.sup ≤ x.sup := h_subset.2
    -- Compute width
    have h_width_y : width y = y.sup - y.inf := rfl
    have h_width_x : width x = x.sup - x.inf := rfl
    -- From `y ⊆ x`, width `y ≤ width x`
    have h_width_ge : width y ≤ width x := sub_le_sub h_sup h_inf
    -- From `h` and `h_width_ge`, we have width `y = width x`
    have h_width_eq : width y = width x := le_antisymm h_width_ge h
    -- Substitute back to get `y.sup - y.inf = x.sup - x.inf`
    have h_eq_width : y.sup - y.inf = x.sup - x.inf := by rw [←h_width_y, h_width_eq, h_width_x]
    -- From `y.sup - y.inf = x.sup - x.inf`, `y.sup ≤ x.sup` and `x.inf ≤ y.inf`,
    -- it follows that `y.sup = x.sup` and `y.inf = x.inf`
    have h_diff : x.sup - y.sup = y.inf - x.inf := by linarith [h_eq_width]
    have h_eq_zero : x.sup - y.sup = 0 := by linarith [h_diff, h_sup, h_inf]
    have h_sup_eq : y.sup = x.sup := by linarith [h_eq_zero]
    have h_inf_eq : y.inf = x.inf := by linarith [h_eq_zero]
    -- Thus `y == x`
    have h_beq : y == x := by
      simp [BEq.beq, Interval] at *
      exact And.intro h_inf_eq h_sup_eq
    -- `y == x` is a contradiction to the assumption `¬(y == x)`
    show False from h_bneq h_beq

end RealInterval
