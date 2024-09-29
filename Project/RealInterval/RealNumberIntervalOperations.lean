import Project.RealInterval.Basic

namespace RealInterval

-- Membership of a real number in an interval
instance : Membership ℝ Interval :=
  ⟨λ x α ↦ x.inf ≤ α ∧ α ≤ x.sup⟩

-- Scalar multiplication of intervals using Mathlib's scalar multiplication
noncomputable instance : SMul ℝ Interval :=
  ⟨λ c x ↦ {
    inf := min (c * x.inf) (c * x.sup),
    sup := max (c * x.inf) (c * x.sup),
    inf_leq_sup := min_le_max
  }⟩

end RealInterval
