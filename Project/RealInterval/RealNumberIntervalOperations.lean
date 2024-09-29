import Project.RealInterval.Basic

namespace RealInterval

-- Scalar multiplication of intervals using Mathlib's scalar multiplication
noncomputable instance : SMul ℝ Interval :=
  ⟨λ c x ↦ {
    inf := min (c * x.inf) (c * x.sup),
    sup := max (c * x.inf) (c * x.sup),
    inf_leq_sup := min_le_max
  }⟩

end RealInterval
