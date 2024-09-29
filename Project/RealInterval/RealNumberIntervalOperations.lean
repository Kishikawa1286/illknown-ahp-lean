import Project.RealInterval.Basic

namespace RealInterval

-- Subset or equal relation for intervals
-- Let x := [xᴸ, xᵁ] and y := [yᴸ, yᵁ]
-- If yᴸ ≤ xᴸ, xᵁ ≤ yᵁ holds, then x ⊆ y
instance : HasSubset Interval :=
  ⟨λ x y ↦ y.inf ≤ x.inf ∧ x.sup ≤ y.sup⟩

-- Strict subset relation for intervals (excluding equality)
-- Let x := [xᴸ, xᵁ] and y := [yᴸ, yᵁ]
-- If yᴸ ≤ xᴸ, xᵁ ≤ yᵁ and x ≠ y holds, then x ⊂ y
instance : HasSSubset Interval :=
  ⟨λ x y ↦ x ⊆ y ∧ ¬(x == y)⟩

-- Scalar multiplication of intervals using Mathlib's scalar multiplication
noncomputable instance : SMul ℝ Interval :=
  ⟨λ c x ↦ {
    inf := min (c * x.inf) (c * x.sup),
    sup := max (c * x.inf) (c * x.sup),
    inf_leq_sup := min_le_max
  }⟩

end RealInterval
