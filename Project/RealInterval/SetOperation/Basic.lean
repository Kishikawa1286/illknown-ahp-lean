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

-- Hull of two intervals
-- Let x := [xᴸ, xᵁ] and y := [yᴸ, yᵁ]
-- The hull of x and y is defined as [min(xᴸ, yᴸ), max(xᵁ, yᵁ)]
noncomputable def intervals_hull (x y : Interval) : Interval :=
  {
    inf := min x.inf y.inf,
    sup := max x.sup y.sup,
    inf_leq_sup := by
      have h1 : min x.inf y.inf ≤ x.inf := min_le_left x.inf y.inf
      have h2 : x.inf ≤ x.sup := x.inf_leq_sup
      have h3 : x.sup ≤ max x.sup y.sup := le_max_left x.sup y.sup
      exact le_trans h1 (le_trans h2 h3)
  }

end RealInterval
