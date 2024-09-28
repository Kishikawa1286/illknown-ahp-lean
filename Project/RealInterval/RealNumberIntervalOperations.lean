import Project.RealInterval.Basic

namespace RealInterval

-- Equality of a real number and an interval
def eq (c : ℝ) (x : Interval) : Prop :=
  c == x.inf ∧ c == x.sup

notation c "==" x => eq c x
notation x "==" c => eq c x

-- Subset or equal relation for intervals
def subseteq (x y : Interval) : Prop :=
  x.inf ≥ y.inf ∧ x.sup ≤ y.sup

notation x "⊆" y => subseteq x y
notation y "⊇" x => subseteq x y

-- Subset relation for intervals (excluding equality)
def subset (x y : Interval) : Prop :=
  subseteq x y ∧ ¬(x == y)

-- Define the subset and subset operators
notation x "⊂" y => subset x y
notation y "⊃" x => subset x y

-- Define the in operator for real numbers and intervals
def included (x : ℝ) (i : Interval) : Prop :=
  i.inf ≤ x ∧ x ≤ i.sup

notation x "∈" i => included x i
notation x "∉" i => ¬included x i
notation i "∋" x => included x i
notation i "∌" x => ¬included x i

-- Scalar multiplication of intervals using min and max
noncomputable def scalarMul (c : ℝ) (x : Interval) : Interval :=
  {
    inf := min (c * x.inf) (c * x.sup),
    sup := max (c * x.inf) (c * x.sup),
    inf_leq_sup := by
      apply min_le_max
  }

notation c "*" x => scalarMul c x
notation x "*" c => scalarMul c x

end RealInterval
