import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Interval.Basic

open Classical

-- Module to define intervals of real numbers
namespace Interval

-- Structure to represent a real interval
structure RealInterval where
  inf : ℝ  -- Lower bound of the interval
  sup : ℝ  -- Upper bound of the interval
  inf_leq_sup : inf ≤ sup  -- inf is less than or equal to sup

-- Equality of intervals
noncomputable instance : BEq RealInterval where
  beq x y := x.inf == y.inf && x.sup == y.sup

-- Check if an interval is a point
def isPoint (x : RealInterval) : Prop :=
  x.inf == x.sup

-- Equality of a real number and an interval
def eqRealInterval (c : ℝ) (x : RealInterval) : Prop :=
  c == x.inf ∧ c == x.sup

notation c "==" x => eqRealInterval c x
notation x "==" c => eqRealInterval c x

-- Subset or equal relation for intervals
def subseteq (x y : RealInterval) : Prop :=
  x.inf ≥ y.inf ∧ x.sup ≤ y.sup

notation x "⊆" y => subseteq x y
notation y "⊇" x => subseteq x y

-- Subset relation for intervals (excluding equality)
def subset (x y : RealInterval) : Prop :=
  subseteq x y ∧ ¬(x == y)

-- Define the subset and subset operators
notation x "⊂" y => subset x y
notation y "⊃" x => subset x y

-- Define the in operator for real numbers and intervals
def inInterval (x : ℝ) (i : RealInterval) : Prop :=
  i.inf ≤ x ∧ x ≤ i.sup

notation x "∈" i => inInterval x i
notation x "∉" i => ¬inInterval x i
notation i "∋" x => inInterval x i
notation i "∌" x => ¬inInterval x i

-- Scalar multiplication of intervals using min and max
noncomputable def scalarMul (c : ℝ) (x : RealInterval) : RealInterval :=
  {
    inf := min (c * x.inf) (c * x.sup),
    sup := max (c * x.inf) (c * x.sup),
    inf_leq_sup := by
      apply min_le_max
  }

notation c "*" x => scalarMul c x
notation x "*" c => scalarMul c x

-- Addition of intervals
def addIntervals (x y : RealInterval) : RealInterval :=
  {
    inf := x.inf + y.inf,
    sup := x.sup + y.sup,
    inf_leq_sup := by
      exact add_le_add x.inf_leq_sup y.inf_leq_sup
  }

-- Assign the operator + to addIntervals
instance : Add RealInterval where
  add := addIntervals

end Interval
