import Mathlib.Data.Real.Basic

namespace RealInterval

-- Structure to represent a real interval
structure Interval where
  inf : ℝ  -- Lower bound of the interval
  sup : ℝ  -- Upper bound of the interval
  inf_leq_sup : inf ≤ sup  -- inf is less than or equal to sup

-- Equality of intervals
noncomputable instance : BEq Interval where
  beq x y := x.inf == y.inf && x.sup == y.sup

-- Check if an interval is a singleton
def isSingleton (x : Interval) : Prop :=
  x.inf == x.sup

end RealInterval
