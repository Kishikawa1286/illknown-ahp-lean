import Project.RealInterval.Basic

namespace RealInterval

instance : PartialOrder Interval where
  le x y := x.inf ≤ y.inf ∧ x.sup ≤ y.sup

  le_refl x := ⟨le_refl x.inf, le_refl x.sup⟩

  le_trans x y z :=
    λ ⟨h1_inf, h1_sup⟩ ⟨h2_inf, h2_sup⟩ ↦ ⟨le_trans h1_inf h2_inf, le_trans h1_sup h2_sup⟩

  le_antisymm x y hxy hyyx :=
    by
      have h_inf : x.inf = y.inf := le_antisymm hxy.1 hyyx.1
      have h_sup : x.sup = y.sup := le_antisymm hxy.2 hyyx.2
      exact eq_of_inf_sup_eq h_inf h_sup

end RealInterval
