/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MapGerm

/-!
# The contradiction formulation of Lê's conjecture

The final theorem is equivalent to excluding every injective representative
whose differential is zero. This is the form produced by the separate
normal form contradictions.
-/

public section

namespace OnLeConjecture.Analytic

/-- Lê's conjecture is equivalent to the exclusion of injective map germs
with zero differential. -/
theorem leConjecture_iff_no_injective_zero_differential :
    LeConjecture ↔
      ∀ g : PointedMapGerm 2 3,
        g.differential = 0 → ¬ g.HasInjectiveRepresentative := by
  constructor
  · intro h g hdifferential hinjective
    exact (h g hinjective) hdifferential
  · intro h g hinjective hdifferential
    exact h g hdifferential hinjective

/-- It suffices to exclude an injective representative for every map germ
with zero differential. -/
theorem leConjecture_of_no_injective_zero_differential
    (h : ∀ g : PointedMapGerm 2 3,
      g.differential = 0 → ¬ g.HasInjectiveRepresentative) :
    LeConjecture :=
  leConjecture_iff_no_injective_zero_differential.mpr h

end OnLeConjecture.Analytic
