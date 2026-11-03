/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrderTwoPreparation

/-!
# The deviation of an implicit branch

For an equation with nonzero derivative in the first variable, its
restriction to the parameter axis is, on any pointed solution, the first
coordinate times an analytic unit. The value of that unit is the negative
first derivative of the equation. Thus this factorization also controls
the first nonzero coefficient of an implicit branch.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem firstCoordinateTail_isUnit_of_differential_ne_zero
    (F : Germ 2) (hF : differential F (firstCoordinateVector 1) ≠ 0) :
    IsUnit (firstCoordinateTail F) := by
  apply isUnit_of_valueRingHom_ne_zero
  rw [← value_partialDerivative_firstCoordinate, valueRingHom_partialDerivative]
  exact hF

/-- The parameter-axis defect is the first coordinate times a unit along
any pointed solution of an equation with nonzero first derivative. -/
theorem exists_implicit_defect_unit
    {n : ℕ} (F : Germ 2) (hF : differential F (firstCoordinateVector 1) ≠ 0)
    (φ : PointedMapGerm n 2) (hsolution : φ.pullbackRingHom F = 0) :
    ∃ u : Germ n, IsUnit u ∧
      φ.pullbackRingHom (hyperplaneExtension 1 (hyperplaneRestriction 1 F)) =
        φ.pullbackRingHom (coordinate (0 : Fin 2)) * u ∧
      valueRingHom n u = -differential F (firstCoordinateVector 1) := by
  let u : Germ n := -φ.pullbackRingHom (firstCoordinateTail F)
  have hu : IsUnit u :=
    ((firstCoordinateTail_isUnit_of_differential_ne_zero F hF).map φ.pullbackRingHom).neg
  refine ⟨u, hu, ?_, ?_⟩
  · have h := congrArg φ.pullbackRingHom (firstCoordinate_decomposition F)
    rw [hsolution, map_add, map_mul, firstCoordinateCoefficient] at h
    dsimp only [u]
    linear_combination -h
  · simp only [u, map_neg, PointedMapGerm.valueRingHom_pullback,
      ← value_partialDerivative_firstCoordinate, valueRingHom_partialDerivative]
    rfl

end OnLeConjecture.Analytic.Germ
