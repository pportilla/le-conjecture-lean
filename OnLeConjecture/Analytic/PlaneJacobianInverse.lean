/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.JacobianPullback
public import OnLeConjecture.Analytic.Inverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The analytic inverse theorem from a unit plane Jacobian

The value of the coordinate Jacobian is the determinant of the actual
differential. Elementary two-dimensional linear algebra proves that this
differential is bijective, and the analytic inverse theorem constructs
the inverse pointed germ.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

open OnLeConjecture.Analytic.Germ

theorem exists_pointedEquivGerm_of_coordinateJacobian_isUnit
    (g : PointedMapGerm 2 2) (hJ : IsUnit (coordinateJacobian g)) :
    ∃ e : PointedEquivGerm 2, e.forward = g := by
  let a := valueRingHom 2 (partialDerivative (0 : Fin 2) (g.1.component 0))
  let b := valueRingHom 2 (partialDerivative (1 : Fin 2) (g.1.component 0))
  let c := valueRingHom 2 (partialDerivative (0 : Fin 2) (g.1.component 1))
  let d := valueRingHom 2 (partialDerivative (1 : Fin 2) (g.1.component 1))
  have hdet : a * d - b * c ≠ 0 := by
    simpa only [coordinateJacobian, jacobian_eq, map_sub, map_mul] using
      valueRingHom_ne_zero_of_isUnit hJ
  have hcomponent (i : Fin 2) (z : Source 2) :
      g.differential z i =
        valueRingHom 2 (partialDerivative (0 : Fin 2) (g.1.component i)) * z 0 +
        valueRingHom 2 (partialDerivative (1 : Fin 2) (g.1.component i)) * z 1 := by
    have hz : z = z 0 • coordinateVector (0 : Fin 2) + z 1 • coordinateVector (1 : Fin 2) := by
      ext j
      fin_cases j <;> simp [coordinateVector_apply]
    have hscalar : g.differential z i = Germ.differential (g.1.component i) z := by
      rw [MapGerm.germDifferential_component, MapGerm.componentDifferential_apply]
      rfl
    rw [hscalar, hz, map_add, map_smul, map_smul]
    rw [← valueRingHom_partialDerivative, ← valueRingHom_partialDerivative]
    change _ = _ * (z 0 * 1 + z 1 * 0) + _ * (z 0 * 0 + z 1 * 1)
    ring
  have hker (z : Source 2) (hz : g.differential z = 0) : z = 0 := by
    have hzero := congrFun hz 0
    have hone := congrFun hz 1
    rw [hcomponent] at hzero hone
    change a * z 0 + b * z 1 = 0 at hzero
    change c * z 0 + d * z 1 = 0 at hone
    have hx : (a * d - b * c) * z 0 = 0 := by linear_combination d * hzero - b * hone
    have hy : (a * d - b * c) * z 1 = 0 := by linear_combination a * hone - c * hzero
    ext i
    fin_cases i
    · exact (mul_eq_zero.mp hx).resolve_left hdet
    · exact (mul_eq_zero.mp hy).resolve_left hdet
  have hinj : Function.Injective g.differential := by
    intro z w hzw
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hzw, sub_self]
  exact g.exists_pointedEquivGerm_of_differential_bijective
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

end OnLeConjecture.Analytic.PointedMapGerm
