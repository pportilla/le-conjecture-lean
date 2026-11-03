/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CoordinateJetOrder
public import OnLeConjecture.PlaneCurve.ParametricMorse

/-!
# Regular order two and the parametric Morse form

This file shows that regularity of order two in the first coordinate supplies
every hypothesis of the parametric Morse lemma.
-/

public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- A plane germ regular of order two in the first coordinate admits the
parametric Morse normal form. -/
theorem exists_parametric_morse_normal_form_of_regular_order_two
    (g : Germ 2)
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder g 2) :
    ∃ (e : PointedEquivGerm 2) (h : Germ 1),
      e.pullbackAlgEquiv g =
        Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.hyperplaneExtension 1 h ∧
      (∀ q : Germ 1,
        e.pullbackAlgEquiv (Germ.hyperplaneExtension 1 q) =
          Germ.hyperplaneExtension 1 q) ∧
      e.forward.1.component (1 : Fin 2) =
        Germ.coordinate (1 : Fin 2) ∧
      h ∈ Germ.maximalIdeal 1 := by
  have hcoeff := Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular
  have hg : g ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    have hzero := hcoeff.2 0 (by omega)
    rw [Germ.value_firstCoordinateTaylorCoefficient] at hzero
    simpa using hzero
  have hfirst : Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2) g) = 0 := by
    rw [Germ.value_partialDerivative_zero_eq_value_tail]
    have hzero := hcoeff.2 1 (by omega)
    rw [Germ.value_firstCoordinateTaylorCoefficient] at hzero
    simpa [Germ.firstCoordinateTailIterate_succ] using hzero
  have hsecond : Germ.valueRingHom 2
      (Germ.partialDerivative (0 : Fin 2)
        (Germ.partialDerivative (0 : Fin 2) g)) ≠ 0 := by
    rw [Germ.value_secondPartialDerivative_zero_eq_two_mul_value_tailIterate]
    have hnonzero := hcoeff.1
    rw [Germ.value_firstCoordinateTaylorCoefficient] at hnonzero
    exact mul_ne_zero (by norm_num) hnonzero
  exact exists_parametric_morse_normal_form g hg hfirst hsecond

end OnLeConjecture.PlaneCurve
