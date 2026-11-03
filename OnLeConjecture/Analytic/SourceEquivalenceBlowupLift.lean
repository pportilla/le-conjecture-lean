/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupPolar
public import OnLeConjecture.Analytic.ParameterTranslationBlowup

/-!
# Analytic blowup lifts of source equivalences fixing the parameter

For an arbitrary pointed analytic source equivalence fixing the second
coordinate, division by the exceptional equation constructs its lift in
every finite tangent chart. The center changes by the affine map determined
by the original first coordinate's linear coefficients. The lifted first
derivative is the pulled-back original first derivative, so the analytic
inverse function theorem proves that the lift is an equivalence.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The finite tangent-center map of a source equivalence fixing the
second coordinate, expressed by the first coordinate's linear part. -/
@[expose] noncomputable def finiteChartCenter (e : PointedEquivGerm 2) (ζ : ℂ) : ℂ :=
  valueRingHom 2 (partialDerivative (0 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (0 : Fin 2)))) * ζ +
  valueRingHom 2 (partialDerivative (1 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (0 : Fin 2))))

theorem coordinateJacobian_eq_firstDerivative_of_preserves_y
    (e : PointedEquivGerm 2)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1) :
    coordinateJacobian e.forward =
      partialDerivative (0 : Fin 2) (e.forward.pullbackRingHom (coordinate (0 : Fin 2))) := by
  rw [coordinateJacobian, ← PointedMapGerm.pullback_coordinate,
    ← PointedMapGerm.pullback_coordinate, hy, jacobian_coordinate_one_right]

theorem firstDerivative_isUnit_of_preserves_y
    (e : PointedEquivGerm 2)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1) :
    IsUnit (partialDerivative (0 : Fin 2)
      (e.forward.pullbackRingHom (coordinate (0 : Fin 2)))) := by
  rw [← coordinateJacobian_eq_firstDerivative_of_preserves_y e hy]
  exact OnLeConjecture.Analytic.Germ.PointedEquivGerm.coordinateJacobian_isUnit e

theorem finiteChartCenter_injective_of_preserves_y
    (e : PointedEquivGerm 2)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1) :
    Function.Injective (finiteChartCenter e) := by
  intro ζ η h
  unfold finiteChartCenter at h
  exact mul_left_cancel₀
    (valueRingHom_ne_zero_of_isUnit (firstDerivative_isUnit_of_preserves_y e hy))
    (add_right_cancel h)

/-- Division by the exceptional coordinate determines the affine image
of the center from the original analytic derivatives. -/
theorem value_pointBlowup_order_one_quotient (ζ : ℂ) (f q : Germ 2)
    (hfactor : (pointBlowupChartGerm ζ).pullbackRingHom f = coordinate (1 : Fin 2) * q) :
    valueRingHom 2 q =
      valueRingHom 2 (partialDerivative (0 : Fin 2) f) * ζ +
        valueRingHom 2 (partialDerivative (1 : Fin 2) f) := by
  have hfactor' : (pointBlowupChartGerm ζ).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ 1 * q := by simpa only [pow_one] using hfactor
  have hx := pointBlowupTransform_partialDerivative_zero ζ 1 (by decide) f q hfactor'
  have hy := pointBlowupTransform_partialDerivative_one ζ 1 (by decide) f q hfactor'
  simp only [Nat.sub_self, pow_zero, Nat.cast_one, one_mul] at hx hy
  have hxv := congrArg (valueRingHom 2) hx
  rw [PointedMapGerm.valueRingHom_pullback] at hxv
  have hyv := congrArg (valueRingHom 2) hy
  simp only [PointedMapGerm.valueRingHom_pullback, map_sub, map_add, map_mul,
    valueRingHom_coordinate, valueRingHom_const, zero_mul, zero_add,
    add_zero] at hyv
  rw [← hxv] at hyv
  linear_combination -hyv

/-- Every finite tangent chart admits an analytic equivalence lift of a
source equivalence fixing the parameter. The exceptional equation is
unchanged, and the lifted Jacobian is the pulled-back original Jacobian. -/
theorem exists_preserves_y_pointBlowup_lift
    (e : PointedEquivGerm 2)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1)
    (ζ : ℂ) :
    ∃ E : PointedEquivGerm 2,
      E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 ∧
      (∀ b : Germ 1, E.forward.pullbackRingHom (hyperplaneExtension 1 b) =
        hyperplaneExtension 1 b) ∧
      e.forward.comp (pointBlowupChartGerm ζ) =
        (pointBlowupChartGerm (finiteChartCenter e ζ)).comp E.forward ∧
      coordinateJacobian E.forward =
        (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) := by
  let f := e.forward.pullbackRingHom (coordinate (0 : Fin 2))
  have hf : f ∈ maximalIdeal 2 ^ 1 := by
    simpa only [pow_one] using
      e.forward.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal (0 : Fin 2))
  obtain ⟨q, hfactor⟩ := exists_pointBlowupChart_factor ζ 1 f hf
  have hx := pointBlowupTransform_partialDerivative_zero ζ 1 (by decide) f q hfactor
  simp only [Nat.sub_self, pow_zero, one_mul] at hx
  simp only [pow_one] at hfactor
  have hcenter : valueRingHom 2 q = finiteChartCenter e ζ :=
    value_pointBlowup_order_one_quotient ζ f q hfactor
  let x' := q - constRingHom 2 (finiteChartCenter e ζ)
  have hx' : x' ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    simp only [x', map_sub, valueRingHom_const, hcenter, sub_self]
  have hpartial : partialDerivative (0 : Fin 2) x' =
      (pointBlowupChartGerm ζ).pullbackRingHom (partialDerivative (0 : Fin 2) f) := by
    simp only [x', partialDerivative_sub, partialDerivative_const, sub_zero]
    exact hx.symm
  have hunit : IsUnit (partialDerivative (0 : Fin 2) x') := by
    rw [hpartial]
    exact (firstDerivative_isUnit_of_preserves_y e hy).map _
  have hdx : differential x' (firstCoordinateVector 1) ≠ 0 := by
    change differential x' (coordinateVector (0 : Fin 2)) ≠ 0
    rw [← valueRingHom_partialDerivative]
    exact valueRingHom_ne_zero_of_isUnit hunit
  obtain ⟨E, hEx, hEa⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension x' hx' hdx
  change E.forward.pullbackRingHom (coordinate (0 : Fin 2)) = x' at hEx
  have hEy := parameterTranslation_preserves_y E hEa
  refine ⟨E, hEy, hEa, ?_, ?_⟩
  · apply PointedMapGerm.ext_components
    intro j
    have hcomponent (B : PointedMapGerm 2 2) :
        B.1.component j = B.pullbackRingHom (coordinate j) := (B.pullback_coordinate j).symm
    rw [hcomponent, hcomponent, PointedMapGerm.pullbackRingHom_comp,
      PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, RingHom.comp_apply]
    fin_cases j
    · change (pointBlowupChartGerm ζ).pullbackRingHom f =
        E.forward.pullbackRingHom ((pointBlowupChartGerm (finiteChartCenter e ζ)).pullbackRingHom
          (coordinate (0 : Fin 2)))
      rw [hfactor, pointBlowupChartGerm_pullback_zero, map_mul, map_add, hEx, hEy,
        PointedMapGerm.pullback_constRingHom]
      simp only [x', sub_add_cancel]
    · change (pointBlowupChartGerm ζ).pullbackRingHom
        (e.forward.pullbackRingHom (coordinate (1 : Fin 2))) =
        E.forward.pullbackRingHom
          ((pointBlowupChartGerm (finiteChartCenter e ζ)).pullbackRingHom (coordinate 1))
      rw [hy, pointBlowupChartGerm_pullback_one, pointBlowupChartGerm_pullback_one, hEy]
  · rw [coordinateJacobian_eq_firstDerivative_of_preserves_y E hEy, hEx, hpartial,
      coordinateJacobian_eq_firstDerivative_of_preserves_y e hy]

end OnLeConjecture.Analytic.Germ
