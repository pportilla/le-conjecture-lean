/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SourceEquivalenceBlowupLift
public import OnLeConjecture.Analytic.UnitCoordinateScaling
public import OnLeConjecture.Analytic.AnalyticPointBasis

/-!
# Analytic blowup lifts preserving a smooth divisor up to a unit

If a source equivalence sends the second coordinate to itself times an
analytic unit, its lift in every finite tangent chart is constructed
analytically. The exceptional coordinate acquires exactly the pullback
of that unit. The center is determined by the original linear part.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem firstDerivative_value_ne_zero_of_preserves_y_mul_unit
    (e : PointedEquivGerm 2) (V : Germ 2)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * V) :
    valueRingHom 2 (partialDerivative (0 : Fin 2)
      (e.forward.pullbackRingHom (coordinate (0 : Fin 2)))) ≠ 0 := by
  have h := valueRingHom_ne_zero_of_isUnit
    (OnLeConjecture.Analytic.Germ.PointedEquivGerm.coordinateJacobian_isUnit e)
  rw [coordinateJacobian, ← PointedMapGerm.pullback_coordinate,
    ← PointedMapGerm.pullback_coordinate, hy, jacobian_eq] at h
  simp only [partialDerivative_mul, partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1),
    map_sub, map_mul, map_add, valueRingHom_coordinate,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero, one_mul] at h
  exact (mul_ne_zero_iff.mp h).1

/-- The affine finite-center map when the second coordinate acquires
the analytic unit `V`. -/
@[expose] noncomputable def divisorFiniteChartCenter
    (e : PointedEquivGerm 2) (V : Germ 2) (ζ : ℂ) : ℂ :=
  finiteChartCenter e ζ / valueRingHom 2 V

theorem divisorFiniteChartCenter_injective
    (e : PointedEquivGerm 2) (V : Germ 2) (hV : IsUnit V)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * V) :
    Function.Injective (divisorFiniteChartCenter e V) := by
  intro ζ η h
  have hcenter : finiteChartCenter e ζ = finiteChartCenter e η :=
    (div_left_inj' (valueRingHom_ne_zero_of_isUnit hV)).mp h
  unfold finiteChartCenter at hcenter
  exact mul_left_cancel₀ (firstDerivative_value_ne_zero_of_preserves_y_mul_unit e V hy)
    (add_right_cancel hcenter)

/-- An analytic source equivalence preserving `y=0` lifts to an analytic
equivalence of every finite chart. The exceptional-coordinate unit and
the Jacobian relation are computed from the original equivalence. -/
theorem exists_preserves_y_unit_pointBlowup_lift
    (e : PointedEquivGerm 2) (V : Germ 2) (hV : IsUnit V)
    (hy : e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * V)
    (ζ : ℂ) :
    ∃ E : PointedEquivGerm 2,
      E.forward.pullbackRingHom (coordinate (1 : Fin 2)) =
        coordinate 1 * (pointBlowupChartGerm ζ).pullbackRingHom V ∧
      e.forward.comp (pointBlowupChartGerm ζ) =
        (pointBlowupChartGerm (divisorFiniteChartCenter e V ζ)).comp E.forward ∧
      (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) =
        (pointBlowupChartGerm ζ).pullbackRingHom V * coordinateJacobian E.forward := by
  let f := e.forward.pullbackRingHom (coordinate (0 : Fin 2))
  have hf : f ∈ maximalIdeal 2 ^ 1 := by
    simpa only [pow_one] using
      e.forward.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal (0 : Fin 2))
  obtain ⟨q, hfactor⟩ := exists_pointBlowupChart_factor ζ 1 f hf
  have hx := pointBlowupTransform_partialDerivative_zero ζ 1 (by decide) f q hfactor
  simp only [Nat.sub_self, pow_zero, one_mul] at hx
  simp only [pow_one] at hfactor
  obtain ⟨W, hVW⟩ := hV.exists_right_inv
  have hW : IsUnit W := isUnit_iff_exists_inv.mpr ⟨V, by simpa only [mul_comm] using hVW⟩
  have hWvalue : valueRingHom 2 W = 1 / valueRingHom 2 V := by
    apply (eq_div_iff (valueRingHom_ne_zero_of_isUnit hV)).mpr
    simpa only [map_mul, map_one, mul_comm] using congrArg (valueRingHom 2) hVW
  let c := divisorFiniteChartCenter e V ζ
  let x' := q * (pointBlowupChartGerm ζ).pullbackRingHom W - constRingHom 2 c
  have hcenter : valueRingHom 2 q * valueRingHom 2 W = c := by
    rw [value_pointBlowup_order_one_quotient ζ f q hfactor, hWvalue]
    change finiteChartCenter e ζ * (1 / valueRingHom 2 V) = _
    simp only [c, divisorFiniteChartCenter, div_eq_mul_inv, one_mul]
  have hx' : x' ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    simp only [x', map_sub, map_mul, PointedMapGerm.valueRingHom_pullback,
      valueRingHom_const, hcenter, sub_self]
  have hWpartial : valueRingHom 2 (partialDerivative (0 : Fin 2)
      ((pointBlowupChartGerm ζ).pullbackRingHom W)) = 0 := by
    rw [partialDerivative_zero_pointBlowupChart_pullback, map_mul,
      valueRingHom_coordinate, zero_mul]
  have hxvalue := congrArg (valueRingHom 2) hx
  rw [PointedMapGerm.valueRingHom_pullback] at hxvalue
  have hdxvalue : valueRingHom 2 (partialDerivative (0 : Fin 2) x') =
      valueRingHom 2 (partialDerivative (0 : Fin 2) f) * valueRingHom 2 W := by
    simp only [x', partialDerivative_sub, partialDerivative_mul, partialDerivative_const,
      map_add, map_mul, sub_zero, PointedMapGerm.valueRingHom_pullback,
      hWpartial, mul_zero, add_zero, ← hxvalue]
  have hdx : differential x' (firstCoordinateVector 1) ≠ 0 := by
    change differential x' (coordinateVector (0 : Fin 2)) ≠ 0
    rw [← valueRingHom_partialDerivative, hdxvalue]
    exact mul_ne_zero (firstDerivative_value_ne_zero_of_preserves_y_mul_unit e V hy)
      (valueRingHom_ne_zero_of_isUnit hW)
  obtain ⟨a, haX, haCoeff⟩ :=
    exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension x' hx' hdx
  change a.forward.pullbackRingHom (coordinate (0 : Fin 2)) = x' at haX
  have haY := parameterTranslation_preserves_y a haCoeff
  obtain ⟨E, hE⟩ := a.exists_coordinate_mul_units
    (![1, (pointBlowupChartGerm ζ).pullbackRingHom V] : Fin 2 → Germ 2)
    (by
      intro i
      fin_cases i
      · exact isUnit_one
      · exact hV.map _)
  have hEX : E.forward.pullbackRingHom (coordinate (0 : Fin 2)) = x' := by
    simpa only [Matrix.cons_val_zero, haX, mul_one] using hE 0
  have hEY : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinate 1 * (pointBlowupChartGerm ζ).pullbackRingHom V := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_fin_one, haY] using hE 1
  have hVWpull : (pointBlowupChartGerm ζ).pullbackRingHom V *
      (pointBlowupChartGerm ζ).pullbackRingHom W = 1 := by
    rw [← map_mul, hVW, map_one]
  have hcomm : e.forward.comp (pointBlowupChartGerm ζ) =
      (pointBlowupChartGerm c).comp E.forward := by
    apply PointedMapGerm.ext_components
    intro j
    have hcomponent (B : PointedMapGerm 2 2) :
        B.1.component j = B.pullbackRingHom (coordinate j) := (B.pullback_coordinate j).symm
    rw [hcomponent, hcomponent, PointedMapGerm.pullbackRingHom_comp,
      PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, RingHom.comp_apply]
    fin_cases j
    · change (pointBlowupChartGerm ζ).pullbackRingHom f =
        E.forward.pullbackRingHom
          ((pointBlowupChartGerm c).pullbackRingHom (coordinate (0 : Fin 2)))
      rw [hfactor, pointBlowupChartGerm_pullback_zero, map_mul, map_add, hEX, hEY,
        PointedMapGerm.pullback_constRingHom]
      simp only [x', sub_add_cancel]
      calc
        coordinate 1 * q = coordinate 1 * q *
            ((pointBlowupChartGerm ζ).pullbackRingHom V *
              (pointBlowupChartGerm ζ).pullbackRingHom W) := by rw [hVWpull, mul_one]
        _ = _ := by ring
    · change (pointBlowupChartGerm ζ).pullbackRingHom
        (e.forward.pullbackRingHom (coordinate (1 : Fin 2))) =
        E.forward.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom (coordinate 1))
      rw [hy, map_mul, pointBlowupChartGerm_pullback_one, pointBlowupChartGerm_pullback_one, hEY]
  refine ⟨E, hEY, hcomm, ?_⟩
  have hJac := congrArg coordinateJacobian hcomm
  rw [coordinateJacobian_comp, coordinateJacobian_comp,
    coordinateJacobian_pointBlowupChartGerm, coordinateJacobian_pointBlowupChartGerm] at hJac
  change (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) * coordinate 1 =
    E.forward.pullbackRingHom (coordinate (1 : Fin 2)) * coordinateJacobian E.forward at hJac
  rw [hEY] at hJac
  apply mul_left_cancel₀ (coordinate_ne_zero (1 : Fin 2))
  calc
    coordinate (1 : Fin 2) *
        (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) =
      (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) *
        coordinate (1 : Fin 2) := mul_comm _ _
    _ = (coordinate (1 : Fin 2) * (pointBlowupChartGerm ζ).pullbackRingHom V) *
        coordinateJacobian E.forward := hJac
    _ = _ := mul_assoc _ _ _

/-- The commuting chart square transports the strict transform with
the exceptional-coordinate unit raised to the original multiplicity. -/
theorem strict_transform_of_y_unit_blowup_lift
    (e E : PointedEquivGerm 2) (ζ c : ℂ) (V : Germ 2)
    (hEY : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinate 1 * (pointBlowupChartGerm ζ).pullbackRingHom V)
    (hcomm : e.forward.comp (pointBlowupChartGerm ζ) =
      (pointBlowupChartGerm c).comp E.forward)
    (f F : Germ 2) (m : ℕ)
    (hfactor : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F) :
    (pointBlowupChartGerm ζ).pullbackRingHom (e.forward.pullbackRingHom f) =
      coordinate (1 : Fin 2) ^ m *
        ((pointBlowupChartGerm ζ).pullbackRingHom V ^ m * E.forward.pullbackRingHom F) := by
  have h := congrArg (fun B : PointedMapGerm 2 2 ↦ B.pullbackRingHom f) hcomm
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at h
  rw [h, hfactor, map_mul, map_pow, hEY, mul_pow, mul_assoc]

/-- The transported strict transform has exactly the original ordinary
order, despite the exceptional-coordinate unit. -/
theorem y_unit_lift_transform_mem_pow_iff
    (E : PointedEquivGerm 2) (ζ : ℂ) (V : Germ 2) (hV : IsUnit V)
    (m k : ℕ) (F : Germ 2) :
    (pointBlowupChartGerm ζ).pullbackRingHom V ^ m * E.forward.pullbackRingHom F ∈
      maximalIdeal 2 ^ k ↔ F ∈ maximalIdeal 2 ^ k := by
  rw [Ideal.unit_mul_mem_iff_mem _ ((hV.map _).pow m)]
  exact E.pullback_mem_maximalIdeal_pow_iff F

end OnLeConjecture.Analytic.Germ
