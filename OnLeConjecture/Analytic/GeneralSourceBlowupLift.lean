/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SourceDivisorEquivalenceBlowupLift
public import OnLeConjecture.Analytic.PlaneJacobianInverse

/-!
# Blowup lifts under the finite tangent condition

Both coordinate pullbacks of an arbitrary pointed source equivalence
are divided by the exceptional equation. Nonvanishing of the second
quotient's value is precisely the finite tangent condition. Their quotient
constructs the first lifted coordinate. The commuting square yields the
Jacobian identity, and the analytic inverse theorem makes the lift an
equivalence. No preserved source divisor or atlas compatibility is assumed.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The second coordinate of the image tangent vector `(ζ,1)`. -/
@[expose] noncomputable def finiteTangentDenominator (e : PointedEquivGerm 2) (ζ : ℂ) : ℂ :=
  valueRingHom 2 (partialDerivative (0 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (1 : Fin 2)))) * ζ +
  valueRingHom 2 (partialDerivative (1 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (1 : Fin 2))))

/-- The image center when the image tangent vector lies in the finite chart. -/
@[expose] noncomputable def generalFiniteChartCenter (e : PointedEquivGerm 2) (ζ : ℂ) : ℂ :=
  finiteChartCenter e ζ / finiteTangentDenominator e ζ

/-- An arbitrary pointed source equivalence lifts analytically in every
finite chart whose image tangent is finite. The exceptional unit is the
constructed second divided coordinate. -/
theorem exists_pointBlowup_lift_of_finite_tangent
    (e : PointedEquivGerm 2) (ζ : ℂ)
    (hfinite : finiteTangentDenominator e ζ ≠ 0) :
    ∃ Q U : Germ 2, ∃ E : PointedEquivGerm 2,
      IsUnit U ∧
      (pointBlowupChartGerm ζ).pullbackRingHom
        (e.forward.pullbackRingHom (coordinate (0 : Fin 2))) = coordinate 1 * Q ∧
      (pointBlowupChartGerm ζ).pullbackRingHom
        (e.forward.pullbackRingHom (coordinate (1 : Fin 2))) = coordinate 1 * U ∧
      generalFiniteChartCenter e ζ = valueRingHom 2 Q / valueRingHom 2 U ∧
      U * (E.forward.pullbackRingHom (coordinate (0 : Fin 2)) +
        constRingHom 2 (generalFiniteChartCenter e ζ)) = Q ∧
      E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U ∧
      e.forward.comp (pointBlowupChartGerm ζ) =
        (pointBlowupChartGerm (generalFiniteChartCenter e ζ)).comp E.forward ∧
      (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) =
        U * coordinateJacobian E.forward := by
  let f := e.forward.pullbackRingHom (coordinate (0 : Fin 2))
  let h := e.forward.pullbackRingHom (coordinate (1 : Fin 2))
  have hfirst : f ∈ maximalIdeal 2 ^ 1 := by
    simpa only [pow_one] using
      e.forward.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal (0 : Fin 2))
  have hsecond : h ∈ maximalIdeal 2 ^ 1 := by
    simpa only [pow_one] using
      e.forward.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal (1 : Fin 2))
  obtain ⟨Q, hQ⟩ := exists_pointBlowupChart_factor ζ 1 f hfirst
  obtain ⟨U, hUfactor⟩ := exists_pointBlowupChart_factor ζ 1 h hsecond
  simp only [pow_one] at hQ hUfactor
  have hQvalue : valueRingHom 2 Q = finiteChartCenter e ζ :=
    value_pointBlowup_order_one_quotient ζ f Q hQ
  have hUvalue : valueRingHom 2 U = finiteTangentDenominator e ζ :=
    value_pointBlowup_order_one_quotient ζ h U hUfactor
  have hU : IsUnit U := isUnit_of_valueRingHom_ne_zero (hUvalue ▸ hfinite)
  obtain ⟨W, hUW⟩ := hU.exists_right_inv
  have hWvalue : valueRingHom 2 W = 1 / valueRingHom 2 U := by
    apply (eq_div_iff (valueRingHom_ne_zero_of_isUnit hU)).mpr
    simpa only [map_mul, map_one, mul_comm] using congrArg (valueRingHom 2) hUW
  let c := generalFiniteChartCenter e ζ
  have hcenter : c = valueRingHom 2 Q / valueRingHom 2 U := by
    rw [hQvalue, hUvalue]
    rfl
  let x' := Q * W - constRingHom 2 c
  have hx' : x' ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    simp only [x', map_sub, map_mul, valueRingHom_const, hWvalue, hcenter,
      div_eq_mul_inv, one_mul, sub_self]
  have hy' : coordinate (1 : Fin 2) * U ∈ maximalIdeal 2 :=
    (maximalIdeal 2).mul_mem_right U (coordinate_mem_maximalIdeal 1)
  obtain ⟨F, hF⟩ := PointedMapGerm.exists_with_components
    (![x', coordinate (1 : Fin 2) * U] : Fin 2 → Germ 2)
    (by
      intro i
      fin_cases i
      · exact hx'
      · exact hy')
  have hFX : F.pullbackRingHom (coordinate (0 : Fin 2)) = x' := by
    rw [PointedMapGerm.pullback_coordinate]
    exact hF 0
  have hFY : F.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U := by
    rw [PointedMapGerm.pullback_coordinate]
    exact hF 1
  have hratio : U * (F.pullbackRingHom (coordinate (0 : Fin 2)) + constRingHom 2 c) = Q := by
    rw [hFX]
    simp only [x', sub_add_cancel]
    calc
      U * (Q * W) = Q * (U * W) := by ring
      _ = Q := by rw [hUW, mul_one]
  have hcomm : e.forward.comp (pointBlowupChartGerm ζ) =
      (pointBlowupChartGerm c).comp F := by
    apply PointedMapGerm.ext_components
    intro j
    have hcomponent (B : PointedMapGerm 2 2) :
        B.1.component j = B.pullbackRingHom (coordinate j) := (B.pullback_coordinate j).symm
    rw [hcomponent, hcomponent, PointedMapGerm.pullbackRingHom_comp,
      PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, RingHom.comp_apply]
    fin_cases j
    · change (pointBlowupChartGerm ζ).pullbackRingHom f =
        F.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom (coordinate (0 : Fin 2)))
      rw [hQ, pointBlowupChartGerm_pullback_zero, map_mul, map_add, hFY,
        PointedMapGerm.pullback_constRingHom, mul_assoc, hratio]
    · change (pointBlowupChartGerm ζ).pullbackRingHom h =
        F.pullbackRingHom ((pointBlowupChartGerm c).pullbackRingHom (coordinate (1 : Fin 2)))
      rw [hUfactor, pointBlowupChartGerm_pullback_one, hFY]
  have hJac : (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) =
      U * coordinateJacobian F := by
    have hJ := congrArg coordinateJacobian hcomm
    rw [coordinateJacobian_comp, coordinateJacobian_comp,
      coordinateJacobian_pointBlowupChartGerm, coordinateJacobian_pointBlowupChartGerm] at hJ
    change (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) * coordinate 1 =
      F.pullbackRingHom (coordinate (1 : Fin 2)) * coordinateJacobian F at hJ
    rw [hFY] at hJ
    apply mul_left_cancel₀ (coordinate_ne_zero (1 : Fin 2))
    calc
      coordinate (1 : Fin 2) *
          (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) =
        (pointBlowupChartGerm ζ).pullbackRingHom (coordinateJacobian e.forward) *
          coordinate (1 : Fin 2) := mul_comm _ _
      _ = (coordinate (1 : Fin 2) * U) * coordinateJacobian F := hJ
      _ = _ := mul_assoc _ _ _
  have hJUnit : IsUnit (coordinateJacobian F) := by
    apply isUnit_of_mul_isUnit_right (x := U)
    rw [← hJac]
    exact (OnLeConjecture.Analytic.Germ.PointedEquivGerm.coordinateJacobian_isUnit e).map _
  obtain ⟨E, hE⟩ := F.exists_pointedEquivGerm_of_coordinateJacobian_isUnit hJUnit
  refine ⟨Q, U, E, hU, hQ, hUfactor, hcenter, ?_, ?_, ?_, ?_⟩ <;> rw [hE]
  · exact hratio
  · exact hFY
  · exact hcomm
  · exact hJac

/-- Distinct finite source tangents with finite images have distinct
target centers. This follows from the original nonzero Jacobian. -/
theorem generalFiniteChartCenter_injective_on_finite_tangents
    (e : PointedEquivGerm 2) (ζ η : ℂ)
    (hζ : finiteTangentDenominator e ζ ≠ 0)
    (hη : finiteTangentDenominator e η ≠ 0)
    (heq : generalFiniteChartCenter e ζ = generalFiniteChartCenter e η) : ζ = η := by
  let a := valueRingHom 2 (partialDerivative (0 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (0 : Fin 2))))
  let b := valueRingHom 2 (partialDerivative (1 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (0 : Fin 2))))
  let c := valueRingHom 2 (partialDerivative (0 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (1 : Fin 2))))
  let d := valueRingHom 2 (partialDerivative (1 : Fin 2)
    (e.forward.pullbackRingHom (coordinate (1 : Fin 2))))
  have hdet : a * d - b * c ≠ 0 := by
    have h := valueRingHom_ne_zero_of_isUnit
      (OnLeConjecture.Analytic.Germ.PointedEquivGerm.coordinateJacobian_isUnit e)
    rw [coordinateJacobian, ← PointedMapGerm.pullback_coordinate,
      ← PointedMapGerm.pullback_coordinate, jacobian_eq, map_sub, map_mul, map_mul] at h
    exact h
  have hcross := (div_eq_div_iff hζ hη).mp heq
  change (a * ζ + b) * (c * η + d) = (a * η + b) * (c * ζ + d) at hcross
  have hprod : (a * d - b * c) * (ζ - η) = 0 := by linear_combination hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hdet)

/-- The strict transform acquires the exceptional-coordinate unit to
the original multiplicity, for the general constructed chart lift. -/
theorem strict_transform_of_general_blowup_lift
    (e E : PointedEquivGerm 2) (ζ c : ℂ) (U : Germ 2)
    (hEy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U)
    (hcomm : e.forward.comp (pointBlowupChartGerm ζ) =
      (pointBlowupChartGerm c).comp E.forward)
    (f F : Germ 2) (m : ℕ)
    (hfactor : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F) :
    (pointBlowupChartGerm ζ).pullbackRingHom (e.forward.pullbackRingHom f) =
      coordinate (1 : Fin 2) ^ m * (U ^ m * E.forward.pullbackRingHom F) := by
  have h := congrArg (fun B : PointedMapGerm 2 2 ↦ B.pullbackRingHom f) hcomm
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at h
  rw [h, hfactor, map_mul, map_pow, hEy, mul_pow, mul_assoc]

/-- Source equivalence and the exceptional unit preserve every ordinary
order threshold of the strict transform. -/
theorem general_blowup_lift_transform_mem_pow_iff
    (E : PointedEquivGerm 2) (U : Germ 2) (hU : IsUnit U) (m k : ℕ) (F : Germ 2) :
    U ^ m * E.forward.pullbackRingHom F ∈ maximalIdeal 2 ^ k ↔
      F ∈ maximalIdeal 2 ^ k := by
  rw [Ideal.unit_mul_mem_iff_mem _ (hU.pow m)]
  exact E.pullback_mem_maximalIdeal_pow_iff F

end OnLeConjecture.Analytic.Germ
