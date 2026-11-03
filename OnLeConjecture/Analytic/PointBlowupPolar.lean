/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupChart
public import OnLeConjecture.Analytic.JacobianPullback
public import OnLeConjecture.PlaneCurve.Intersection

/-!
# Derivatives and polar ideals in an analytic point blowup chart

For the chart `(x,y) ↦ (y(x+c),y)`, an actual factor identity
`pullback f = y^m F` determines the pullbacks of both partial derivatives.
The resulting identities describe the transformed Jacobian and polar
ideal. They do not assert an intersection sum over resolution centers.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Differentiation along the exceptional coordinate in the point blowup
chart contributes one factor of the exceptional equation. -/
theorem partialDerivative_zero_pointBlowupChart_pullback (c : ℂ) (f : Germ 2) :
    partialDerivative (0 : Fin 2) ((pointBlowupChartGerm c).pullbackRingHom f) =
      coordinate (1 : Fin 2) *
        (pointBlowupChartGerm c).pullbackRingHom (partialDerivative (0 : Fin 2) f) := by
  rw [PointedMapGerm.pullbackRingHom_apply, partialDerivative_compPointed]
  rw [← PointedMapGerm.pullback_coordinate, ← PointedMapGerm.pullback_coordinate,
    pointBlowupChartGerm_pullback_zero, pointBlowupChartGerm_pullback_one]
  simp only [partialDerivative_mul, partialDerivative_add, partialDerivative_const,
    partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1),
    zero_mul, mul_zero, zero_add, add_zero, mul_one]
  exact mul_comm _ _

/-- Differentiation in the exceptional normal coordinate has both chain
rule terms. -/
theorem partialDerivative_one_pointBlowupChart_pullback (c : ℂ) (f : Germ 2) :
    partialDerivative (1 : Fin 2) ((pointBlowupChartGerm c).pullbackRingHom f) =
      (coordinate (0 : Fin 2) + constRingHom 2 c) *
          (pointBlowupChartGerm c).pullbackRingHom (partialDerivative (0 : Fin 2) f) +
        (pointBlowupChartGerm c).pullbackRingHom (partialDerivative (1 : Fin 2) f) := by
  rw [PointedMapGerm.pullbackRingHom_apply, partialDerivative_compPointed]
  rw [← PointedMapGerm.pullback_coordinate, ← PointedMapGerm.pullback_coordinate,
    pointBlowupChartGerm_pullback_zero, pointBlowupChartGerm_pullback_one]
  simp only [partialDerivative_mul, partialDerivative_add, partialDerivative_const,
    partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide : (1 : Fin 2) ≠ 0),
    mul_zero, add_zero, mul_one, one_mul]
  rw [mul_comm]
  rfl

/-- The analytic point blowup chart has coordinate Jacobian `y`. -/
theorem coordinateJacobian_pointBlowupChartGerm (c : ℂ) :
    coordinateJacobian (pointBlowupChartGerm c) = coordinate (1 : Fin 2) := by
  rw [coordinateJacobian, ← PointedMapGerm.pullback_coordinate,
    ← PointedMapGerm.pullback_coordinate,
    pointBlowupChartGerm_pullback_zero, pointBlowupChartGerm_pullback_one,
    jacobian_coordinate_one_right, partialDerivative_mul, partialDerivative_add]
  simp only [partialDerivative_const, partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1),
    zero_mul, zero_add, add_zero, mul_one]

/-- The Jacobian of the two pulled-back germs has one additional
exceptional factor from the coordinate change. -/
theorem jacobian_pointBlowupChart_pullback (c : ℂ) (f g : Germ 2) :
    jacobian ((pointBlowupChartGerm c).pullbackRingHom f)
        ((pointBlowupChartGerm c).pullbackRingHom g) =
      coordinate (1 : Fin 2) * (pointBlowupChartGerm c).pullbackRingHom (jacobian f g) := by
  change jacobian (compPointed f _) (compPointed g _) = _
  rw [jacobian_compPointed, coordinateJacobian_pointBlowupChartGerm]
  exact mul_comm _ _

/-- The first polar pulls back to the first derivative of the strict
transform times precisely the displayed exceptional power. -/
theorem pointBlowupTransform_partialDerivative_zero
    (c : ℂ) (m : ℕ) (hm : 0 < m) (f F : Germ 2)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F) :
    (pointBlowupChartGerm c).pullbackRingHom (partialDerivative (0 : Fin 2) f) =
      coordinate (1 : Fin 2) ^ (m - 1) * partialDerivative (0 : Fin 2) F := by
  have hderiv := congrArg (partialDerivative (0 : Fin 2)) htransform
  simp only [partialDerivative_zero_pointBlowupChart_pullback, partialDerivative_mul,
    partialDerivative_pow,
    partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1),
    smul_zero, zero_mul, zero_add] at hderiv
  apply mul_left_cancel₀ (coordinate_ne_zero (1 : Fin 2))
  rw [hderiv, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]

/-- The second derivative retains the derivative of the exceptional power
and the change in first coordinate. -/
theorem pointBlowupTransform_partialDerivative_one
    (c : ℂ) (m : ℕ) (hm : 0 < m) (f F : Germ 2)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F) :
    (pointBlowupChartGerm c).pullbackRingHom (partialDerivative (1 : Fin 2) f) =
      coordinate (1 : Fin 2) ^ (m - 1) *
        ((m : Germ 2) * F + coordinate (1 : Fin 2) * partialDerivative (1 : Fin 2) F -
          (coordinate (0 : Fin 2) + constRingHom 2 c) * partialDerivative (0 : Fin 2) F) := by
  have hderiv := congrArg (partialDerivative (1 : Fin 2)) htransform
  rw [partialDerivative_one_pointBlowupChart_pullback, partialDerivative_mul,
    partialDerivative_pow, partialDerivative_coordinate_same, smul_eq_mul, mul_one,
    nsmul_eq_mul, pointBlowupTransform_partialDerivative_zero c m hm f F htransform] at hderiv
  have hpower : coordinate (1 : Fin 2) ^ m =
      coordinate (1 : Fin 2) * coordinate (1 : Fin 2) ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm]
  rw [hpower] at hderiv
  linear_combination hderiv

/-- The transformed Jacobian is determined by the actual two factor
identities. The exceptional exponent is `m+n−2`. -/
theorem pointBlowupTransform_jacobian
    (c : ℂ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (f g F G : Germ 2)
    (hf : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F)
    (hg : (pointBlowupChartGerm c).pullbackRingHom g =
      coordinate (1 : Fin 2) ^ n * G) :
    (pointBlowupChartGerm c).pullbackRingHom (jacobian f g) =
      coordinate (1 : Fin 2) ^ (m + n - 2) *
        (coordinate (1 : Fin 2) * jacobian F G +
          (n : Germ 2) * partialDerivative (0 : Fin 2) F * G -
            (m : Germ 2) * F * partialDerivative (0 : Fin 2) G) := by
  rw [jacobian_eq, map_sub, map_mul, map_mul,
    pointBlowupTransform_partialDerivative_zero c m hm f F hf,
    pointBlowupTransform_partialDerivative_one c n hn g G hg,
    pointBlowupTransform_partialDerivative_one c m hm f F hf,
    pointBlowupTransform_partialDerivative_zero c n hn g G hg]
  have hexponent : m + n - 2 = (m - 1) + (n - 1) := by omega
  rw [hexponent, pow_add, jacobian_eq]
  ring

/-- The total transform of the first polar ideal factors as an exceptional
principal ideal times the ideal generated by `yF` and `F_x`. -/
theorem pointBlowupTransform_polarIdeal
    (c : ℂ) (m : ℕ) (hm : 0 < m) (f F : Germ 2)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * F) :
    Ideal.map (pointBlowupChartGerm c).pullbackRingHom
        (PlaneCurve.pairIdeal f (partialDerivative (0 : Fin 2) f)) =
      Ideal.span {coordinate (1 : Fin 2) ^ (m - 1)} *
        PlaneCurve.pairIdeal (coordinate (1 : Fin 2) * F) (partialDerivative (0 : Fin 2) F) := by
  simp only [PlaneCurve.pairIdeal, Ideal.span_insert, Ideal.map_sup,
    Ideal.map_span, Set.image_singleton,
    htransform, pointBlowupTransform_partialDerivative_zero c m hm f F htransform,
    Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
  congr 3
  rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hm]

/-- The polar formulas apply to the analytic transform constructed from
ordinary order divisibility. No strict-transform identity is an input. -/
theorem constructed_pointBlowupTransform_polar
    (c : ℂ) (m : ℕ) (hm : 0 < m) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) :
    let F := pointBlowupTransform c m f hf
    (pointBlowupChartGerm c).pullbackRingHom (partialDerivative (0 : Fin 2) f) =
        coordinate (1 : Fin 2) ^ (m - 1) * partialDerivative (0 : Fin 2) F ∧
      Ideal.map (pointBlowupChartGerm c).pullbackRingHom
          (PlaneCurve.pairIdeal f (partialDerivative (0 : Fin 2) f)) =
        Ideal.span {coordinate (1 : Fin 2) ^ (m - 1)} *
          PlaneCurve.pairIdeal (coordinate (1 : Fin 2) * F) (partialDerivative (0 : Fin 2) F) := by
  exact ⟨pointBlowupTransform_partialDerivative_zero c m hm f _
      (pointBlowupTransform_factor c m f hf),
    pointBlowupTransform_polarIdeal c m hm f _ (pointBlowupTransform_factor c m f hf)⟩

end OnLeConjecture.Analytic.Germ
