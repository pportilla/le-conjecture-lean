/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RegularBlowupCharts
public import OnLeConjecture.Analytic.GeneralSourceBlowupLift
public import OnLeConjecture.Analytic.SwappedNodeBlowup
public import OnLeConjecture.Analytic.InverseGeneralSourceBlowupLift

/-!
# Supported tangents in transverse coordinates

A positive-order strict transform of a transversely regular germ cannot
map to the complementary tangent under a source equivalence. Consequently
the finite-tangent condition needed for the analytic lift is a theorem for
each recorded point on the strict transform, not an extra chart assumption.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem coordinateSwapPointedEquiv_forward_comp_self :
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward.comp
      (coordinateSwapPointedEquiv (1 : Fin 2)).forward = PointedMapGerm.identity 2 := by
  apply PointedMapGerm.ext_components
  intro i
  simp only [← PointedMapGerm.pullback_coordinate, PointedMapGerm.pullbackRingHom_comp,
    RingHom.comp_apply, PointedMapGerm.pullbackRingHom_identity]
  fin_cases i
  · change (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (coordinate 0)) =
        coordinate (0 : Fin 2)
    rw [PointedMapGerm.pullback_coordinate, coordinateSwapPointedEquiv_component_zero]
    exact coordinateSwapPointedEquiv_pullback_second
  · change (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (coordinate 1)) =
        coordinate (1 : Fin 2)
    rw [coordinateSwapPointedEquiv_pullback_second, PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1

theorem coordinateSwapPointedEquiv_pullback_twice (f : Germ 2) :
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) = f := by
  have hcomp := congrArg (fun B : PointedMapGerm 2 2 ↦ B.pullbackRingHom f)
    coordinateSwapPointedEquiv_forward_comp_self
  rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    PointedMapGerm.pullbackRingHom_identity] at hcomp
  exact hcomp

/-- An invertible derivative cannot annihilate a nonzero tangent vector. -/
theorem finiteChartCenter_ne_zero_of_denominator_zero
    (e : PointedEquivGerm 2) (ζ : ℂ) (hden : finiteTangentDenominator e ζ = 0) :
    finiteChartCenter e ζ ≠ 0 := by
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
  intro hnum
  apply hdet
  change c * ζ + d = 0 at hden
  change a * ζ + b = 0 at hnum
  linear_combination a * hden - c * hnum

/-- Every supported tangent of a regular germ remains in a finite chart
after an arbitrary pointed source equivalence. -/
theorem finiteTangentDenominator_ne_zero_of_positive_transform
    (e : PointedEquivGerm 2) (ζ : ℂ) (m : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hregular : IsRegularInFirstCoordinateOfOrder f m)
    (htransform : (pointBlowupChartGerm ζ).pullbackRingHom
      (e.forward.pullbackRingHom f) = coordinate (1 : Fin 2) ^ m * g)
    (hg : g ∈ maximalIdeal 2) : finiteTangentDenominator e ζ ≠ 0 := by
  intro hden
  let s := coordinateSwapPointedEquiv (1 : Fin 2)
  have hnum := finiteChartCenter_ne_zero_of_denominator_zero e ζ hden
  have hsx : s.forward.pullbackRingHom (coordinate (0 : Fin 2)) = coordinate 1 := by
    rw [PointedMapGerm.pullback_coordinate]
    exact coordinateSwapPointedEquiv_component_zero 1
  have hsy : s.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 0 :=
    coordinateSwapPointedEquiv_pullback_second
  have hswappedX : (s.comp e).forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      e.forward.pullbackRingHom (coordinate 1) := by
    change (s.forward.comp e.forward).pullbackRingHom (coordinate 0) = _
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, hsx]
  have hswappedY : (s.comp e).forward.pullbackRingHom (coordinate (1 : Fin 2)) =
      e.forward.pullbackRingHom (coordinate 0) := by
    change (s.forward.comp e.forward).pullbackRingHom (coordinate 1) = _
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, hsy]
  have hfinite : finiteTangentDenominator (s.comp e) ζ ≠ 0 := by
    simpa only [finiteTangentDenominator, hswappedY, finiteChartCenter] using hnum
  have hcenter : generalFiniteChartCenter (s.comp e) ζ = 0 := by
    rw [generalFiniteChartCenter]
    have hzero : finiteChartCenter (s.comp e) ζ = 0 := by
      simpa only [finiteChartCenter, hswappedX, finiteTangentDenominator] using hden
    rw [hzero, zero_div]
  obtain ⟨Q, U, E, hU, _hQ, _hUfactor, _hc, _hratio, hEy, hcomm, _hJac⟩ :=
    exists_pointBlowup_lift_of_finite_tangent (s.comp e) ζ hfinite
  rw [hcenter] at hcomm
  obtain ⟨F, hF⟩ := exists_pointBlowupChart_factor 0 m (s.forward.pullbackRingHom f)
    (s.forward.pullback_mem_maximalIdeal_pow hf)
  have hFunit := complementaryBlowupTransform_isUnit_of_regular m f F hregular hF
  have hpull := congrArg (fun B : PointedMapGerm 2 2 ↦
    B.pullbackRingHom (s.forward.pullbackRingHom f)) hcomm
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at hpull
  have htwice : (s.comp e).forward.pullbackRingHom (s.forward.pullbackRingHom f) =
      e.forward.pullbackRingHom f := by
    change (s.forward.comp e.forward).pullbackRingHom (s.forward.pullbackRingHom f) = _
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    rw [coordinateSwapPointedEquiv_pullback_twice]
  rw [htwice, htransform, hF, map_mul, map_pow, hEy, mul_pow, mul_assoc] at hpull
  have hgeq : g = U ^ m * E.forward.pullbackRingHom F :=
    mul_left_cancel₀ (pow_ne_zero m (coordinate_ne_zero (1 : Fin 2))) hpull
  have hgunit : IsUnit g := by
    rw [hgeq]
    exact (hU.pow m).mul (hFunit.map _)
  exact valueRingHom_ne_zero_of_isUnit hgunit (mem_maximalIdeal_iff.mp hg)

/-- A prescribed old supported chart has an analytically constructed
finite chart in the new transverse coordinates. The finite condition and
all commuting identities are conclusions. -/
theorem exists_finite_chart_lift_of_regular_pullback
    (e : PointedEquivGerm 2) (c : ℂ) (m : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder (e.forward.pullbackRingHom f) m)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g) (hg : g ∈ maximalIdeal 2) :
    ∃ (ζ : ℂ) (E : PointedEquivGerm 2) (U : Germ 2), IsUnit U ∧
      E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U ∧
      e.forward.comp (pointBlowupChartGerm ζ) =
        (pointBlowupChartGerm c).comp E.forward ∧
      (pointBlowupChartGerm ζ).pullbackRingHom (e.forward.pullbackRingHom f) =
        coordinate (1 : Fin 2) ^ m * (U ^ m * E.forward.pullbackRingHom g) := by
  have hback : e.symm.forward.pullbackRingHom (e.forward.pullbackRingHom f) = f :=
    e.pullbackRingEquiv.symm_apply_apply f
  have hfinite := finiteTangentDenominator_ne_zero_of_positive_transform e.symm c m
    (e.forward.pullbackRingHom f) g (e.forward.pullback_mem_maximalIdeal_pow hf)
    hregular (by rw [hback]; exact htransform) hg
  obtain ⟨E, U, hU, hEy, hcomm⟩ := exists_inverse_finite_chart_lift e c hfinite
  refine ⟨generalFiniteChartCenter e.symm c, E, U, hU, hEy, hcomm, ?_⟩
  have h := congrArg (fun B : PointedMapGerm 2 2 ↦ B.pullbackRingHom f) hcomm
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at h
  rw [h, htransform, map_mul, map_pow, hEy, mul_pow, mul_assoc]

/-- The constructed lift carries a full-order child to another transverse
regular germ. Thus the local construction can be iterated on a top-order path. -/
theorem regular_child_of_finite_chart_lift
    (e E : PointedEquivGerm 2) (c ζ : ℂ) (m : ℕ) (f g U : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hg : g ∈ maximalIdeal 2 ^ m) (hU : IsUnit U)
    (hEy : E.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U)
    (hcomm : e.forward.comp (pointBlowupChartGerm ζ) =
      (pointBlowupChartGerm c).comp E.forward)
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g) :
    IsRegularInFirstCoordinateOfOrder (E.forward.pullbackRingHom g) m := by
  have hnew : (pointBlowupChartGerm ζ).pullbackRingHom (e.forward.pullbackRingHom f) =
      coordinate (1 : Fin 2) ^ m * (U ^ m * E.forward.pullbackRingHom g) := by
    have h := congrArg (fun B : PointedMapGerm 2 2 ↦ B.pullbackRingHom f) hcomm
    simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at h
    rw [h, htransform, map_mul, map_pow, hEy, mul_pow, mul_assoc]
  have hfull := pointBlowupTransform_regular_of_full_order ζ m
    (e.forward.pullbackRingHom f) (U ^ m * E.forward.pullbackRingHom g)
    (e.forward.pullback_mem_maximalIdeal_pow hf)
    ((e.pullback_mem_maximalIdeal_pow_iff f).not.mpr hnext)
    ((maximalIdeal 2 ^ m).mul_mem_left _ (E.forward.pullback_mem_maximalIdeal_pow hg)) hnew
  exact (isRegularInFirstCoordinateOfOrder_unit_mul_iff _ _ (hU.pow m)).mp hfull

end OnLeConjecture.Analytic.Germ
