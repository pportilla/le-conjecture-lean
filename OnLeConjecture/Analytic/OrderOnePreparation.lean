/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.ParametricMorse
public import OnLeConjecture.Analytic.WeierstrassPreparation

/-!
# Analytic preparation in orders zero and one

This file proves analytic Weierstrass preparation for a plane germ whose
order in the first coordinate is at most one. In order one, the inverse of
the coordinate replacement expresses the zero set as a graph over the
parameter coordinate. Analytic division then supplies the unit factor.
-/

public section

namespace OnLeConjecture.Analytic

open Filter

namespace Germ

/-- A plane germ of order one in the first coordinate has nonzero first
directional derivative. -/
theorem differential_firstCoordinateVector_ne_zero_of_regular_order_one
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f 1) :
    Germ.differential f (firstCoordinateVector 1) ≠ 0 := by
  have htailValue :
      Germ.valueRingHom 2 (Germ.firstCoordinateTail f) ≠ 0 := by
    have h := (Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).1
    rw [Germ.value_firstCoordinateTaylorCoefficient] at h
    simpa [Germ.firstCoordinateTailIterate_succ] using h
  have hext :
      Germ.differential
          (Germ.hyperplaneExtension 1
            (Germ.firstCoordinateCoefficient f))
          (firstCoordinateVector 1) = 0 := by
    have h := congrArg (Germ.valueRingHom 2)
      (Germ.partialDerivative_zero_hyperplaneExtension
        (Germ.firstCoordinateCoefficient f))
    rw [Germ.valueRingHom_partialDerivative] at h
    simpa [Germ.partialDerivative, firstCoordinateVector,
      coordinateVector] using h
  have hdec := congrArg Germ.differential
    (Germ.firstCoordinate_decomposition f)
  have happ := congrArg
    (fun L : Source 2 →L[ℂ] ℂ ↦ L (firstCoordinateVector 1)) hdec
  rw [Germ.differential_add, Germ.differential_mul] at happ
  simp only [add_apply, smul_apply] at happ
  simp only [Germ.valueRingHom_coordinate,
    Germ.differential_coordinate_apply, hext,
    firstCoordinateVector_apply_zero, zero_smul, zero_add,
    add_zero] at happ
  rw [happ]
  simpa [smul_eq_mul] using htailValue

/-- Analytic Weierstrass preparation holds for every plane germ of order
zero in the first coordinate. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_zero
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f 0) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f 0 := by
  change ∃ p : Polynomial (Germ 1), ∃ u : Germ 2,
    p.Monic ∧ p.natDegree = 0 ∧
      (∀ k, k < 0 → p.coeff k ∈ Germ.maximalIdeal 1) ∧
      IsUnit u ∧
      f = Germ.firstCoordinatePolynomialEvaluation p * u
  have hfUnit : IsUnit f := by
    simpa using Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
  refine ⟨1, f, Polynomial.monic_one, ?_, ?_, hfUnit, ?_⟩
  · simp
  · intro k hk
    omega
  · simp [Germ.firstCoordinatePolynomialEvaluation]

/-- Analytic Weierstrass preparation holds for every plane germ of order
one in the first coordinate. -/
theorem hasAnalyticWeierstrassFactorizationOfOrder_one
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f 1) :
    Germ.HasAnalyticWeierstrassFactorizationOfOrder f 1 := by
  change ∃ p : Polynomial (Germ 1), ∃ u : Germ 2,
    p.Monic ∧ p.natDegree = 1 ∧
      (∀ k, k < 1 → p.coeff k ∈ Germ.maximalIdeal 1) ∧
      IsUnit u ∧
      f = Germ.firstCoordinatePolynomialEvaluation p * u
  have hfmax : f ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    have hzero :=
      (Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular).2 0
        (by omega)
    rw [Germ.value_firstCoordinateTaylorCoefficient] at hzero
    simpa using hzero
  have hfderivative :
      Germ.differential f (firstCoordinateVector 1) ≠ 0 :=
    Germ.differential_firstCoordinateVector_ne_zero_of_regular_order_one
      hregular
  obtain ⟨e, he, hext⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_preserving_hyperplaneExtension
      f hfmax hfderivative
  let h : Germ 2 :=
    e.pullbackAlgEquiv.symm (Germ.coordinate (0 : Fin 2))
  let a : Germ 1 := Germ.firstCoordinateCoefficient h
  let q : Germ 2 := Germ.firstCoordinateTail h
  let v : Germ 2 := e.pullbackAlgEquiv q
  have hcoordinate :
      Germ.coordinate (0 : Fin 2) =
        f * v + Germ.hyperplaneExtension 1 a := by
    have hdecomposition := Germ.firstCoordinate_decomposition h
    calc
      Germ.coordinate (0 : Fin 2) = e.pullbackAlgEquiv h := by
        exact (e.pullbackAlgEquiv.apply_symm_apply
          (Germ.coordinate (0 : Fin 2))).symm
      _ = e.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin 2) * q +
            Germ.hyperplaneExtension 1 a) := by
        rw [hdecomposition]
      _ = f * v + Germ.hyperplaneExtension 1 a := by
        rw [map_add, map_mul, he, hext]
  have hextDerivative :
      Germ.differential (Germ.hyperplaneExtension 1 a)
          (firstCoordinateVector 1) = 0 := by
    have hzero := congrArg (Germ.valueRingHom 2)
      (Germ.partialDerivative_zero_hyperplaneExtension a)
    rw [Germ.valueRingHom_partialDerivative] at hzero
    simpa [Germ.partialDerivative, firstCoordinateVector,
      coordinateVector] using hzero
  have hvValue : Germ.valueRingHom 2 v ≠ 0 := by
    intro hvzero
    have hdifferential := congrArg Germ.differential hcoordinate
    have happly := congrArg
      (fun L : Source 2 →L[ℂ] ℂ ↦ L (firstCoordinateVector 1))
      hdifferential
    rw [Germ.differential_add, Germ.differential_mul] at happly
    simp only [add_apply, smul_apply] at happly
    simp only [Germ.differential_coordinate_apply,
      firstCoordinateVector_apply_zero, Germ.mem_maximalIdeal_iff.mp hfmax,
      hvzero, zero_smul, hextDerivative, add_zero] at happly
    exact one_ne_zero happly
  have hvUnit : IsUnit v := Germ.isUnit_of_valueRingHom_ne_zero hvValue
  let u : Germ 2 := (↑hvUnit.unit⁻¹ : Germ 2)
  have huUnit : IsUnit u := by
    exact Units.isUnit hvUnit.unit⁻¹
  have hfactor :
      f = (Germ.coordinate (0 : Fin 2) - Germ.hyperplaneExtension 1 a) * u := by
    have hdifference :
        Germ.coordinate (0 : Fin 2) - Germ.hyperplaneExtension 1 a =
          f * v := sub_eq_iff_eq_add.mpr hcoordinate
    have hvInv : v * u = 1 := by
      calc
        v * u = (↑hvUnit.unit : Germ 2) *
            (↑hvUnit.unit⁻¹ : Germ 2) := by
          rw [hvUnit.unit_spec]
        _ = 1 := Units.mul_inv hvUnit.unit
    calc
      f = f * (v * u) := by
        rw [hvInv, mul_one]
      _ = (f * v) * u := by rw [mul_assoc]
      _ = (Germ.coordinate (0 : Fin 2) -
            Germ.hyperplaneExtension 1 a) * u := by rw [hdifference]
  have haMax : a ∈ Germ.maximalIdeal 1 := by
    rw [Germ.mem_maximalIdeal_iff]
    have hhValue : Germ.valueRingHom 2 h = 0 := by
      change Germ.valueRingHom 2
        (e.inverse.pullbackRingHom (Germ.coordinate (0 : Fin 2))) = 0
      rw [PointedMapGerm.valueRingHom_pullback,
        Germ.valueRingHom_coordinate]
    calc
      Germ.valueRingHom 1 a = Germ.valueRingHom 2 h := by
        simpa [a, Germ.firstCoordinateCoefficient] using
          Germ.value_firstCoordinateTaylorCoefficient (k := 0) h
      _ = 0 := hhValue
  let p : Polynomial (Germ 1) := Polynomial.X - Polynomial.C a
  refine ⟨p, u, ?_, ?_, ?_, huUnit, ?_⟩
  · exact Polynomial.monic_X_sub_C a
  · exact Polynomial.natDegree_X_sub_C a
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa [p] using (neg_mem haMax)
  · have hpEvaluation :
        Germ.firstCoordinatePolynomialEvaluation p =
          Germ.coordinate (0 : Fin 2) - Germ.hyperplaneExtension 1 a := by
      simp [p, Germ.firstCoordinatePolynomialEvaluation]
    rw [hpEvaluation]
    exact hfactor

/-- The completed image closure condition holds in order zero. -/
theorem completedWeierstrassImageClosureAtOrder_zero :
    Germ.CompletedWeierstrassImageClosureAtOrder 0 :=
  (Germ.completedWeierstrassImageClosureAtOrder_iff 0).2
    fun _f hregular ↦
      Germ.hasAnalyticWeierstrassFactorizationOfOrder_zero hregular

/-- The completed image closure condition holds in order one. -/
theorem completedWeierstrassImageClosureAtOrder_one :
    Germ.CompletedWeierstrassImageClosureAtOrder 1 :=
  (Germ.completedWeierstrassImageClosureAtOrder_iff 1).2
    fun _f hregular ↦
      Germ.hasAnalyticWeierstrassFactorizationOfOrder_one hregular

end Germ

end OnLeConjecture.Analytic
