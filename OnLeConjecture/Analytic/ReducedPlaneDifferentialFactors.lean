/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableDerivativeOrder
public import OnLeConjecture.Analytic.FiniteParametricMorse
public import OnLeConjecture.Analytic.PlaneUniqueFactorization
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Differential factors of a reduced analytic germ

A nonzero germ vanishing at the origin cannot divide every partial
derivative: restriction to a line on which it is nonzero contradicts the
one-variable derivative order formula. Consequently a squarefree plane
germ has no prime divisor common to itself and its two partials.

This statement concerns the zero fibre. It does not assert that the
Jacobian algebra is finite without proving the additional critical-value
argument.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem not_dvd_derivative_of_oneVariable_mem_maximalIdeal
    (f : Germ 1) (hf : f ∈ maximalIdeal 1) (hne : f ≠ 0) :
    ¬ f ∣ partialDerivative (0 : Fin 1) f := by
  intro hdvd
  obtain ⟨hderivative, horder⟩ := derivative_ne_zero_and_order_add_one f hf hne
  have hle := ENat.toNat_le_toNat (vanishingOrder_le_iff_dvd.mpr hdvd)
    (fun htop => hderivative (vanishingOrder_eq_top_iff.mp htop))
  omega

/-- Nonzero pointed analytic germs do not divide all their partials. -/
theorem exists_partialDerivative_not_dvd {n : ℕ} (f : Germ n)
    (hf : f ∈ maximalIdeal n) (hne : f ≠ 0) :
    ∃ i : Fin n, ¬ f ∣ partialDerivative i f := by
  by_contra h
  have hall : ∀ i : Fin n, f ∣ partialDerivative i f := by simpa using h
  obtain ⟨v, hv⟩ := exists_lineRestriction_ne_zero hne
  have hpointed : lineRestriction v f ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff]
    change valueRingHom 1 ((lineGerm v).pullbackRingHom f) = 0
    rw [PointedMapGerm.valueRingHom_pullback]
    exact mem_maximalIdeal_iff.mp hf
  apply not_dvd_derivative_of_oneVariable_mem_maximalIdeal _ hpointed hv
  change lineRestriction v f ∣ partialDerivative (0 : Fin 1) (compPointed f (lineGerm v))
  rw [partialDerivative_compPointed_sum]
  apply Finset.dvd_sum
  intro i hi
  exact dvd_mul_of_dvd_left ((lineRestriction v).map_dvd (hall i)) _

theorem exists_partialDerivative_not_dvd_of_irreducible
    (p : Germ 2) (hp : Irreducible p) :
    ∃ i : Fin 2, ¬ p ∣ partialDerivative i p := by
  apply exists_partialDerivative_not_dvd p _ hp.ne_zero
  rw [mem_maximalIdeal_iff]
  by_contra h
  exact hp.not_isUnit (isUnit_of_valueRingHom_ne_zero h)

theorem not_dvd_partialDerivative_zero_of_regular
    (f : Germ 2) (hf : f ∈ maximalIdeal 2) (m : ℕ)
    (hregular : IsRegularInFirstCoordinateOfOrder f m) :
    ¬ f ∣ partialDerivative (0 : Fin 2) f := by
  let v := firstCoordinateVector 1
  have hline : lineRestriction v f ≠ 0 := by
    intro hz
    have hord : vanishingOrder (lineRestriction v f) = m := hregular
    rw [hz, vanishingOrder_eq_top_iff.mpr rfl] at hord
    exact (ENat.natCast_ne_top m) hord.symm
  have hpointed : lineRestriction v f ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff]
    exact (PointedMapGerm.valueRingHom_pullback (lineGerm v) f).trans
      (mem_maximalIdeal_iff.mp hf)
  have hcoord0 : (lineGerm v).1.component 0 = coordinate (0 : Fin 1) := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [] with z
    simp [lineMap, v, firstCoordinateVector]
  have hcoord1 : (lineGerm v).1.component 1 = 0 := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [] with z
    simp [lineMap, v, firstCoordinateVector]
  have hderivative : partialDerivative (0 : Fin 1) (lineRestriction v f) =
      lineRestriction v (partialDerivative (0 : Fin 2) f) := by
    change partialDerivative (0 : Fin 1) (compPointed f (lineGerm v)) = _
    rw [partialDerivative_compPointed_sum, Fin.sum_univ_two, hcoord0, hcoord1,
      partialDerivative_coordinate_same, partialDerivative_zero, mul_one, mul_zero, add_zero]
    rfl
  intro hdiv
  apply not_dvd_derivative_of_oneVariable_mem_maximalIdeal _ hpointed hline
  rw [hderivative]
  exact (lineRestriction v).map_dvd hdiv

/-- A prime divisor of a squarefree germ fails to divide at least one
partial derivative of that germ. -/
theorem exists_partialDerivative_not_dvd_of_squarefree
    (f : Germ 2) (hf : Squarefree f) (p : Germ 2)
    (hp : Prime p) (hpf : p ∣ f) :
    ∃ i : Fin 2, ¬ p ∣ partialDerivative i f := by
  obtain ⟨a, rfl⟩ := hpf
  have hpa : ¬ p ∣ a := by
    intro hpa
    have hsquare : p * p ∣ p * a := mul_dvd_mul_left p hpa
    exact hp.not_isUnit (hf p hsquare)
  obtain ⟨i, hi⟩ := exists_partialDerivative_not_dvd_of_irreducible p hp.irreducible
  refine ⟨i, ?_⟩
  intro hdiv
  rw [partialDerivative_mul] at hdiv
  have hprod : p ∣ partialDerivative i p * a := by
    have hsub := dvd_sub hdiv (dvd_mul_right p (partialDerivative i a))
    simpa only [add_sub_cancel_right] using hsub
  exact (hp.dvd_or_dvd hprod).elim hi hpa

theorem not_prime_dvd_self_and_partials_of_squarefree
    (f : Germ 2) (hf : Squarefree f) (p : Germ 2) (hp : Prime p) :
    ¬ (p ∣ f ∧ p ∣ partialDerivative 0 f ∧ p ∣ partialDerivative 1 f) := by
  rintro ⟨hpf, hp0, hp1⟩
  obtain ⟨i, hi⟩ := exists_partialDerivative_not_dvd_of_squarefree f hf p hp hpf
  fin_cases i
  · exact hi hp0
  · exact hi hp1

end OnLeConjecture.Analytic.Germ
