/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CoefficientRecurrence
public import OnLeConjecture.DTwo.QuadraticBaseDecomposition
public import OnLeConjecture.PlaneCurve.QuadraticNormalization
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Analytic coefficients in the quadratic recurrence

This file connects divisibility of the analytic coefficient differential to
the finite recurrence used in the case of source order two.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

namespace Germ

/-- Differentiating the canonical first coordinate expansion. -/
theorem partialDerivative_zero_eq_tail_add_coordinate_mul_general
    (f : Germ 2) :
    Germ.partialDerivative (0 : Fin 2) f =
      Germ.firstCoordinateTail f +
        Germ.coordinate (0 : Fin 2) *
          Germ.partialDerivative (0 : Fin 2)
            (Germ.firstCoordinateTail f) := by
  have h := congrArg (Germ.partialDerivative (0 : Fin 2))
    (Germ.firstCoordinate_decomposition f)
  rw [Germ.partialDerivative_add, Germ.partialDerivative_mul,
    Germ.partialDerivative_coordinate_same,
    Germ.partialDerivative_zero_hyperplaneExtension] at h
  simpa [one_mul] using h

/-- The coefficients of a first coordinate derivative are obtained by the
usual shifted multiplication by the index. -/
theorem firstCoordinateTaylorCoefficient_partialDerivative_zero
    {k : ℕ} (f : Germ 2) :
    Germ.firstCoordinateTaylorCoefficient k
        (Germ.partialDerivative (0 : Fin 2) f) =
      ((k + 1 : ℕ) : ℂ) •
        Germ.firstCoordinateTaylorCoefficient (k + 1) f := by
  induction k generalizing f with
  | zero =>
      rw [Germ.partialDerivative_zero_eq_tail_add_coordinate_mul_general,
        Germ.firstCoordinateTaylorCoefficient_add,
        Germ.firstCoordinateTaylorCoefficient_zero,
        Germ.firstCoordinateTaylorCoefficient_zero,
        map_mul, Germ.hyperplaneRestriction_coordinate_zero,
        zero_mul, add_zero,
        Germ.firstCoordinateTaylorCoefficient_succ]
      simp
  | succ k ih =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.partialDerivative_zero_eq_tail_add_coordinate_mul_general,
        Germ.firstCoordinateTaylorCoefficient_add]
      have hmul : Germ.firstCoordinateTaylorCoefficient (k + 1)
          (Germ.coordinate (0 : Fin 2) *
            Germ.partialDerivative (0 : Fin 2)
              (Germ.firstCoordinateTail f)) =
          Germ.firstCoordinateTaylorCoefficient k
            (Germ.partialDerivative (0 : Fin 2)
              (Germ.firstCoordinateTail f)) := by
        rw [Germ.firstCoordinateTaylorCoefficient_succ,
          Germ.firstCoordinateTail_coordinate_mul]
      rw [hmul, ih, ← Germ.firstCoordinateTaylorCoefficient_succ]
      module

/-- The coefficient of a plane germ in a power of the second coordinate. -/
@[expose]
noncomputable def secondCoordinateTaylorCoefficient
    (j : ℕ) (f : Germ 2) : Germ 1 :=
  Germ.firstCoordinateTaylorCoefficient j
    (planeCoordinateSwapEquiv.pullbackAlgEquiv f)

/-- Expansion of a plane germ in the second coordinate. -/
@[expose]
noncomputable def secondCoordinateFormalRingHom :
    Germ 2 →+* PowerSeries (Germ 1) :=
  (Germ.firstCoordinateFormalRingHom 1).comp
    planeCoordinateSwapEquiv.pullbackAlgEquiv.toRingHom

@[simp]
theorem secondCoordinateFormalRingHom_coeff (j : ℕ) (f : Germ 2) :
    PowerSeries.coeff j (Germ.secondCoordinateFormalRingHom f) =
      Germ.secondCoordinateTaylorCoefficient j f := by
  simp [Germ.secondCoordinateFormalRingHom,
    Germ.secondCoordinateTaylorCoefficient,
    Germ.firstCoordinateFormalSeries]

/-- The coefficient variable is the first coordinate after expanding in the
second coordinate. -/
theorem secondCoordinateFormalRingHom_coordinate_zero :
    Germ.secondCoordinateFormalRingHom
        (Germ.coordinate (0 : Fin 2)) =
      PowerSeries.C (Germ.coordinate (0 : Fin 1)) := by
  rw [Germ.secondCoordinateFormalRingHom, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe]
  change Germ.firstCoordinateFormalRingHom 1
    (planeCoordinateSwapEquiv.pullbackAlgEquiv
      (Germ.coordinate (0 : Fin 2))) = _
  rw [Germ.planeCoordinateSwapEquiv_pullback_zero]
  have hcoordinate : Germ.coordinate (1 : Fin 2) =
      Germ.hyperplaneExtension 1 (Germ.coordinate (0 : Fin 1)) := by
    exact (Germ.hyperplaneExtension_coordinate (n := 1) (0 : Fin 1)).symm
  rw [hcoordinate, Germ.firstCoordinateFormalRingHom_hyperplaneExtension]

/-- The second coordinate is the formal variable in the second coordinate
expansion. -/
theorem secondCoordinateFormalRingHom_coordinate_one :
    Germ.secondCoordinateFormalRingHom
        (Germ.coordinate (1 : Fin 2)) = PowerSeries.X := by
  rw [Germ.secondCoordinateFormalRingHom, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe]
  change Germ.firstCoordinateFormalRingHom 1
    (planeCoordinateSwapEquiv.pullbackAlgEquiv
      (Germ.coordinate (1 : Fin 2))) = _
  rw [Germ.planeCoordinateSwapEquiv_pullback_one,
    Germ.firstCoordinateFormalRingHom_coordinate]

/-- Swapping the two coordinates changes differentiation in the second
coordinate into differentiation in the first coordinate. -/
theorem planeCoordinateSwap_partialDerivative_one (f : Germ 2) :
    planeCoordinateSwapEquiv.pullbackAlgEquiv
        (Germ.partialDerivative (1 : Fin 2) f) =
      Germ.partialDerivative (0 : Fin 2)
        (planeCoordinateSwapEquiv.pullbackAlgEquiv f) := by
  change Germ.compPointed (Germ.partialDerivative (1 : Fin 2) f)
      planeCoordinateSwapEquiv.forward =
    Germ.partialDerivative (0 : Fin 2)
      (Germ.compPointed f planeCoordinateSwapEquiv.forward)
  rw [Germ.partialDerivative_compPointed,
    show planeCoordinateSwapEquiv.forward.1.component (0 : Fin 2) =
        Germ.coordinate (1 : Fin 2) by
      exact (planeCoordinateSwapEquiv.forward.pullback_coordinate 0).trans
        Germ.planeCoordinateSwapEquiv_pullback_zero,
    show planeCoordinateSwapEquiv.forward.1.component (1 : Fin 2) =
        Germ.coordinate (0 : Fin 2) by
      exact (planeCoordinateSwapEquiv.forward.pullback_coordinate 1).trans
        Germ.planeCoordinateSwapEquiv_pullback_one]
  simp

/-- Expansion in the second coordinate commutes with differentiation in that
coordinate and formal differentiation. -/
theorem secondCoordinateFormalRingHom_partialDerivative_one (f : Germ 2) :
    Germ.secondCoordinateFormalRingHom
        (Germ.partialDerivative (1 : Fin 2) f) =
      PowerSeries.derivative (Germ 1)
        (Germ.secondCoordinateFormalRingHom f) := by
  apply PowerSeries.ext
  intro j
  rw [Germ.secondCoordinateFormalRingHom_coeff,
    Germ.secondCoordinateTaylorCoefficient,
    Germ.planeCoordinateSwap_partialDerivative_one,
    Germ.firstCoordinateTaylorCoefficient_partialDerivative_zero,
    PowerSeries.coeff_derivative,
    Germ.secondCoordinateFormalRingHom_coeff]
  simp [Germ.secondCoordinateTaylorCoefficient, Algebra.smul_def,
    mul_comm]

/-- The coefficient differential written in formal power series in the second
coordinate. -/
@[expose]
noncomputable def quadraticCoefficientPowerSeriesDifferential
    (g : Germ 1) (k : ℕ) (B : PowerSeries (Germ 1)) :
    PowerSeries (Germ 1) :=
  PowerSeries.C (2 * g) * PowerSeries.derivative (Germ 1) B -
    (PowerSeries.X ^ k * PowerSeries.derivative (Germ 1) B) *
      PowerSeries.C 2 -
    (PowerSeries.X ^ (k - 1) * B) * PowerSeries.C (k : Germ 1)

/-- The analytic coefficient differential expands to the corresponding
formal power series differential. -/
theorem secondCoordinateFormalRingHom_quadraticBaseCoefficientDifferential
    (k : ℕ) (B : Germ 2) :
    Germ.secondCoordinateFormalRingHom
        (Germ.quadraticBaseCoefficientDifferential k B) =
      Germ.quadraticCoefficientPowerSeriesDifferential
        (Germ.coordinate (0 : Fin 1)) k
        (Germ.secondCoordinateFormalRingHom B) := by
  simp only [Germ.quadraticBaseCoefficientDifferential,
    Germ.quadraticCoefficientPowerSeriesDifferential,
    map_sub, map_mul, map_nsmul, map_pow,
    Germ.secondCoordinateFormalRingHom_coordinate_zero,
    Germ.secondCoordinateFormalRingHom_coordinate_one,
    Germ.secondCoordinateFormalRingHom_partialDerivative_one, map_ofNat]
  have hnat : (k : PowerSeries (Germ 1)) =
      PowerSeries.C (k : Germ 1) := by
    exact (map_natCast PowerSeries.C k).symm
  simp only [nsmul_eq_mul]
  rw [hnat]
  ring

/-- The coefficient of `y^(j-1)` in the formal coefficient differential is
the difference of the two sides of the recurrence. -/
theorem coeff_quadraticCoefficientPowerSeriesDifferential
    (g : Germ 1) (k j : ℕ) (B : PowerSeries (Germ 1))
    (hk : 1 ≤ k) (hj : 1 ≤ j) :
    PowerSeries.coeff (j - 1)
        (Germ.quadraticCoefficientPowerSeriesDifferential g k B) =
      ((2 * j : ℕ) : Germ 1) * g * PowerSeries.coeff j B -
        if k ≤ j then
          ((2 * j - k : ℕ) : Germ 1) *
            PowerSeries.coeff (j - k) B
        else 0 := by
  by_cases hkj : k ≤ j
  · by_cases heq : j = k
    · subst j
      have hnot : ¬ k ≤ k - 1 := by omega
      have hidx : k - 1 - (k - 1) = 0 := by omega
      have hsucc : k - 1 + 1 = k := by omega
      simp only [Germ.quadraticCoefficientPowerSeriesDifferential,
        map_sub, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_derivative, hnot, if_false, hidx, hsucc,
        hkj, if_true, if_pos (le_refl (k - 1)), Nat.sub_self]
      have hcastSucc : ((k - 1 : ℕ) : Germ 1) + 1 = (k : Germ 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : Germ 1)) hsucc
      have hscalarNat : 2 * k - k = k := by omega
      rw [hcastSucc, hscalarNat]
      push_cast
      ring
    · have hlt : k < j := lt_of_le_of_ne hkj (Ne.symm heq)
      have hkpred : k ≤ j - 1 := by omega
      have hkone : k - 1 ≤ j - 1 := by omega
      have hidxOne : j - 1 - k + 1 = j - k := by omega
      have hidxTwo : j - 1 - (k - 1) = j - k := by omega
      simp only [Germ.quadraticCoefficientPowerSeriesDifferential,
        map_sub, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_derivative, hkj, if_true, hkpred, hkone,
        hidxOne, hidxTwo]
      have hindexZero : j - 1 + 1 = j := by omega
      have hcastSucc : ((j - 1 : ℕ) : Germ 1) + 1 =
          (j : Germ 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : Germ 1)) hindexZero
      have hcastShift : ((j - 1 - k : ℕ) : Germ 1) + 1 =
          ((j - k : ℕ) : Germ 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun n : ℕ => (n : Germ 1)) hidxOne
      have hscalarNat : 2 * j - k = 2 * (j - k) + k := by omega
      rw [hindexZero, hcastSucc, hcastShift, hscalarNat]
      push_cast
      ring
  · have hnotPred : ¬ k ≤ j - 1 := by omega
    have hnotOne : ¬ k - 1 ≤ j - 1 := by omega
    have hsucc : j - 1 + 1 = j := by omega
    simp only [Germ.quadraticCoefficientPowerSeriesDifferential,
      map_sub, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_derivative, hkj, if_false, hnotPred, hnotOne,
      hsucc]
    have hcastSucc : ((j - 1 : ℕ) : Germ 1) + 1 = (j : Germ 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun n : ℕ => (n : Germ 1)) hsucc
    rw [hcastSucc]
    push_cast
    ring

/-- Divisibility by a power of the second coordinate becomes divisibility by
the corresponding power of the formal variable. -/
theorem secondCoordinateFormalRingHom_X_pow_dvd
    {d : ℕ} {f : Germ 2}
    (hdiv : Germ.coordinate (1 : Fin 2) ^ d ∣ f) :
    PowerSeries.X ^ d ∣ Germ.secondCoordinateFormalRingHom f := by
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨Germ.secondCoordinateFormalRingHom q, ?_⟩
  calc
    Germ.secondCoordinateFormalRingHom f =
        Germ.secondCoordinateFormalRingHom
          (Germ.coordinate (1 : Fin 2) ^ d * q) := by rw [hq]
    _ = Germ.secondCoordinateFormalRingHom
          (Germ.coordinate (1 : Fin 2)) ^ d *
        Germ.secondCoordinateFormalRingHom q := by rw [map_mul, map_pow]
    _ = PowerSeries.X ^ d *
        Germ.secondCoordinateFormalRingHom q := by
      rw [Germ.secondCoordinateFormalRingHom_coordinate_one]

/-- Analytic divisibility of the coefficient differential gives the exact
finite recurrence on its analytic coefficient germs. -/
theorem satisfiesCoefficientRecurrenceOver_of_analytic_differential_dvd
    {k m : ℕ} {B : Germ 2} (hk : 1 ≤ k)
    (hdifferential : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.quadraticBaseCoefficientDifferential k B) :
    SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m := by
  have hformal : PowerSeries.X ^ (m - 1) ∣
      Germ.secondCoordinateFormalRingHom
        (Germ.quadraticBaseCoefficientDifferential k B) :=
    Germ.secondCoordinateFormalRingHom_X_pow_dvd hdifferential
  intro j hj hjm
  have hdegree : j - 1 < m - 1 := by omega
  have hzero := (PowerSeries.X_pow_dvd_iff.mp hformal) (j - 1) hdegree
  rw [Germ.secondCoordinateFormalRingHom_quadraticBaseCoefficientDifferential,
    Germ.coeff_quadraticCoefficientPowerSeriesDifferential
      (Germ.coordinate (0 : Fin 1)) k j
      (Germ.secondCoordinateFormalRingHom B) hk hj,
    Germ.secondCoordinateFormalRingHom_coeff,
    Germ.secondCoordinateFormalRingHom_coeff] at hzero
  exact sub_eq_zero.mp hzero

/-- A Jacobian divisibility gives the recurrence for the odd coefficient in
the unique analytic quadratic base decomposition. -/
theorem satisfiesCoefficientRecurrenceOver_of_jacobian_dvd
    {k m : ℕ} (hk : 1 ≤ k) (A B : Germ 2)
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k)
        (Germ.quadraticBaseSubstitutionAlgHom k hk A +
          Germ.coordinate (0 : Fin 2) *
            Germ.quadraticBaseSubstitutionAlgHom k hk B)) :
    SatisfiesCoefficientRecurrenceOver
      (Germ.coordinate (0 : Fin 1))
      (fun j ↦ Germ.secondCoordinateTaylorCoefficient j B) k m := by
  exact Germ.satisfiesCoefficientRecurrenceOver_of_analytic_differential_dvd
    hk (Germ.coefficient_divisibilities_of_jacobian k m hk A B hdiv).2

end Germ

end OnLeConjecture.DTwo
