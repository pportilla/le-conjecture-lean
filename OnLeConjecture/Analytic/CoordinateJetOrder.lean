/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeierstrassPreparation
public import OnLeConjecture.PlaneCurve.ParametricMorse

/-!
# Coordinate jets and analytic order

This file compares repeated partial differentiation in the first coordinate
with repeated analytic division by that coordinate. The value of the
derivative of order `n` is `n!` times the value of the corresponding
coordinate quotient. It follows that regularity in the first coordinate is
equivalent to the expected condition on repeated derivatives.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Differentiating the first coordinate division formula expresses the
first partial derivative in terms of the quotient. -/
theorem partialDerivative_zero_eq_tail_add_coordinate_mul
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

/-- The value of the first partial derivative is the value of the first
coordinate quotient. -/
theorem value_partialDerivative_zero_eq_value_tail (f : Germ 2) :
    Germ.valueRingHom 2 (Germ.partialDerivative (0 : Fin 2) f) =
      Germ.valueRingHom 2 (Germ.firstCoordinateTail f) := by
  rw [Germ.partialDerivative_zero_eq_tail_add_coordinate_mul]
  simp

/-- Repeated differentiation in the first coordinate. -/
@[expose] noncomputable def firstPartialDerivativeIterate :
    ℕ → Germ 2 → Germ 2
  | 0, f => f
  | n + 1, f => Germ.partialDerivative (0 : Fin 2)
      (Germ.firstPartialDerivativeIterate n f)

@[simp]
theorem firstPartialDerivativeIterate_zero (f : Germ 2) :
    Germ.firstPartialDerivativeIterate 0 f = f := rfl

@[simp]
theorem firstPartialDerivativeIterate_succ (n : ℕ) (f : Germ 2) :
    Germ.firstPartialDerivativeIterate (n + 1) f =
      Germ.partialDerivative (0 : Fin 2)
        (Germ.firstPartialDerivativeIterate n f) := rfl

/-- Repeated differentiation of the first coordinate division formula. -/
theorem firstPartialDerivativeIterate_succ_eq
    (n : ℕ) (f : Germ 2) :
    Germ.firstPartialDerivativeIterate (n + 1) f =
      ((n + 1 : ℕ) : ℂ) •
          Germ.firstPartialDerivativeIterate n
            (Germ.firstCoordinateTail f) +
        Germ.coordinate (0 : Fin 2) *
          Germ.firstPartialDerivativeIterate (n + 1)
            (Germ.firstCoordinateTail f) := by
  induction n with
  | zero =>
      simpa using Germ.partialDerivative_zero_eq_tail_add_coordinate_mul f
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        Germ.firstPartialDerivativeIterate_succ]
      rw [ih]
      rw [Germ.partialDerivative_add, Germ.partialDerivative_smul,
        Germ.partialDerivative_mul, Germ.partialDerivative_coordinate_same]
      simp only [Germ.firstPartialDerivativeIterate_succ, one_mul]
      module

/-- The value of the derivative of order `n` is `n!` times the value of the
quotient obtained by dividing `n` times by the first coordinate. -/
theorem value_firstPartialDerivativeIterate_eq_factorial_mul_value_tailIterate
    (n : ℕ) (f : Germ 2) :
    Germ.valueRingHom 2 (Germ.firstPartialDerivativeIterate n f) =
      (n.factorial : ℂ) *
        Germ.valueRingHom 2 (Germ.firstCoordinateTailIterate n f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = n + 1 from rfl,
        Germ.firstPartialDerivativeIterate_succ_eq]
      rw [map_add, Algebra.smul_def, map_mul, map_mul,
        Germ.valueRingHom_coordinate,
        zero_mul, add_zero, ih]
      rw [Germ.firstCoordinateTailIterate_tail]
      have hscalar : Germ.valueRingHom 2
          ((algebraMap ℂ (Germ 2)) ((n + 1 : ℕ) : ℂ)) =
          ((n + 1 : ℕ) : ℂ) := by
        change Germ.valueRingHom 2
          (Germ.constRingHom 2 ((n + 1 : ℕ) : ℂ)) = _
        rw [Germ.valueRingHom_const]
      rw [hscalar]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      ring

/-- Regularity in the first coordinate is equivalent to the vanishing of all
preceding derivatives and the nonvanishing of the derivative of the stated
order. -/
theorem isRegularInFirstCoordinateOfOrder_iff_derivativeIterates
    {d : ℕ} {f : Germ 2} :
    Germ.IsRegularInFirstCoordinateOfOrder f d ↔
      Germ.valueRingHom 2
          (Germ.firstPartialDerivativeIterate d f) ≠ 0 ∧
        ∀ k, k < d →
          Germ.valueRingHom 2
            (Germ.firstPartialDerivativeIterate k f) = 0 := by
  rw [Germ.isRegularInFirstCoordinateOfOrder_iff]
  constructor
  · rintro ⟨hd, hlt⟩
    constructor
    · rw [Germ.value_firstPartialDerivativeIterate_eq_factorial_mul_value_tailIterate]
      rw [← Germ.value_firstCoordinateTaylorCoefficient]
      exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d) hd
    · intro k hk
      rw [Germ.value_firstPartialDerivativeIterate_eq_factorial_mul_value_tailIterate]
      rw [← Germ.value_firstCoordinateTaylorCoefficient]
      rw [hlt k hk, mul_zero]
  · rintro ⟨hd, hlt⟩
    constructor
    · intro hzero
      apply hd
      rw [Germ.value_firstPartialDerivativeIterate_eq_factorial_mul_value_tailIterate]
      rw [← Germ.value_firstCoordinateTaylorCoefficient, hzero, mul_zero]
    · intro k hk
      have hz := hlt k hk
      rw [Germ.value_firstPartialDerivativeIterate_eq_factorial_mul_value_tailIterate]
        at hz
      rw [← Germ.value_firstCoordinateTaylorCoefficient] at hz
      exact (mul_eq_zero.mp hz).resolve_left
        (by exact_mod_cast Nat.factorial_ne_zero k)

/-- The second partial derivative at the origin is twice the value of the
second coordinate quotient. -/
theorem value_secondPartialDerivative_zero_eq_two_mul_value_tailIterate
    (f : Germ 2) :
    Germ.valueRingHom 2
        (Germ.partialDerivative (0 : Fin 2)
          (Germ.partialDerivative (0 : Fin 2) f)) =
      2 * Germ.valueRingHom 2 (Germ.firstCoordinateTailIterate 2 f) := by
  simpa using
    Germ.value_firstPartialDerivativeIterate_eq_factorial_mul_value_tailIterate
      2 f

end Germ

end OnLeConjecture.Analytic
