/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.DepressedCubicCoefficientOrder
public import OnLeConjecture.Analytic.TwoWeightMonomialIdeal
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Local multiplicity bounds for the quartic square transforms

The integral-weight chart has exceptional restriction `(X²+η)²`. At any
root, translation gives a nonzero quadratic coefficient in the first
coordinate. The half-integral-weight chart has the nonzero quadratic
coefficient `η²` in the second coordinate. We express multiplicity at most
two as nonmembership in the cube of the actual analytic maximal ideal.

These are local analytic chart calculations. The repository's point-basis
certificates are numerical objects. No construction of successive blowup
centers, or identification of their multiplicities with those certificates,
is assumed or supplied in this module.
-/

public section

namespace OnLeConjecture.DFour

open OnLeConjecture.Analytic

/-- Exact cancellation of the exceptional factor after the substitution
`x = y^A X` in the integral-weight coefficient expansion. -/
theorem integral_quartic_chart_identity
    {R : Type*} [CommRing R] (A : ℕ) (X y η a₂ a₁ a₀ : R) :
    (y ^ A * X) ^ 4 +
      y ^ (2 * A) * (2 * η + y * a₂) * (y ^ A * X) ^ 2 +
      y ^ (3 * A + 1) * a₁ * (y ^ A * X) +
      y ^ (4 * A) * (η ^ 2 + y * a₀) =
    y ^ (4 * A) * ((X ^ 2 + η) ^ 2 + y * (a₂ * X ^ 2 + a₁ * X + a₀)) := by
  simp only [Nat.mul_comm 2 A, Nat.mul_comm 3 A, Nat.mul_comm 4 A,
    pow_add, pow_mul, pow_one]
  ring

/-- Exact cancellation of the exceptional factor after the substitution
`x = y^A X` in the half-integral-weight coefficient expansion. -/
theorem half_integral_quartic_chart_identity
    {R : Type*} [CommRing R] (A : ℕ) (X y η a₂ a₁ a₀ : R) :
    (y ^ A * X) ^ 4 +
      y ^ (2 * A + 1) * (2 * η + y * a₂) * (y ^ A * X) ^ 2 +
      y ^ (3 * A + 2) * a₁ * (y ^ A * X) +
      y ^ (4 * A + 2) * (η ^ 2 + y * a₀) =
    y ^ (4 * A) * ((X ^ 2 + η * y) ^ 2 +
      y ^ 2 * (a₂ * X ^ 2 + a₁ * X + y * a₀)) := by
  simp only [Nat.mul_comm 2 A, Nat.mul_comm 3 A, Nat.mul_comm 4 A,
    pow_add, pow_mul, pow_one]
  ring

/-- For nonzero `η`, the exceptional polynomial has exactly two distinct
roots, both nonzero. -/
theorem integral_quartic_exceptional_roots (η : ℂ) (hη : η ≠ 0) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧ ζ ≠ -ζ ∧
      ∀ z : ℂ, (z ^ 2 + η) ^ 2 = 0 ↔ z = ζ ∨ z = -ζ := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (-η) (by decide : 0 < 2)
  have hζzero : ζ ≠ 0 := by
    intro hzero
    exact hη (neg_eq_zero.mp (by simpa only [hzero, zero_pow (by decide : 2 ≠ 0)] using hζ.symm))
  refine ⟨ζ, hζzero, ?_, ?_⟩
  · intro hneg
    apply hζzero
    have htwo : (2 : ℂ) * ζ = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  · intro z
    rw [pow_eq_zero_iff (by decide : 2 ≠ 0), add_eq_zero_iff_eq_neg, ← hζ]
    exact sq_eq_sq_iff_eq_or_eq_neg

/-- A nonzero second partial derivative at the origin excludes membership
in the cube of the analytic maximal ideal. -/
theorem not_mem_maximalIdeal_cube_of_second_partial_ne_zero
    (F : Germ 2) (i : Fin 2)
    (hsecond : Germ.valueRingHom 2
      (Germ.partialDerivative i (Germ.partialDerivative i F)) ≠ 0) :
    F ∉ Germ.maximalIdeal 2 ^ 3 := by
  intro hF
  have hfirst := Germ.partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ i hF
  have hsecondMem := Germ.partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ i hfirst
  apply hsecond
  exact Germ.mem_maximalIdeal_iff.mp (by simpa only [pow_one] using hsecondMem)

/-- The integral-weight quartic transform, recentered at the exceptional
point with first coordinate `ζ`. The analytic coefficients may be arbitrary
plane germs, which includes the parameter-dependent coefficients in the
manuscript. -/
@[expose] noncomputable def integralQuarticTransform
    (η ζ : ℂ) (a₂ a₁ a₀ : Germ 2) : Germ 2 :=
  ((Germ.coordinate (0 : Fin 2) + Germ.constRingHom 2 ζ) ^ 2 +
    Germ.constRingHom 2 η) ^ 2 +
  Germ.coordinate (1 : Fin 2) *
    (a₂ * (Germ.coordinate (0 : Fin 2) + Germ.constRingHom 2 ζ) ^ 2 +
      a₁ * (Germ.coordinate (0 : Fin 2) + Germ.constRingHom 2 ζ) + a₀)

/-- The half-integral-weight quartic transform at the unique exceptional
point. -/
@[expose] noncomputable def halfIntegralQuarticTransform
    (η : ℂ) (a₂ a₁ a₀ : Germ 2) : Germ 2 :=
  (Germ.coordinate (0 : Fin 2) ^ 2 +
    Germ.constRingHom 2 η * Germ.coordinate (1 : Fin 2)) ^ 2 +
  Germ.coordinate (1 : Fin 2) ^ 2 *
    (a₂ * Germ.coordinate (0 : Fin 2) ^ 2 +
      a₁ * Germ.coordinate (0 : Fin 2) + Germ.coordinate (1 : Fin 2) * a₀)

/-- The second first-coordinate derivative of the integral chart at a
root of the exceptional polynomial is `8ζ²`. -/
theorem integralQuarticTransform_second_partial
    (η ζ : ℂ) (a₂ a₁ a₀ : Germ 2) (hroot : ζ ^ 2 + η = 0) :
    Germ.valueRingHom 2 (Germ.partialDerivative (0 : Fin 2)
      (Germ.partialDerivative (0 : Fin 2) (integralQuarticTransform η ζ a₂ a₁ a₀))) =
        8 * ζ ^ 2 := by
  simp only [integralQuarticTransform, pow_two, Germ.partialDerivative_add,
    Germ.partialDerivative_mul, Germ.partialDerivative_const,
    Germ.partialDerivative_coordinate_same,
    Germ.partialDerivative_coordinate_ne (show (0 : Fin 2) ≠ 1 by decide),
    map_add, map_mul, map_one, Germ.valueRingHom_coordinate,
    Germ.valueRingHom_const, zero_add, add_zero, zero_mul, one_mul, mul_one]
  linear_combination 4 * hroot

/-- The nonzero `y²` coefficient in the half-integral chart gives the
second partial derivative `2η²`, independently of the error coefficients. -/
theorem halfIntegralQuarticTransform_second_partial
    (η : ℂ) (a₂ a₁ a₀ : Germ 2) :
    Germ.valueRingHom 2 (Germ.partialDerivative (1 : Fin 2)
      (Germ.partialDerivative (1 : Fin 2) (halfIntegralQuarticTransform η a₂ a₁ a₀))) =
        2 * η ^ 2 := by
  simp only [halfIntegralQuarticTransform, pow_two, Germ.partialDerivative_add,
    Germ.partialDerivative_mul, Germ.partialDerivative_const,
    Germ.partialDerivative_coordinate_same,
    Germ.partialDerivative_coordinate_ne (show (1 : Fin 2) ≠ 0 by decide),
    map_add, map_mul, map_one, Germ.valueRingHom_coordinate,
    Germ.valueRingHom_const, zero_add, add_zero, mul_zero, zero_mul, one_mul, mul_one]
  ring

/-- At every exceptional root in the integral case, the analytic transform
vanishes and has multiplicity at most two. -/
theorem integralQuarticTransform_at_root
    (η ζ : ℂ) (hη : η ≠ 0) (hroot : ζ ^ 2 + η = 0)
    (a₂ a₁ a₀ : Germ 2) :
    integralQuarticTransform η ζ a₂ a₁ a₀ ∈ Germ.maximalIdeal 2 ∧
      integralQuarticTransform η ζ a₂ a₁ a₀ ∉ Germ.maximalIdeal 2 ^ 3 := by
  have hζ : ζ ≠ 0 := by
    intro hz
    exact hη (by simpa only [hz, zero_pow (by decide : 2 ≠ 0), zero_add] using hroot)
  constructor
  · rw [Germ.mem_maximalIdeal_iff]
    simp [integralQuarticTransform, hroot]
  · apply not_mem_maximalIdeal_cube_of_second_partial_ne_zero _ 0
    rw [integralQuarticTransform_second_partial η ζ a₂ a₁ a₀ hroot]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hζ)

/-- The half-integral analytic transform has multiplicity at most two. -/
theorem halfIntegralQuarticTransform_not_mem_cube
    (η : ℂ) (hη : η ≠ 0) (a₂ a₁ a₀ : Germ 2) :
    halfIntegralQuarticTransform η a₂ a₁ a₀ ∉ Germ.maximalIdeal 2 ^ 3 := by
  apply not_mem_maximalIdeal_cube_of_second_partial_ne_zero _ 1
  rw [halfIntegralQuarticTransform_second_partial]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hη)

/-- Every term of the half-integral transform has ordinary order at least
two, so together with the preceding exclusion its multiplicity is exactly
two. -/
theorem halfIntegralQuarticTransform_mem_square
    (η : ℂ) (a₂ a₁ a₀ : Germ 2) :
    halfIntegralQuarticTransform η a₂ a₁ a₀ ∈ Germ.maximalIdeal 2 ^ 2 := by
  let I := Germ.maximalIdeal 2
  have hx : Germ.coordinate (0 : Fin 2) ∈ I := Germ.coordinate_mem_maximalIdeal _
  have hy : Germ.coordinate (1 : Fin 2) ∈ I := Germ.coordinate_mem_maximalIdeal _
  have hinner : Germ.coordinate (0 : Fin 2) ^ 2 +
      Germ.constRingHom 2 η * Germ.coordinate (1 : Fin 2) ∈ I := by
    exact I.add_mem (Ideal.pow_mem_of_mem I hx 2 (by decide))
      (Ideal.mul_mem_left I _ hy)
  exact (I ^ 2).add_mem (Ideal.pow_mem_pow hinner 2)
    (Ideal.mul_mem_right _ (I ^ 2) (Ideal.pow_mem_pow hy 2))

/-- In weights `(1,2)`, every correction to the displayed half-integral
quartic square has weight at least five. -/
theorem halfIntegralQuarticTransform_weighted_error
    (η : ℂ) (a₂ a₁ a₀ : Germ 2) :
    halfIntegralQuarticTransform η a₂ a₁ a₀ -
      (Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.constRingHom 2 η * Germ.coordinate (1 : Fin 2)) ^ 2 ∈
      Germ.twoWeightOrderIdeal 1 2 5 := by
  let I := Germ.twoWeightOrderIdeal 1 2 5
  have hx₂y₂ : Germ.coordinate (0 : Fin 2) ^ 2 *
      Germ.coordinate (1 : Fin 2) ^ 2 ∈ I :=
    Germ.monomial_mem_twoWeightOrderIdeal_of_threshold 1 2 5 2 2
      (by decide) (by decide) (by decide)
  have hxy₂ : Germ.coordinate (0 : Fin 2) *
      Germ.coordinate (1 : Fin 2) ^ 2 ∈ I := by
    simpa only [pow_one] using
      Germ.monomial_mem_twoWeightOrderIdeal_of_threshold 1 2 5 1 2
        (by decide) (by decide) (by decide)
  have hy₃ : Germ.coordinate (1 : Fin 2) ^ 3 ∈ I := by
    simpa only [pow_zero, one_mul] using
      Germ.monomial_mem_twoWeightOrderIdeal_of_threshold 1 2 5 0 3
        (by decide) (by decide) (by decide)
  have hsum := I.add_mem
    (I.add_mem (Ideal.mul_mem_left I a₂ hx₂y₂) (Ideal.mul_mem_left I a₁ hxy₂))
    (Ideal.mul_mem_left I a₀ hy₃)
  convert hsum using 1
  dsimp [halfIntegralQuarticTransform]
  ring

end OnLeConjecture.DFour
