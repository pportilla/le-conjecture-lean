/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Algebra of the quadratic orbit collision

This file verifies the residual fibre equations and the conic
parametrization used in the order two projective collision argument. It also
proves the cyclic obstruction to a pure diagonal power difference.
-/

public section

namespace OnLeConjecture.DTwo

/-- The quadratic form in the orbit collision argument. -/
@[expose]
def orbitPhi (s lambda : ℂ) : ℂ :=
  s ^ 2 - lambda ^ 2

/-- The cubic form in the orbit collision argument. -/
@[expose]
def orbitPsi (s lambda : ℂ) : ℂ :=
  2 * s ^ 3 - 3 * s * lambda ^ 2

/-- The cubic form is expressed through the quadratic form and the first
source coordinate. -/
theorem orbitPsi_eq (s lambda : ℂ) :
    orbitPsi s lambda = 3 * orbitPhi s lambda * s - s ^ 3 := by
  rw [orbitPhi, orbitPsi]
  ring

/-- Away from `s=t`, equality of the two forms is equivalent to the two
residual fibre equations. -/
theorem orbit_same_values_iff_residual
    {s lambda t zeta : ℂ} (hst : s ≠ t) :
    orbitPhi s lambda = orbitPhi t zeta ∧
        orbitPsi s lambda = orbitPsi t zeta ↔
      t ^ 2 + s * t - 2 * s ^ 2 + 3 * lambda ^ 2 = 0 ∧
        zeta ^ 2 = t ^ 2 - s ^ 2 + lambda ^ 2 := by
  constructor
  · rintro ⟨hphi, hpsi⟩
    have hzeta : zeta ^ 2 = t ^ 2 - s ^ 2 + lambda ^ 2 := by
      simp only [orbitPhi] at hphi
      linear_combination hphi
    have hproduct :
        (s - t) *
          (t ^ 2 + s * t - 2 * s ^ 2 + 3 * lambda ^ 2) = 0 := by
      calc
        (s - t) *
              (t ^ 2 + s * t - 2 * s ^ 2 + 3 * lambda ^ 2) =
            -(orbitPsi s lambda - orbitPsi t zeta) +
              3 * t * (orbitPhi s lambda - orbitPhi t zeta) := by
                simp only [orbitPhi, orbitPsi]
                ring
        _ = 0 := by
          rw [hphi, hpsi]
          ring
    exact ⟨(mul_eq_zero.mp hproduct).resolve_left
      (sub_ne_zero.mpr hst), hzeta⟩
  · rintro ⟨hresidual, hzeta⟩
    have hphi : orbitPhi s lambda = orbitPhi t zeta := by
      rw [orbitPhi, orbitPhi, hzeta]
      ring
    have hsum :
        (orbitPsi s lambda - orbitPsi t zeta) +
          (s - t) *
            (t ^ 2 + s * t - 2 * s ^ 2 + 3 * lambda ^ 2) =
          3 * t * (orbitPhi s lambda - orbitPhi t zeta) := by
      simp only [orbitPhi, orbitPsi]
      ring
    have hpsi : orbitPsi s lambda = orbitPsi t zeta := by
      rw [hresidual, mul_zero, add_zero, hphi, sub_self, mul_zero] at hsum
      exact sub_eq_zero.mp hsum
    exact ⟨hphi, hpsi⟩

/-- The coordinates in the conic parametrization satisfy the first residual
equation. -/
theorem orbit_conic_first_residual
    {rho alpha beta : ℂ}
    (hconic : rho ^ 2 = 3 * (alpha ^ 2 + beta ^ 2)) :
    let s := -(alpha ^ 2 + 2 * beta ^ 2)
    let lambda := rho * beta
    let t := 2 * alpha ^ 2 + beta ^ 2
    t ^ 2 + s * t - 2 * s ^ 2 + 3 * lambda ^ 2 = 0 := by
  dsimp only
  linear_combination 3 * beta ^ 2 * hconic

/-- The coordinates in the conic parametrization satisfy the second
residual equation. -/
theorem orbit_conic_second_residual
    {rho alpha beta : ℂ}
    (hconic : rho ^ 2 = 3 * (alpha ^ 2 + beta ^ 2)) :
    let s := -(alpha ^ 2 + 2 * beta ^ 2)
    let lambda := rho * beta
    let t := 2 * alpha ^ 2 + beta ^ 2
    let zeta := rho * alpha
    zeta ^ 2 = t ^ 2 - s ^ 2 + lambda ^ 2 := by
  dsimp only
  linear_combination (alpha ^ 2 - beta ^ 2) * hconic

/-- In the conic parametrization, the difference `t - s` equals `rho²`. -/
theorem orbit_conic_t_sub_s
    {rho alpha beta : ℂ}
    (hconic : rho ^ 2 = 3 * (alpha ^ 2 + beta ^ 2)) :
    (2 * alpha ^ 2 + beta ^ 2) -
        (-(alpha ^ 2 + 2 * beta ^ 2)) = rho ^ 2 := by
  linear_combination -hconic

/-- A conic point with nonzero `rho` produces two distinct first source
coordinates with the same values of the quadratic and cubic forms. -/
theorem orbit_conic_same_values
    {rho alpha beta : ℂ}
    (hconic : rho ^ 2 = 3 * (alpha ^ 2 + beta ^ 2))
    (hrho : rho ≠ 0) :
    let s := -(alpha ^ 2 + 2 * beta ^ 2)
    let lambda := rho * beta
    let t := 2 * alpha ^ 2 + beta ^ 2
    let zeta := rho * alpha
    s ≠ t ∧ orbitPhi s lambda = orbitPhi t zeta ∧
      orbitPsi s lambda = orbitPsi t zeta := by
  dsimp only
  have hst : -(alpha ^ 2 + 2 * beta ^ 2) ≠
      2 * alpha ^ 2 + beta ^ 2 := by
    intro heq
    have hzero : rho ^ 2 = 0 := by
      rw [← orbit_conic_t_sub_s hconic, ← heq, sub_self]
    exact hrho (sq_eq_zero_iff.mp hzero)
  refine ⟨hst, ?_⟩
  exact (orbit_same_values_iff_residual hst).mpr
    ⟨orbit_conic_first_residual hconic,
      orbit_conic_second_residual hconic⟩

/-- Three differences cannot be nonzero scalar multiples of the same odd
power of the directed coordinate differences on `-1,0,1`. -/
theorem orbit_odd_power_differences_not_cocycle
    (r : ℕ) (hr : 2 ≤ r) (hodd : Odd r)
    (coefficient valueNeg valueZero valueOne : ℂ)
    (hcoefficient : coefficient ≠ 0)
    (hNegZero : valueNeg - valueZero =
      coefficient * ((0 : ℂ) - (-1)) ^ r)
    (hZeroOne : valueZero - valueOne =
      coefficient * ((1 : ℂ) - 0) ^ r)
    (hOneNeg : valueOne - valueNeg =
      coefficient * ((-1 : ℂ) - 1) ^ r) :
    False := by
  have hnegTwo : ((-2 : ℂ) ^ r) = -(2 : ℂ) ^ r := by
    simpa using hodd.neg_pow (2 : ℂ)
  have hscaled : coefficient * (2 - (2 : ℂ) ^ r) = 0 := by
    calc
      coefficient * (2 - (2 : ℂ) ^ r) =
          coefficient * ((0 : ℂ) - (-1)) ^ r +
            coefficient * ((1 : ℂ) - 0) ^ r +
              coefficient * ((-1 : ℂ) - 1) ^ r := by
                rw [show (0 : ℂ) - (-1) = 1 by norm_num,
                  show (1 : ℂ) - 0 = 1 by norm_num,
                  show (-1 : ℂ) - 1 = -2 by norm_num,
                  one_pow, hnegTwo]
                ring
      _ = (valueNeg - valueZero) + (valueZero - valueOne) +
          (valueOne - valueNeg) := by
        rw [hNegZero, hZeroOne, hOneNeg]
      _ = 0 := by ring
  have hpowerComplex : (2 : ℂ) ^ r = 2 := by
    have hzero := (mul_eq_zero.mp hscaled).resolve_left hcoefficient
    exact (sub_eq_zero.mp hzero).symm
  have hpowerNat : 2 ^ r = 2 := by
    exact_mod_cast hpowerComplex
  have hfour : 2 ^ 2 ≤ 2 ^ r :=
    Nat.pow_le_pow_right (by norm_num) hr
  rw [hpowerNat] at hfour
  norm_num at hfour

/-- A uniform pure diagonal power identity on the three specialized roots
is impossible in odd degree at least two. -/
theorem orbit_diagonal_power_identity_impossible
    (r : ℕ) (hr : 2 ≤ r) (hodd : Odd r)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (value : ℂ → ℂ)
    (hidentity : ∀ s t, s ∈ ({-1, 0, 1} : Set ℂ) →
      t ∈ ({-1, 0, 1} : Set ℂ) →
        value s - value t = coefficient * (t - s) ^ r) :
    False := by
  apply orbit_odd_power_differences_not_cocycle r hr hodd coefficient
    (value (-1)) (value 0) (value 1) hcoefficient
  · apply hidentity
    · simp
    · simp
  · apply hidentity
    · simp
    · simp
  · apply hidentity
    · simp
    · simp

end OnLeConjecture.DTwo
