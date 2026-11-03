/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidual
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The cocycle obstruction for the `E` pair

This file formalizes the cocycle contradiction in Lemma
`dthree-Edouble`.  The specialization uses the four roots

`1, 0, omega, omega^2`

of `Z^4 - Z`, where `omega^2 + omega + 1 = 0`.  The norm of
`omega - 1` has square three.  It follows that

`1 - omega^(2k+1) + (omega-1)^(2k+1)`

is nonzero for every positive `k`.  Consequently, the differences of
three values cannot be nonzero scalar multiples of the indicated odd
powers.  The final theorem applies this obstruction to the factorization

`R(x) - R(X) = (x-X) Theta(x,X)`

when `Theta` is a nonzero scalar multiple of `(x-X)^(2k)` on the
specialized fibre.
-/

public section

namespace OnLeConjecture.DThree

/-- The roots used to specialize the quartic `Z^4 - Z` in the cocycle
argument. -/
@[expose]
noncomputable def eSpecializedFibreRoots (omega : ℂ) : Set ℂ :=
  {1, 0, omega, omega ^ 2}

/-- A zero of `Z^2 + Z + 1` has cube equal to one. -/
theorem e_cube_root_relation_pow_three (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    omega ^ 3 = 1 := by
  calc
    omega ^ 3 =
        1 + (omega - 1) * (omega ^ 2 + omega + 1) := by ring
    _ = 1 := by rw [homega, mul_zero, add_zero]

/-- Each value in the specialized fibre root set is a root of
`Z^4 - Z`. -/
theorem e_specialized_fibre_roots_satisfy_quartic
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    {z : ℂ} (hz : z ∈ eSpecializedFibreRoots omega) :
    z ^ 4 - z = 0 := by
  have hcube := e_cube_root_relation_pow_three omega homega
  simp only [eSpecializedFibreRoots, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hz
  rcases hz with hz | hz | hz | hz
  · rw [hz]
    norm_num
  · rw [hz]
    norm_num
  · rw [hz]
    calc
      omega ^ 4 - omega = omega * (omega ^ 3 - 1) := by ring
      _ = 0 := by
        rw [hcube]
        ring
  · rw [hz]
    calc
      (omega ^ 2) ^ 4 - omega ^ 2 =
          omega ^ 2 * ((omega ^ 3) ^ 2 - 1) := by ring
      _ = 0 := by
        rw [hcube]
        ring

/-- The four specialized quartic roots are pairwise distinct.  The
conclusion lists the six required inequalities. -/
theorem e_specialized_fibre_roots_distinct
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0) :
    (0 : ℂ) ≠ 1 ∧ (0 : ℂ) ≠ omega ∧
      (0 : ℂ) ≠ omega ^ 2 ∧ (1 : ℂ) ≠ omega ∧
      (1 : ℂ) ≠ omega ^ 2 ∧ omega ≠ omega ^ 2 := by
  have hneZero : omega ≠ 0 := by
    intro h
    rw [h] at homega
    norm_num at homega
  have hneOne : omega ≠ 1 := by
    intro h
    rw [h] at homega
    norm_num at homega
  have hsquareNeOne : omega ^ 2 ≠ 1 := by
    intro hsquare
    have hlinear : omega + 2 = 0 := by
      linear_combination homega - hsquare
    have heq : omega = -2 := by linear_combination hlinear
    rw [heq] at hsquare
    norm_num at hsquare
  have hneSquare : omega ≠ omega ^ 2 := by
    intro heq
    have hproduct : omega * (omega - 1) = 0 := by
      calc
        omega * (omega - 1) = omega ^ 2 - omega := by ring
        _ = 0 := sub_eq_zero.mpr heq.symm
    rcases mul_eq_zero.mp hproduct with hzero | hone
    · exact hneZero hzero
    · exact hneOne (sub_eq_zero.mp hone)
  exact ⟨by norm_num, Ne.symm hneZero,
    Ne.symm (pow_ne_zero 2 hneZero), Ne.symm hneOne,
    Ne.symm hsquareNeOne, hneSquare⟩

/-- The square of the norm of `omega - 1` is three. -/
theorem e_cube_root_difference_norm_sq
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0) :
    ‖omega - 1‖ ^ 2 = 3 := by
  have hcube := e_cube_root_relation_pow_three omega homega
  have hnormOmega : ‖omega‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hcube (by norm_num)
  have hsquare : (omega - 1) ^ 2 = -3 * omega := by
    calc
      (omega - 1) ^ 2 = omega ^ 2 - 2 * omega + 1 := by ring
      _ = -3 * omega := by linear_combination homega
  rw [← norm_pow, hsquare, norm_mul, hnormOmega]
  norm_num

/-- Every odd exponent `2k+1` with positive `k` gives a norm strictly
larger than two. -/
theorem e_cube_root_difference_norm_power_gt_two
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    2 < ‖omega - 1‖ ^ (2 * k + 1) := by
  have hnormSquare := e_cube_root_difference_norm_sq omega homega
  have hone : 1 < ‖omega - 1‖ := by
    have hnonneg := norm_nonneg (omega - 1)
    nlinarith [sq_nonneg (‖omega - 1‖ - 1)]
  have hthree : 3 ≤ 2 * k + 1 := by omega
  have hcubegt : 2 < ‖omega - 1‖ ^ 3 := by
    calc
      (2 : ℝ) < 3 * ‖omega - 1‖ := by nlinarith
      _ = ‖omega - 1‖ ^ 3 := by
        rw [pow_succ, hnormSquare]
  exact lt_of_lt_of_le hcubegt
    (pow_le_pow_right₀ hone.le hthree)

/-- The numerical expression obtained by summing the three differences
around the specialized triple is nonzero. -/
theorem e_cocycle_power_ne_zero
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    1 - omega ^ (2 * k + 1) +
        (omega - 1) ^ (2 * k + 1) ≠ 0 := by
  have hcube := e_cube_root_relation_pow_three omega homega
  have hnormOmega : ‖omega‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hcube (by norm_num)
  have hpowgt :=
    e_cube_root_difference_norm_power_gt_two omega homega k hk
  intro hzero
  have hidentity :
      (omega - 1) ^ (2 * k + 1) =
        omega ^ (2 * k + 1) - 1 := by
    linear_combination hzero
  have hnormle : ‖omega - 1‖ ^ (2 * k + 1) ≤ 2 := by
    calc
      ‖omega - 1‖ ^ (2 * k + 1) =
          ‖(omega - 1) ^ (2 * k + 1)‖ := by rw [norm_pow]
      _ = ‖omega ^ (2 * k + 1) - 1‖ := by rw [hidentity]
      _ ≤ ‖omega ^ (2 * k + 1)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [norm_pow, hnormOmega]
        norm_num
  linarith

/-- Three differences cannot be the prescribed nonzero scalar multiples
of the odd powers on the triple `1, 0, omega`. -/
theorem e_odd_power_differences_not_cocycle
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (k : ℕ) (hk : 1 ≤ k)
    (coefficient rOne rZero rOmega : ℂ)
    (hcoefficient : coefficient ≠ 0)
    (hOneZero :
      rOne - rZero =
        coefficient * ((1 : ℂ) - 0) ^ (2 * k + 1))
    (hZeroOmega :
      rZero - rOmega =
        coefficient * (0 - omega) ^ (2 * k + 1))
    (hOmegaOne :
      rOmega - rOne =
        coefficient * (omega - 1) ^ (2 * k + 1)) :
    False := by
  have hneg :
      (-omega) ^ (2 * k + 1) =
        -omega ^ (2 * k + 1) := by
    rw [neg_pow, pow_add, pow_mul]
    norm_num
  have hscaled :
      coefficient *
          (1 - omega ^ (2 * k + 1) +
            (omega - 1) ^ (2 * k + 1)) = 0 := by
    calc
      coefficient *
          (1 - omega ^ (2 * k + 1) +
            (omega - 1) ^ (2 * k + 1)) =
          coefficient * ((1 : ℂ) - 0) ^ (2 * k + 1) +
            coefficient * (0 - omega) ^ (2 * k + 1) +
            coefficient * (omega - 1) ^ (2 * k + 1) := by
              rw [sub_zero, one_pow, zero_sub, hneg]
              ring
      _ = (rOne - rZero) + (rZero - rOmega) +
          (rOmega - rOne) := by
        rw [hOneZero, hZeroOmega, hOmegaOne]
      _ = 0 := by ring
  have hzero :
      1 - omega ^ (2 * k + 1) +
          (omega - 1) ^ (2 * k + 1) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hcoefficient
  exact e_cocycle_power_ne_zero omega homega k hk hzero

/-- The diagonal power form for `Theta` is incompatible with the
difference factorization on the specialized fibre. -/
theorem e_diagonal_power_factorization_impossible
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (k : ℕ) (hk : 1 ≤ k)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (value : ℂ → ℂ) (theta : ℂ → ℂ → ℂ)
    (hfactor : ∀ x ∈ eSpecializedFibreRoots omega,
      ∀ X ∈ eSpecializedFibreRoots omega,
        value x - value X = (x - X) * theta x X)
    (hpower : ∀ x ∈ eSpecializedFibreRoots omega,
      ∀ X ∈ eSpecializedFibreRoots omega,
        theta x X = coefficient * (x - X) ^ (2 * k)) :
    False := by
  have hdifference (x X : ℂ)
      (hx : x ∈ eSpecializedFibreRoots omega)
      (hX : X ∈ eSpecializedFibreRoots omega) :
      value x - value X =
        coefficient * (x - X) ^ (2 * k + 1) := by
    rw [hfactor x hx X hX, hpower x hx X hX, pow_succ]
    ring
  apply e_odd_power_differences_not_cocycle omega homega k hk
    coefficient (value 1) (value 0) (value omega) hcoefficient
  · apply hdifference
    · simp [eSpecializedFibreRoots]
    · simp [eSpecializedFibreRoots]
  · apply hdifference
    · simp [eSpecializedFibreRoots]
    · simp [eSpecializedFibreRoots]
  · apply hdifference
    · simp [eSpecializedFibreRoots]
    · simp [eSpecializedFibreRoots]

/-- For a value expressed in the basis `1, x, x^2, x^3`, its factor
`eTheta` cannot be a nonzero scalar multiple of an even diagonal power on
the specialized fibre. -/
theorem e_basis_theta_diagonal_power_impossible
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (k : ℕ) (hk : 1 ≤ k)
    (coefficient : ℂ) (hcoefficient : coefficient ≠ 0)
    (c0 c1 c2 c3 : ℂ)
    (hpower : ∀ x ∈ eSpecializedFibreRoots omega,
      ∀ X ∈ eSpecializedFibreRoots omega,
        eTheta c1 c2 c3 x X =
          coefficient * (x - X) ^ (2 * k)) :
    False := by
  apply e_diagonal_power_factorization_impossible omega homega k hk
    coefficient hcoefficient (eBasisValue c0 c1 c2 c3)
      (eTheta c1 c2 c3)
  · intro x _ X _
    exact e_basis_difference_factorization c0 c1 c2 c3 x X
  · exact hpower

end OnLeConjecture.DThree
