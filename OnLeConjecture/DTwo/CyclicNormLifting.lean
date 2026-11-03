/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicResidueFactor

/-!
# Lifting a reduced norm root to a cyclic initial collision

The root is supplied by the affine polynomial count. Coprime-power
compatibility lifts it to the original first coordinate, with all
ramification factors and the original second exponent retained.
-/

public section

namespace OnLeConjecture.DTwo

open MvPolynomial

/-- A reduced norm relation supplies the original two required powers,
including the case where both scalar factors vanish. -/
theorem exists_cyclicNorm_scalar_lift
    (h q r : ℕ) (hh : 0 < h) (hq : Odd q) (hcoprime : Nat.Coprime q r)
    (G A T γ : ℂ) (hG : G ≠ 0) (hγ : γ ≠ 0)
    (hnorm : G ^ r * A ^ q + γ ^ q * T ^ q = 0) :
    ∃ x : ℂ, x ≠ 0 ∧ x ^ (h * q) = G ∧ x ^ (h * r) * A + γ * T = 0 := by
  by_cases hA : A = 0
  · have hT : T = 0 := by
      have hzero : γ ^ q * T ^ q = 0 := by simpa [hA, zero_pow hq.pos.ne'] using hnorm
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hγ))
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq G (Nat.mul_pos hh hq.pos)
    have hxzero : x ≠ 0 := by
      intro hz
      exact hG (by simpa [hz, zero_pow (Nat.mul_pos hh hq.pos).ne'] using hx.symm)
    exact ⟨x, hxzero, hx, by simp [hA, hT]⟩
  have hT : T ≠ 0 := by
    intro hz
    have hzero : G ^ r * A ^ q = 0 := by simpa [hz, zero_pow hq.pos.ne'] using hnorm
    exact mul_ne_zero (pow_ne_zero _ hG) (pow_ne_zero _ hA) hzero
  let b : ℂ := -γ * T / A
  have hb : b ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hγ) hT) hA
  have hrelation : G ^ r = b ^ q := by
    dsimp [b]
    rw [div_pow, mul_pow, hq.neg_pow]
    apply (eq_div_iff (pow_ne_zero q hA)).mpr
    linear_combination hnorm
  obtain ⟨x, hxzero, hxG, hxb⟩ :=
    exists_complex_compatible_powers h q r hh hcoprime G b hG hb hrelation
  refine ⟨x, hxzero, hxG, ?_⟩
  rw [hxb]
  dsimp [b]
  rw [div_mul_cancel₀ _ hA]
  ring

/-- Every mixed initial form with zero first monomial exponent has an
off-axis opposite-sign collision. No parity restriction on the descended
degree and no projective intersection hypothesis is needed. -/
theorem exists_cyclicMixedZero_initial_collision
    (k p j d : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (hdegree : p * j = k * d) (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (L R : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hR : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 1 ^ j)) :
    ∃ s Y : ℂ, s ≠ 0 ∧ Y ≠ 0 ∧ Y ^ k ≠ 1 ∧
      2 * s ^ p = c * (Y ^ k - 1) ∧ eval ![s, 1] R - eval ![-s, Y] R = 0 := by
  obtain ⟨h, q, r, hh, hq, hqodd, _, hcoprime, hpFactor, hrFactor,
    hrnot, hN, hNnot, hNdiv, hgcd⟩ := exists_cyclic_reduced_exponents k p j d hk hp hj hdegree
  obtain ⟨M, hM⟩ := exists_weighted_residue_factor p d L hL
  let A := cyclicResidueDifferencePolynomial (d % p) c M
  obtain ⟨Y, hroot, hYzero, hYoff⟩ := cyclicReducedNorm_has_off_axis_root
    k (k + j) q r hk hN hq hNnot hNdiv hgcd hrnot c (γ ^ q) hc (pow_ne_zero _ hγ) A
  let G : ℂ := c / 2 * (Y ^ k - 1)
  have hG : G ≠ 0 := mul_ne_zero (div_ne_zero hc (by norm_num)) (sub_ne_zero.mpr hYoff)
  have hnorm : G ^ r * A.eval (Y ^ k) ^ q + γ ^ q * (1 - Y ^ (k + j)) ^ q = 0 := by
    simpa [cyclicReducedNorm, _root_.Polynomial.IsRoot.def, cyclicMixedPlanePolynomial_eval,
      _root_.Polynomial.expand_eq_comp_X_pow, _root_.Polynomial.eval_comp, G] using hroot
  obtain ⟨s, hs, hsG, hsum⟩ := exists_cyclicNorm_scalar_lift h q r hh hqodd hcoprime
    G (A.eval (Y ^ k)) (1 - Y ^ (k + j)) γ hG hγ hnorm
  rw [← hpFactor] at hsG
  rw [← hrFactor] at hsum
  refine ⟨s, Y, hs, hYzero, hYoff, ?_, ?_⟩
  · rw [hsG]
    dsimp [G]
    ring
  · have hdifference := cyclicResidueDifferencePolynomial_eval k p (d % p) hp c s Y L M hM hsG
    change eval ![s, 1] L - Y ^ k * eval ![-s, Y ^ k] L =
      s ^ (d % p) * A.eval (Y ^ k) at hdifference
    rw [hR]
    simp only [map_mul, map_add, eval_pow, eval_X, eval_C, Matrix.cons_val_zero,
      Matrix.cons_val_one, cyclicInvariantLift_eval, one_pow, one_mul, mul_one]
    rw [pow_add] at hsum
    linear_combination hdifference + hsum

end OnLeConjecture.DTwo
