/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.ResidualWeightedHomogeneity
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Construction of the prepared odd polynomial family

For odd `N ≥ 3`, the coefficients `alpha 0 = 1` and `alpha 1 = N / 2`
determine the leading term and the next coefficient of the explicit sum
`∑ h ≤ N / 2, alpha h * T ^ h * X ^ (N - 2 * h)`. Its remaining exponents
are odd. These facts construct `PreparedOddFamily` and its bivariate model
without assuming any of the defining polynomial identities.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- The univariate polynomial obtained from the prepared coefficient sum. -/
@[expose]
noncomputable def preparedOddPolynomial
    (N : ℕ) (alpha : ℕ → ℂ) (T : ℂ) : _root_.Polynomial ℂ :=
  ∑ h ∈ Finset.range (N / 2 + 1),
    C (alpha h * T ^ h) * X ^ (N - 2 * h)

/-- The exponents in the coefficient sum are distinct on its index range. -/
theorem preparedOddPolynomial_coeff
    (N : ℕ) (alpha : ℕ → ℂ) (T : ℂ)
    {h : ℕ} (hh : h ≤ N / 2) :
    (preparedOddPolynomial N alpha T).coeff (N - 2 * h) =
      alpha h * T ^ h := by
  classical
  rw [preparedOddPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single h]
  · simp
  · intro l hl hne
    have hlLe : l ≤ N / 2 := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
    have hexponent : N - 2 * h ≠ N - 2 * l := by omega
    exact if_neg hexponent
  · intro hnotmem
    exact (hnotmem (Finset.mem_range.mpr (by omega))).elim

/-- No term in the explicit polynomial has degree larger than `N`. -/
theorem preparedOddPolynomial_natDegree_le
    (N : ℕ) (alpha : ℕ → ℂ) (T : ℂ) :
    (preparedOddPolynomial N alpha T).natDegree ≤ N := by
  apply natDegree_sum_le_of_forall_le
  intro h _hh
  exact (natDegree_C_mul_X_pow_le (alpha h * T ^ h) (N - 2 * h)).trans
    (Nat.sub_le N (2 * h))

/-- The coefficient at degree `N` is one, so the sum is monic of degree
exactly `N`, including parameter value zero. -/
theorem preparedOddPolynomial_isMonicOfDegree
    (N : ℕ) (alpha : ℕ → ℂ) (hzero : alpha 0 = 1) (T : ℂ) :
    IsMonicOfDegree (preparedOddPolynomial N alpha T) N := by
  apply (isMonicOfDegree_iff _ _).mpr
  refine ⟨preparedOddPolynomial_natDegree_le N alpha T, ?_⟩
  simpa [hzero] using preparedOddPolynomial_coeff N alpha T (h := 0)
    (Nat.zero_le (N / 2))

/-- When `N` is odd, every exponent of the explicit coefficient sum is
odd, so substitution of `-X` negates the polynomial. -/
theorem preparedOddPolynomial_comp_neg
    (N : ℕ) (hodd : Odd N) (alpha : ℕ → ℂ) (T : ℂ) :
    (preparedOddPolynomial N alpha T).comp (-X) =
      -preparedOddPolynomial N alpha T := by
  classical
  rw [preparedOddPolynomial, sum_comp, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  have hhLe : h ≤ N / 2 := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh
  have hexponent : Odd (N - 2 * h) := by
    obtain ⟨m, hm⟩ := hodd
    refine ⟨m - h, ?_⟩
    omega
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [hexponent.neg_pow, mul_neg]

/-- The explicit coefficient sum constructs the prepared family. Only
its degree, parity, and first two scalar coefficients are inputs. -/
@[expose]
noncomputable def PreparedOddFamily.ofCoefficients
    {N : ℕ} (alpha : ℕ → ℂ) (hN : 3 ≤ N) (hodd : Odd N)
    (hzero : alpha 0 = 1) (hone : alpha 1 = (N : ℂ) / 2) :
    PreparedOddFamily N where
  polynomial := preparedOddPolynomial N alpha
  monic T := (preparedOddPolynomial_isMonicOfDegree N alpha hzero T).monic
  natDegree_eq T :=
    (preparedOddPolynomial_isMonicOfDegree N alpha hzero T).natDegree_eq
  coeff_sub_two T := by
    have hindex : 1 ≤ N / 2 := by omega
    simpa [hone] using preparedOddPolynomial_coeff N alpha T hindex
  odd T := preparedOddPolynomial_comp_neg N hodd alpha T

/-- The constructed family has the complete coefficient formula by its
definition, with no additional identity hypothesis. -/
theorem PreparedOddFamily.ofCoefficients_polynomial
    {N : ℕ} (alpha : ℕ → ℂ) (hN : 3 ≤ N) (hodd : Odd N)
    (hzero : alpha 0 = 1) (hone : alpha 1 = (N : ℂ) / 2) (T : ℂ) :
    (PreparedOddFamily.ofCoefficients alpha hN hodd hzero hone).polynomial T =
      ∑ h ∈ Finset.range (N / 2 + 1),
        C (alpha h * T ^ h) * X ^ (N - 2 * h) := by
  rfl

/-- The coefficient construction also supplies the bivariate weighted
homogeneous model used by residual collision lifting. -/
@[expose]
noncomputable def PreparedOddFamily.BivariateModel.ofExplicitCoefficients
    {N : ℕ} (alpha : ℕ → ℂ) (hN : 3 ≤ N) (hodd : Odd N)
    (hzero : alpha 0 = 1) (hone : alpha 1 = (N : ℂ) / 2) :
    (PreparedOddFamily.ofCoefficients alpha hN hodd hzero hone).BivariateModel where
  polynomial := preparedOddBivariatePolynomial N alpha
  specialization T := by
    rw [PreparedOddFamily.ofCoefficients_polynomial,
      parameterSpecialization_preparedOddBivariatePolynomial]
  weightedHomogeneous :=
    preparedOddBivariatePolynomial_isWeightedHomogeneous N alpha

end OnLeConjecture.DTwo
