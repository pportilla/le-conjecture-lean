/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.ExtremeResidualCollision

/-!
# Fourier decomposition of the extreme residual polynomial

Constant rotation differences force every term involving the first
coordinate to be invariant. The only possible noninvariant term is a
pure power of the second coordinate, with its unreduced exponent.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic

/-- A polynomial with no complex root is constant. -/
theorem polynomial_eq_constant_of_no_roots (P : Polynomial ℂ)
    (hroots : ∀ z : ℂ, P.eval z ≠ 0) : P = Polynomial.C (P.coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  by_contra hdegree
  have hdeg : P.degree ≠ 0 := by
    intro hzero
    exact hdegree (Polynomial.natDegree_eq_of_degree_eq_some hzero)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hdeg
  exact hroots z hz

/-- A single primitive rotation with constant difference suffices. -/
theorem extreme_residual_fourier_of_primitive_constant
    (a k D : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k)
    (R : MvPolynomial (Fin 2) ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hconstant : ∃ c : ℂ, cyclicRotationDifference R ζ = Polynomial.C c) :
    ∃ U : MvPolynomial (Fin 2) ℂ, ∃ c : ℂ,
      U ∈ cyclicInvariantAlgebra k ∧ U.IsWeightedHomogeneous ![a, 1] D ∧
      R = U + MvPolynomial.C c * MvPolynomial.X 1 ^ D := by
  classical
  let d₀ : Fin 2 →₀ ℕ := Finsupp.single 1 D
  let c : ℂ := MvPolynomial.coeff d₀ R
  let U := R - MvPolynomial.monomial d₀ c
  have hmon : (MvPolynomial.monomial d₀ c).IsWeightedHomogeneous ![a, 1] D := by
    apply MvPolynomial.isWeightedHomogeneous_monomial
    simp [d₀, Finsupp.weight_apply]
  have hU : U ∈ cyclicInvariantAlgebra k := by
    apply mem_cyclicInvariantAlgebra_of_support_dvd
    intro d hd
    have hdU := MvPolynomial.mem_support_iff.mp hd
    have hdd₀ : d ≠ d₀ := by
      intro hh
      subst d
      simp [U, c] at hdU
    have hdR : MvPolynomial.coeff d R ≠ 0 := by
      simpa only [U, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
        if_neg hdd₀.symm, sub_zero] using hdU
    have hfirst : d 0 ≠ 0 := by
      intro hzero
      have hweight : a * d 0 + d 1 = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hR hdR
      have hsecond : d 1 = D := by simpa only [hzero, mul_zero, zero_add] using hweight
      apply hdd₀
      ext i
      fin_cases i
      · simpa [d₀] using hzero
      · simpa [d₀] using hsecond
    obtain ⟨b, hb⟩ := hconstant
    have hcoef := cyclicRotationDifference_coeff a 1 D one_pos R hR d hdR ζ
    rw [hb, Polynomial.coeff_C, if_neg hfirst] at hcoef
    have hpow : ζ ^ d 1 = 1 := by
      have hz : 1 - ζ ^ d 1 = 0 :=
        (mul_eq_zero.mp hcoef.symm).resolve_left hdR
      exact (sub_eq_zero.mp hz).symm
    exact (hζ.pow_eq_one_iff_dvd _).mp hpow
  refine ⟨U, c, hU, hR.sub hmon, ?_⟩
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  exact (sub_add_cancel R (MvPolynomial.monomial d₀ c)).symm

/-- Injectivity forces the stated invariant-plus-pure-power form. -/
theorem extremeResidual_fourier_of_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (a D : ℕ) (ha : 0 < a) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (htail : ∀ i, g.1.component i -
      Germ.coordinatePolynomialAlgHom 2 (extremeResidualPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a (![2 * a, 3 * a, D] i + 1)) :
    ∃ U : MvPolynomial (Fin 2) ℂ, ∃ c : ℂ,
      U ∈ cyclicInvariantAlgebra (2 * a) ∧ U.IsWeightedHomogeneous ![a, 1] D ∧
      R = U + MvPolynomial.C c * MvPolynomial.X 1 ^ D := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2 * a : ℕ) : ℂ))
  have hζ : IsPrimitiveRoot ζ (2 * a) :=
    Complex.isPrimitiveRoot_exp (2 * a) (by omega)
  apply extreme_residual_fourier_of_primitive_constant a (2 * a) D ζ hζ R hR
  by_cases hzero : cyclicRotationDifference R ζ = 0
  · exact ⟨0, by simp [hzero]⟩
  · exact ⟨_, polynomial_eq_constant_of_no_roots _
      (extremeResidual_no_roots_of_injective g hg a D ha R hR htail ζ hζ.pow_eq_one hzero)⟩

end OnLeConjecture.DTwo
