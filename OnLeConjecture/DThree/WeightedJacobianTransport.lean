/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedInitialFormFactor
public import OnLeConjecture.DThree.WeightedPowerJacobianDescent

/-!
# Transport of weighted Jacobian divisibility

Analytic divisibility by a power of the second coordinate passes to the
Jacobian of two weighted polynomial initial forms. Source and target
rescaling preserves the resulting polynomial divisibility. When both forms
come from a weighted power substitution, the divisibility descends to the
ordinary forms.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Analytic divisibility of a Jacobian passes to the Jacobian of two
weighted homogeneous polynomial initial forms. The assumptions `a ≤ m` and
`a ≤ n` are the inequalities needed to control differentiation in the first
coordinate. -/
theorem formT_pow_dvd_polynomial_jacobian_of_analytic_divisibility
    (a m n N : ℕ) (ha : 0 < a) (ham : a ≤ m) (han : a ≤ n)
    (P Q : Form ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] m)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] n)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (m + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (n + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ N ∣ Germ.jacobian f g) :
    formT ^ N ∣ OnLeConjecture.Polynomial.jacobian P Q := by
  let R := OnLeConjecture.Polynomial.jacobian P Q
  let D := m + n - a - 1
  have hmone : 1 ≤ m := by omega
  have hnone : 1 ≤ n := by omega
  have hR : R.IsWeightedHomogeneous ![a, 1] D := by
    have hraw :=
      OnLeConjecture.Polynomial.isWeightedHomogeneous_jacobian
        ![a, 1] P Q m n hP hQ ham hmone han hnone
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, R, D,
      show m - a + (n - 1) = m + n - a - 1 by omega] using hraw
  have htail :
      Germ.jacobian f g - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.weightedOrderIdeal a (D + 1) := by
    have hraw :=
      Germ.jacobian_sub_coordinatePolynomial_mem_weightedOrderIdeal
        a m n ha ham han P Q hP hQ f g hf hg
    change Germ.jacobian f g - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.weightedOrderIdeal a (m + n - a) at hraw
    have hthreshold : D + 1 = m + n - a := by
      dsimp only [D]
      omega
    rw [hthreshold]
    exact hraw
  have hfactor :=
    Germ.secondVariable_pow_dvd_of_dvd_weighted_initial_form
      a D N (Germ.jacobian f g) R hR htail hdiv
  simpa only [formT, R] using hfactor

/-- Source scaling and independent target scalings preserve the polynomial
Jacobian divisibility obtained from analytic initial forms. -/
theorem formT_pow_dvd_rescaled_polynomial_jacobian_of_analytic_divisibility
    (a m n N : ℕ) (ha : 0 < a) (ham : a ≤ m) (han : a ≤ n)
    (P Q : Form ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] m)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] n)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (m + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (n + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ N ∣ Germ.jacobian f g)
    (s u v : ℂ) :
    formT ^ N ∣ OnLeConjecture.Polynomial.jacobian
      (rescaleForm s u P) (rescaleForm s v Q) := by
  apply formT_pow_dvd_jacobian_rescaleForm
  exact formT_pow_dvd_polynomial_jacobian_of_analytic_divisibility
    a m n N ha ham han P Q hP hQ f g hf hg hdiv

/-- The rescaled Jacobian formula records the source scalar and both target
scalars together with the transported divisibility. -/
theorem rescaled_polynomial_jacobian_formula_and_divisibility_of_analytic
    (a m n N : ℕ) (ha : 0 < a) (ham : a ≤ m) (han : a ≤ n)
    (P Q : Form ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] m)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] n)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (m + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (n + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ N ∣ Germ.jacobian f g)
    (s u v : ℂ) :
    OnLeConjecture.Polynomial.jacobian
        (rescaleForm s u P) (rescaleForm s v Q) =
      MvPolynomial.C (u * v * s) *
        OnLeConjecture.Analytic.diagonalPolynomialSubstitution
          (sourceRescaleVector s)
          (OnLeConjecture.Polynomial.jacobian P Q) ∧
    formT ^ N ∣ OnLeConjecture.Polynomial.jacobian
      (rescaleForm s u P) (rescaleForm s v Q) := by
  refine ⟨jacobian_rescaleForm s u v P Q, ?_⟩
  exact formT_pow_dvd_rescaled_polynomial_jacobian_of_analytic_divisibility
    a m n N ha ham han P Q hP hQ f g hf hg hdiv s u v

/-- For two ordinary homogeneous forms of positive degree, analytic
divisibility of their weighted substitutions by `y^(6a-1)` implies the
fifth power divisibility of their ordinary Jacobian. -/
theorem formT_five_dvd_jacobian_of_analytic_weighted_power_initial_forms
    (a r s : ℕ) (ha : 0 < a) (hr : 0 < r) (hs : 0 < s)
    (F G : Form ℂ) (hF : F.IsHomogeneous r) (hG : G.IsHomogeneous s)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2
        (weightedPowerSubstitutionForm a F) ∈
      Germ.weightedOrderIdeal a (a * r + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2
        (weightedPowerSubstitutionForm a G) ∈
      Germ.weightedOrderIdeal a (a * s + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian f g) :
    formT ^ 5 ∣ OnLeConjecture.Polynomial.jacobian F G := by
  have hweighted : formT ^ (6 * a - 1) ∣
      OnLeConjecture.Polynomial.jacobian
        (weightedPowerSubstitutionForm a F)
        (weightedPowerSubstitutionForm a G) := by
    apply formT_pow_dvd_polynomial_jacobian_of_analytic_divisibility
      a (a * r) (a * s) (6 * a - 1) ha
        (Nat.le_mul_of_pos_right a hr) (Nat.le_mul_of_pos_right a hs)
        (weightedPowerSubstitutionForm a F)
        (weightedPowerSubstitutionForm a G)
        (weightedPowerSubstitutionForm_isWeightedHomogeneous a r F hF)
        (weightedPowerSubstitutionForm_isWeightedHomogeneous a s G hG)
        f g hf hg hdiv
  exact formT_five_dvd_jacobian_of_weighted_substitution_divisibility
    a ha F G hweighted

/-- The fifth power divisibility obtained after weighted power descent is
preserved by source and target rescaling of the ordinary forms. -/
theorem
    formT_five_dvd_rescaled_jacobian_of_analytic_weighted_power_initial_forms
    (a r s : ℕ) (ha : 0 < a) (hr : 0 < r) (hs : 0 < s)
    (F G : Form ℂ) (hF : F.IsHomogeneous r) (hG : G.IsHomogeneous s)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2
        (weightedPowerSubstitutionForm a F) ∈
      Germ.weightedOrderIdeal a (a * r + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2
        (weightedPowerSubstitutionForm a G) ∈
      Germ.weightedOrderIdeal a (a * s + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (6 * a - 1) ∣
      Germ.jacobian f g)
    (lambda u v : ℂ) :
    formT ^ 5 ∣ OnLeConjecture.Polynomial.jacobian
      (rescaleForm lambda u F) (rescaleForm lambda v G) := by
  apply formT_pow_dvd_jacobian_rescaleForm
  exact formT_five_dvd_jacobian_of_analytic_weighted_power_initial_forms
    a r s ha hr hs F G hF hG f g hf hg hdiv

end OnLeConjecture.DThree
