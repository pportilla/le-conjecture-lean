/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EJacobianDescent
public import OnLeConjecture.DThree.WeightedResidueDecomposition
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Jacobian descent through a power substitution

Replacing the second variable by its `a`th power multiplies a Jacobian by
`a y^(a-1)`. This module cancels that factor and reflects divisibility through
the substitution. It supplies the ordinary fifth power divisibility used in
the E and H residue zero arguments.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Polynomial

/-- The first partial derivative commutes with the power substitution in the
second variable. -/
theorem pderiv_zero_weightedPowerSubstitutionForm
    (a : ℕ) (F : Form ℂ) :
    MvPolynomial.pderiv (0 : Fin 2) (weightedPowerSubstitutionForm a F) =
      weightedPowerSubstitutionForm a (MvPolynomial.pderiv 0 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
      simp only [map_mul (weightedPowerSubstitutionForm a),
        MvPolynomial.pderiv_mul, map_add, hp]
      fin_cases n
      · simp [weightedPowerSubstitutionForm, formX]
      · simp [weightedPowerSubstitutionForm, formT]

/-- The second partial derivative after the power substitution has the
factor `a y^(a-1)`. -/
theorem pderiv_one_weightedPowerSubstitutionForm
    (a : ℕ) (F : Form ℂ) :
    MvPolynomial.pderiv (1 : Fin 2) (weightedPowerSubstitutionForm a F) =
      MvPolynomial.C (a : ℂ) * formT ^ (a - 1) *
        weightedPowerSubstitutionForm a (MvPolynomial.pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
  | mul_X p n hp =>
      simp only [map_mul (weightedPowerSubstitutionForm a),
        MvPolynomial.pderiv_mul, map_add, hp]
      fin_cases n
      · simp [weightedPowerSubstitutionForm, formX]
        ring
      · simp [weightedPowerSubstitutionForm, formT]
        ring

/-- The Jacobian of two substituted forms is the substituted ordinary
Jacobian multiplied by `a y^(a-1)`. -/
theorem jacobian_weightedPowerSubstitutionForm
    (a : ℕ) (F G : Form ℂ) :
    jacobian (weightedPowerSubstitutionForm a F)
        (weightedPowerSubstitutionForm a G) =
      MvPolynomial.C (a : ℂ) * formT ^ (a - 1) *
        weightedPowerSubstitutionForm a (jacobian F G) := by
  rw [jacobian, jacobian, pderiv_zero_weightedPowerSubstitutionForm,
    pderiv_zero_weightedPowerSubstitutionForm,
    pderiv_one_weightedPowerSubstitutionForm,
    pderiv_one_weightedPowerSubstitutionForm, map_sub, map_mul, map_mul]
  ring

/-- In the presentation as a polynomial in the second variable, power
substitution is polynomial expansion by `a`. -/
theorem eFormToIterated_weightedPowerSubstitutionForm
    (a : ℕ) (F : Form ℂ) :
    eFormToIterated (weightedPowerSubstitutionForm a F) =
      Polynomial.expand (Polynomial ℂ) a (eFormToIterated F) := by
  let right : Form ℂ →ₐ[ℂ] EIteratedSourceRing :=
    ((Polynomial.expand (Polynomial ℂ) a).restrictScalars ℂ).comp
      eFormToIterated
  have hequality : eFormToIterated.comp (weightedPowerSubstitutionForm a) =
      right := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change eFormToIterated (weightedPowerSubstitutionForm a formX) =
        Polynomial.expand (Polynomial ℂ) a (eFormToIterated formX)
      rw [weightedPowerSubstitutionForm_x, eFormToIterated_x,
        Polynomial.expand_C]
    · change eFormToIterated (weightedPowerSubstitutionForm a formT) =
        Polynomial.expand (Polynomial ℂ) a (eFormToIterated formT)
      rw [weightedPowerSubstitutionForm_t, map_pow, eFormToIterated_t,
        Polynomial.expand_X]
  exact AlgHom.congr_fun hequality F

/-- Divisibility by the substituted `n`th power of the second variable
reflects to divisibility before substitution. -/
theorem formT_pow_dvd_of_weightedPowerSubstitutionForm_dvd
    (a n : ℕ) (ha : 0 < a) (F : Form ℂ)
    (hdiv : formT ^ (a * n) ∣ weightedPowerSubstitutionForm a F) :
    formT ^ n ∣ F := by
  have hmap := map_dvd eFormToIterated hdiv
  rw [map_pow, eFormToIterated_t,
    eFormToIterated_weightedPowerSubstitutionForm] at hmap
  have houter : Polynomial.X ^ n ∣ eFormToIterated F := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have hcoeff := Polynomial.X_pow_dvd_iff.mp hmap (a * d) (by
      exact (Nat.mul_lt_mul_left ha).mpr hd)
    simpa only [Polynomial.coeff_expand_mul' ha] using hcoeff
  have hback := map_dvd eIteratedToForm houter
  rw [map_pow, eIteratedToForm_outerX] at hback
  have hequality : eIteratedToForm (eFormToIterated F) = F := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eIteratedToForm_comp_formToIterated F
  rwa [hequality] at hback

/-- Divisibility of the substituted Jacobian by `y^(6a-1)` implies
divisibility of the ordinary Jacobian by the fifth power of the second
variable. -/
theorem formT_five_dvd_jacobian_of_weighted_substitution_divisibility
    (a : ℕ) (ha : 0 < a) (F G : Form ℂ)
    (hdiv : formT ^ (6 * a - 1) ∣
      jacobian (weightedPowerSubstitutionForm a F)
        (weightedPowerSubstitutionForm a G)) :
    formT ^ 5 ∣ jacobian F G := by
  obtain ⟨A, hA⟩ := hdiv
  let inverseA : Form ℂ := MvPolynomial.C ((a : ℂ)⁻¹)
  have haComplex : (a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  have hscalar : MvPolynomial.C (a : ℂ) * inverseA = 1 := by
    dsimp only [inverseA]
    rw [← map_mul, mul_inv_cancel₀ haComplex, map_one]
  have ht : (formT : Form ℂ) ≠ 0 :=
    MvPolynomial.X_ne_zero (R := ℂ) (1 : Fin 2)
  have hfactor : MvPolynomial.C (a : ℂ) * formT ^ (a - 1) ≠ 0 :=
    mul_ne_zero (MvPolynomial.C_ne_zero.mpr haComplex)
      (pow_ne_zero _ ht)
  have hsubstitution :
      formT ^ (5 * a) ∣
        weightedPowerSubstitutionForm a (jacobian F G) := by
    refine ⟨inverseA * A, ?_⟩
    apply mul_left_cancel₀ hfactor
    calc
      (MvPolynomial.C (a : ℂ) * formT ^ (a - 1)) *
            weightedPowerSubstitutionForm a (jacobian F G) =
          jacobian (weightedPowerSubstitutionForm a F)
            (weightedPowerSubstitutionForm a G) :=
        (jacobian_weightedPowerSubstitutionForm a F G).symm
      _ = formT ^ (6 * a - 1) * A := hA
      _ = (MvPolynomial.C (a : ℂ) * formT ^ (a - 1)) *
          (formT ^ (5 * a) * (inverseA * A)) := by
        rw [show 6 * a - 1 = (a - 1) + 5 * a by omega, pow_add]
        calc
          (formT ^ (a - 1) * formT ^ (5 * a)) * A =
              1 * ((formT ^ (a - 1) * formT ^ (5 * a)) * A) := by
                ring
          _ = (MvPolynomial.C (a : ℂ) * inverseA) *
              ((formT ^ (a - 1) * formT ^ (5 * a)) * A) := by
                rw [hscalar]
          _ = _ := by ring
  apply formT_pow_dvd_of_weightedPowerSubstitutionForm_dvd
    a 5 ha (jacobian F G)
  simpa [Nat.mul_comm] using hsubstitution

end OnLeConjecture.DThree
