/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HProjectiveDifferenceZero
public import OnLeConjecture.DThree.Rescaling
public import OnLeConjecture.Polynomial.WeightedJacobian
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Jacobian divisibility after quadratic substitution in the H case

A weighted form in `x,w` is pulled back by `w = t ^ 2`. Its ordinary
Jacobian acquires the factor `2t`. Consequently, literal divisibility of the
ordinary Jacobian by `t ^ 5` implies divisibility of the weighted Jacobian by
`w ^ 2`.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- The iterated presentation `K[x][w]` of the weighted polynomial ring. -/
abbrev HIteratedWeightedRing (K : Type*) [CommSemiring K] :=
  Polynomial (Polynomial K)

/-- Present a weighted form as a polynomial in `w` with coefficients in
`K[x]`. -/
noncomputable def hWeightedFormToIterated :
    MvPolynomial (Fin 2) K →ₐ[K] HIteratedWeightedRing K :=
  MvPolynomial.aeval fun i => if i = 0 then C X else X

/-- Return from the iterated presentation to the weighted variables. -/
noncomputable def hIteratedToWeightedForm :
    HIteratedWeightedRing K →ₐ[K] MvPolynomial (Fin 2) K :=
  Polynomial.aevalAeval hFormX hFormW

@[simp]
theorem hWeightedFormToIterated_x :
    hWeightedFormToIterated (K := K) (hFormX (K := K)) =
      (C X : HIteratedWeightedRing K) := by
  rw [hWeightedFormToIterated, hFormX, MvPolynomial.aeval_X]
  simp

@[simp]
theorem hWeightedFormToIterated_w :
    hWeightedFormToIterated (K := K) (hFormW (K := K)) =
      (X : HIteratedWeightedRing K) := by
  rw [hWeightedFormToIterated, hFormW, MvPolynomial.aeval_X]
  simp

@[simp]
theorem hIteratedToWeightedForm_innerX :
    hIteratedToWeightedForm (K := K)
        (C X : HIteratedWeightedRing K) = hFormX := by
  exact Polynomial.aevalAeval_X hFormX hFormW

@[simp]
theorem hIteratedToWeightedForm_outerX :
    hIteratedToWeightedForm (K := K)
        (X : HIteratedWeightedRing K) = hFormW := by
  exact Polynomial.aevalAeval_Y hFormX hFormW

theorem hIteratedToWeightedForm_comp_weightedFormToIterated :
    hIteratedToWeightedForm.comp hWeightedFormToIterated =
      AlgHom.id K (MvPolynomial (Fin 2) K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change hIteratedToWeightedForm
      (hWeightedFormToIterated hFormX) = hFormX
    rw [hWeightedFormToIterated_x,
      hIteratedToWeightedForm_innerX]
  · change hIteratedToWeightedForm
      (hWeightedFormToIterated hFormW) = hFormW
    rw [hWeightedFormToIterated_w,
      hIteratedToWeightedForm_outerX]

/-- Substitute `w = t ^ 2` in a weighted form. -/
@[expose]
noncomputable def hQuadraticSubstitutionForm :
    MvPolynomial (Fin 2) K →ₐ[K] Form K :=
  MvPolynomial.aeval fun i => if i = 0 then formX else formT ^ 2

@[simp]
theorem hQuadraticSubstitutionForm_x :
    hQuadraticSubstitutionForm (K := K) (hFormX (K := K)) =
      (formX : Form K) := by
  rw [hQuadraticSubstitutionForm, hFormX, MvPolynomial.aeval_X]
  simp

@[simp]
theorem hQuadraticSubstitutionForm_w :
    hQuadraticSubstitutionForm (K := K) (hFormW (K := K)) =
      (formT : Form K) ^ 2 := by
  rw [hQuadraticSubstitutionForm, hFormW, MvPolynomial.aeval_X]
  simp

/-- Quadratic substitution sends the first weighted coordinate to the
normalized cubic form of the `H` pair. -/
theorem hQuadraticSubstitutionForm_hPForm :
    hQuadraticSubstitutionForm (hPForm (K := K)) =
      cubicForm 3 0 := by
  simp only [hPForm, cubicForm, map_add, map_mul, map_pow,
    hQuadraticSubstitutionForm_x, hQuadraticSubstitutionForm_w,
    map_ofNat, map_zero]
  ring

/-- Quadratic substitution sends the second weighted coordinate to the
normalized quartic form of the `H` pair. -/
theorem hQuadraticSubstitutionForm_hQForm :
    hQuadraticSubstitutionForm (hQForm (K := K)) =
      quarticForm 1 0 4 0 2 := by
  simp only [hQForm, quarticForm, map_add, map_mul, map_pow,
    hQuadraticSubstitutionForm_x, hQuadraticSubstitutionForm_w,
    map_ofNat, map_zero, map_one]
  ring

@[simp]
theorem h_pderiv_x_formX :
    MvPolynomial.pderiv (0 : Fin 2) (formX : Form K) = 1 := by
  simp [formX]

@[simp]
theorem h_pderiv_x_formT :
    MvPolynomial.pderiv (0 : Fin 2) (formT : Form K) = 0 := by
  simp [formT]

@[simp]
theorem h_pderiv_t_formX :
    MvPolynomial.pderiv (1 : Fin 2) (formX : Form K) = 0 := by
  simp [formX]

@[simp]
theorem h_pderiv_t_formT :
    MvPolynomial.pderiv (1 : Fin 2) (formT : Form K) = 1 := by
  simp [formT]

/-- Differentiation in `x` commutes with quadratic substitution. -/
theorem h_pderiv_x_quadraticSubstitutionForm
    (F : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv (0 : Fin 2)
        (hQuadraticSubstitutionForm F) =
      hQuadraticSubstitutionForm (MvPolynomial.pderiv 0 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
      simp only [map_mul, MvPolynomial.pderiv_mul, hF]
      fin_cases i
      · simp [hQuadraticSubstitutionForm, formX, formT]
      · simp [hQuadraticSubstitutionForm, formX, formT]

/-- Differentiation in `t` after quadratic substitution contributes the
factor `2t`. -/
theorem h_pderiv_t_quadraticSubstitutionForm
    (F : MvPolynomial (Fin 2) K) :
    MvPolynomial.pderiv (1 : Fin 2)
        (hQuadraticSubstitutionForm F) =
      2 * formT *
        hQuadraticSubstitutionForm (MvPolynomial.pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add F G hF hG =>
      simp only [map_add, hF, hG]
      ring
  | mul_X F i hF =>
      simp only [map_mul, MvPolynomial.pderiv_mul, hF]
      fin_cases i
      · simp [hQuadraticSubstitutionForm, formX, formT]
        ring
      · simp [hQuadraticSubstitutionForm, formX, formT]
        ring

/-- The ordinary Jacobian of two quadratic pullbacks is `2t` times the
pullback of their weighted Jacobian. -/
theorem h_jacobian_quadraticSubstitutionForm
    (F G : MvPolynomial (Fin 2) K) :
    OnLeConjecture.Polynomial.jacobian
        (hQuadraticSubstitutionForm F)
        (hQuadraticSubstitutionForm G) =
      2 * formT * hQuadraticSubstitutionForm
        (hFormJacobian F G) := by
  rw [OnLeConjecture.Polynomial.jacobian, hFormJacobian,
    h_pderiv_x_quadraticSubstitutionForm,
    h_pderiv_t_quadraticSubstitutionForm,
    h_pderiv_x_quadraticSubstitutionForm,
    h_pderiv_t_quadraticSubstitutionForm]
  simp only [map_sub, map_mul]
  ring

/-- Restrict a weighted form to `w = 0`. -/
noncomputable def hWeightedFormAtWZero :
    MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval fun i => if i = 0 then X else 0

/-- Restrict an ordinary form to `t = 0`. -/
noncomputable def hFormAtTZero :
    Form K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval fun i => if i = 0 then X else 0

@[simp]
theorem hFormAtTZero_t : hFormAtTZero (formT : Form K) = 0 := by
  rw [hFormAtTZero, formT, MvPolynomial.aeval_X]
  simp

theorem hFormAtTZero_comp_quadraticSubstitutionForm :
    (hFormAtTZero (K := K)).comp
        (hQuadraticSubstitutionForm (K := K)) =
      hWeightedFormAtWZero (K := K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change hFormAtTZero
      (hQuadraticSubstitutionForm hFormX) =
        hWeightedFormAtWZero hFormX
    rw [hQuadraticSubstitutionForm_x]
    simp [hFormAtTZero, hWeightedFormAtWZero, formX, hFormX]
  · change hFormAtTZero
      (hQuadraticSubstitutionForm hFormW) =
        hWeightedFormAtWZero hFormW
    rw [hQuadraticSubstitutionForm_w]
    simp [hFormAtTZero, hWeightedFormAtWZero, formT, hFormW]

/-- Evaluation of the outer variable of the iterated presentation at zero. -/
noncomputable def hIteratedAtOuterZero :
    HIteratedWeightedRing K →ₐ[K] Polynomial K :=
  Polynomial.eval₂AlgHom (AlgHom.id K (Polynomial K)) 0
    fun _ => Commute.all _ _

theorem hIteratedAtOuterZero_eq_coeff_zero
    (F : HIteratedWeightedRing K) :
    hIteratedAtOuterZero F = F.coeff 0 := by
  simp [hIteratedAtOuterZero, _root_.Polynomial.eval₂_at_zero]

theorem hIteratedAtOuterZero_comp_weightedFormToIterated :
    (hIteratedAtOuterZero (K := K)).comp
        (hWeightedFormToIterated (K := K)) =
      hWeightedFormAtWZero (K := K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change hIteratedAtOuterZero
      (hWeightedFormToIterated hFormX) =
        hWeightedFormAtWZero hFormX
    rw [hWeightedFormToIterated_x,
      hIteratedAtOuterZero_eq_coeff_zero]
    simp [hWeightedFormAtWZero, hFormX]
  · change hIteratedAtOuterZero
      (hWeightedFormToIterated hFormW) =
        hWeightedFormAtWZero hFormW
    rw [hWeightedFormToIterated_w,
      hIteratedAtOuterZero_eq_coeff_zero]
    simp [hWeightedFormAtWZero, hFormW]

/-- Divisibility of a quadratic pullback by `t ^ 2` reflects to divisibility
of the weighted form by `w`. -/
theorem hFormW_dvd_of_formT_sq_dvd_quadraticSubstitutionForm
    (F : MvPolynomial (Fin 2) K)
    (hdiv : formT ^ 2 ∣ hQuadraticSubstitutionForm F) :
    hFormW ∣ F := by
  have hzero : hWeightedFormAtWZero F = 0 := by
    obtain ⟨A, hA⟩ := hdiv
    have heval := congrArg hFormAtTZero hA
    rw [map_mul, map_pow, hFormAtTZero_t,
      zero_pow (by norm_num : 2 ≠ 0), zero_mul] at heval
    calc
      hWeightedFormAtWZero F =
          hFormAtTZero (hQuadraticSubstitutionForm F) := by
        exact (AlgHom.congr_fun
          hFormAtTZero_comp_quadraticSubstitutionForm F).symm
      _ = 0 := heval
  have hcoeff : (hWeightedFormToIterated F).coeff 0 = 0 := by
    calc
      (hWeightedFormToIterated F).coeff 0 =
          hIteratedAtOuterZero (hWeightedFormToIterated F) := by
        rw [hIteratedAtOuterZero_eq_coeff_zero]
      _ = hWeightedFormAtWZero F :=
        AlgHom.congr_fun
          hIteratedAtOuterZero_comp_weightedFormToIterated F
      _ = 0 := hzero
  have hXd : X ∣ hWeightedFormToIterated F :=
    Polynomial.X_dvd_iff.mpr hcoeff
  have hmap := map_dvd hIteratedToWeightedForm hXd
  have hback :
      hIteratedToWeightedForm (hWeightedFormToIterated F) = F := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun
        hIteratedToWeightedForm_comp_weightedFormToIterated F
  rw [hIteratedToWeightedForm_outerX, hback] at hmap
  exact hmap

/-- Divisibility of a quadratic pullback by `t ^ 4` reflects to divisibility
of the weighted form by `w ^ 2`. -/
theorem hFormW_sq_dvd_of_formT_four_dvd_quadraticSubstitutionForm
    (F : MvPolynomial (Fin 2) K)
    (hdiv : formT ^ 4 ∣ hQuadraticSubstitutionForm F) :
    hFormW ^ 2 ∣ F := by
  have htTwoDvdFour : (formT : Form K) ^ 2 ∣ formT ^ 4 := by
    refine ⟨formT ^ 2, ?_⟩
    ring
  have hwDvd : hFormW (K := K) ∣ F :=
    hFormW_dvd_of_formT_sq_dvd_quadraticSubstitutionForm F
      (htTwoDvdFour.trans hdiv)
  obtain ⟨G, hG⟩ := hwDvd
  obtain ⟨A, hA⟩ := hdiv
  have hsubstitution :
      hQuadraticSubstitutionForm F =
        formT ^ 2 * hQuadraticSubstitutionForm G := by
    rw [hG, map_mul, hQuadraticSubstitutionForm_w]
  have htTwo : (formT : Form K) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (MvPolynomial.X_ne_zero (R := K) (1 : Fin 2))
  have hGdiv : formT ^ 2 ∣ hQuadraticSubstitutionForm G := by
    refine ⟨A, ?_⟩
    apply mul_left_cancel₀ htTwo
    calc
      formT ^ 2 * hQuadraticSubstitutionForm G =
          hQuadraticSubstitutionForm F := hsubstitution.symm
      _ = formT ^ 4 * A := hA
      _ = formT ^ 2 * (formT ^ 2 * A) := by ring
  obtain ⟨H, hH⟩ :=
    hFormW_dvd_of_formT_sq_dvd_quadraticSubstitutionForm G hGdiv
  refine ⟨H, ?_⟩
  rw [hG, hH]
  ring

/-- Literal divisibility by `t ^ 5` leaves divisibility by `t ^ 4` after
removing the Jacobian factor `2t`. -/
theorem h_formT_four_dvd_weightedJacobian_substitution_of_formT_five_dvd
    [CharZero K]
    (F G : MvPolynomial (Fin 2) K)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (hQuadraticSubstitutionForm F)
        (hQuadraticSubstitutionForm G)) :
    formT ^ 4 ∣ hQuadraticSubstitutionForm (hFormJacobian F G) := by
  obtain ⟨A, hA⟩ := hdiv
  let inverseTwo : Form K := MvPolynomial.C ((2 : K)⁻¹)
  have hscalar : (2 : Form K) * inverseTwo = 1 := by
    dsimp only [inverseTwo]
    change MvPolynomial.C (2 : K) *
        MvPolynomial.C ((2 : K)⁻¹) = 1
    rw [← map_mul]
    norm_num
  have ht : (formT : Form K) ≠ 0 :=
    MvPolynomial.X_ne_zero (R := K) (1 : Fin 2)
  have hfactor : (2 : Form K) * formT ≠ 0 :=
    mul_ne_zero (by norm_num) ht
  refine ⟨inverseTwo * A, ?_⟩
  apply mul_left_cancel₀ hfactor
  calc
    ((2 : Form K) * formT) *
          hQuadraticSubstitutionForm (hFormJacobian F G) =
        OnLeConjecture.Polynomial.jacobian
          (hQuadraticSubstitutionForm F)
          (hQuadraticSubstitutionForm G) :=
      (h_jacobian_quadraticSubstitutionForm F G).symm
    _ = formT ^ 5 * A := hA
    _ = ((2 : Form K) * formT) *
        (formT ^ 4 * (inverseTwo * A)) := by
      calc
        formT ^ 5 * A = 1 * (formT ^ 5 * A) := by ring
        _ = ((2 : Form K) * inverseTwo) *
            (formT ^ 5 * A) := by rw [hscalar]
        _ = ((2 : Form K) * formT) *
            (formT ^ 4 * (inverseTwo * A)) := by ring

/-- The two literal `t ^ 5` Jacobian divisibilities produce the weighted
Jacobian quotients required by the conic argument. -/
theorem exists_h_jacobian_quotients_of_literal_divisibilities
    [CharZero K]
    (R : MvPolynomial (Fin 2) K)
    (hPdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (cubicForm 3 0) (hQuadraticSubstitutionForm R))
    (hQdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (quarticForm 1 0 4 0 2) (hQuadraticSubstitutionForm R)) :
    ∃ LambdaP LambdaQ : MvPolynomial (Fin 2) K,
      hFormJacobian hPForm R = hFormW ^ 2 * LambdaP ∧
      hFormJacobian hQForm R = hFormW ^ 2 * LambdaQ := by
  have hPdiv' : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (hQuadraticSubstitutionForm (hPForm (K := K)))
        (hQuadraticSubstitutionForm R) := by
    simpa only [hQuadraticSubstitutionForm_hPForm] using hPdiv
  have hQdiv' : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian
        (hQuadraticSubstitutionForm (hQForm (K := K)))
        (hQuadraticSubstitutionForm R) := by
    simpa only [hQuadraticSubstitutionForm_hQForm] using hQdiv
  have hPfour :=
    h_formT_four_dvd_weightedJacobian_substitution_of_formT_five_dvd
      hPForm R hPdiv'
  have hQfour :=
    h_formT_four_dvd_weightedJacobian_substitution_of_formT_five_dvd
      hQForm R hQdiv'
  have hPweighted :=
    hFormW_sq_dvd_of_formT_four_dvd_quadraticSubstitutionForm
      (hFormJacobian hPForm R) hPfour
  have hQweighted :=
    hFormW_sq_dvd_of_formT_four_dvd_quadraticSubstitutionForm
      (hFormJacobian hQForm R) hQfour
  rcases hPweighted with ⟨LambdaP, hLambdaP⟩
  rcases hQweighted with ⟨LambdaQ, hLambdaQ⟩
  exact ⟨LambdaP, LambdaQ, hLambdaP, hLambdaQ⟩

end OnLeConjecture.DThree
