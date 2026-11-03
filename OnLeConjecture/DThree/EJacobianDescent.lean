/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.Rescaling
public import OnLeConjecture.DThree.EInvariantDescent
public import OnLeConjecture.DThree.EJacobianDiagonal
public import OnLeConjecture.DThree.EThetaBridge
public import OnLeConjecture.Polynomial.WeightedJacobian
public import Mathlib.Tactic.Ring

/-!
# Jacobian divisibility after cubic descent for the `E` pair

This file connects the homogeneous variables `x,t` with the source ring
`C[x,w]`, where `w=t^3`.  It transports the Jacobian divisibility condition
through cubic invariant descent and obtains divisibility of the characteristic
derivative by `w`.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The natural presentation of a homogeneous form as a polynomial in `t`
with coefficients in `C[x]`. -/
noncomputable def eFormToIterated :
    Form ℂ →ₐ[ℂ] EIteratedSourceRing :=
  MvPolynomial.aeval fun i => if i = 0 then C X else X

/-- The inverse presentation sends the inner and outer polynomial variables
to `x` and `t`. -/
noncomputable def eIteratedToForm :
    EIteratedSourceRing →ₐ[ℂ] Form ℂ :=
  Polynomial.aevalAeval formX formT

@[simp]
theorem eFormToIterated_x :
    eFormToIterated formX = C X := by
  rw [eFormToIterated, formX, MvPolynomial.aeval_X]
  simp

@[simp]
theorem eFormToIterated_t :
    eFormToIterated formT = X := by
  rw [eFormToIterated, formT, MvPolynomial.aeval_X]
  simp

@[simp]
theorem eIteratedToForm_innerX :
    eIteratedToForm (C X) = formX := by
  exact Polynomial.aevalAeval_X formX formT

@[simp]
theorem eIteratedToForm_outerX :
    eIteratedToForm X = formT := by
  exact Polynomial.aevalAeval_Y formX formT

theorem eIteratedToForm_comp_formToIterated :
    eIteratedToForm.comp eFormToIterated =
      AlgHom.id ℂ (Form ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change eIteratedToForm (eFormToIterated formX) = formX
    rw [eFormToIterated_x, eIteratedToForm_innerX]
  · change eIteratedToForm (eFormToIterated formT) = formT
    rw [eFormToIterated_t, eIteratedToForm_outerX]

theorem eFormToIterated_comp_iteratedToForm :
    eFormToIterated.comp eIteratedToForm =
      AlgHom.id ℂ EIteratedSourceRing := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    change eFormToIterated (eIteratedToForm (C X)) = C X
    rw [eIteratedToForm_innerX, eFormToIterated_x]
  · change eFormToIterated (eIteratedToForm X) = X
    rw [eIteratedToForm_outerX, eFormToIterated_t]

/-- Homogeneous forms and iterated polynomials are isomorphic. -/
noncomputable def eFormEquivIterated :
    Form ℂ ≃ₐ[ℂ] EIteratedSourceRing :=
  AlgEquiv.ofAlgHom eFormToIterated eIteratedToForm
    eFormToIterated_comp_iteratedToForm
    eIteratedToForm_comp_formToIterated

/-- Substitute `w=t^3` in a polynomial in `C[x,w]`. -/
noncomputable def eSourceCubeSubstitutionForm :
    ESourceRing ℂ →ₐ[ℂ] Form ℂ :=
  MvPolynomial.aeval fun
    | ESourceCoordinate.x => formX
    | ESourceCoordinate.w => formT ^ 3

@[simp]
theorem eSourceCubeSubstitutionForm_x :
    eSourceCubeSubstitutionForm (eSourceX ℂ) = formX := by
  rw [eSourceCubeSubstitutionForm, eSourceX, MvPolynomial.aeval_X]

@[simp]
theorem eSourceCubeSubstitutionForm_w :
    eSourceCubeSubstitutionForm (eSourceW ℂ) = formT ^ 3 := by
  rw [eSourceCubeSubstitutionForm, eSourceW, MvPolynomial.aeval_X]

theorem eFormToIterated_comp_sourceCubeSubstitutionForm :
    eFormToIterated.comp eSourceCubeSubstitutionForm =
      eSourceCubeSubstitution := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | x =>
      change eFormToIterated
          (eSourceCubeSubstitutionForm (eSourceX ℂ)) =
        eSourceCubeSubstitution (eSourceX ℂ)
      rw [eSourceCubeSubstitutionForm_x, eFormToIterated_x,
        eSourceCubeSubstitution_x]
  | w =>
      change eFormToIterated
          (eSourceCubeSubstitutionForm (eSourceW ℂ)) =
        eSourceCubeSubstitution (eSourceW ℂ)
      rw [eSourceCubeSubstitutionForm_w, map_pow,
        eFormToIterated_t, eSourceCubeSubstitution_w]

/-- The normalized cubic form is the pullback of `P=x^3+3w` under
`w=t^3`. -/
theorem eSourceCubeSubstitutionForm_sourceP :
    eSourceCubeSubstitutionForm (eSourceP ℂ) =
      cubicForm 0 3 := by
  simp only [eSourceP, cubicForm, map_add, map_pow, map_mul,
    eSourceCubeSubstitutionForm_x, eSourceCubeSubstitutionForm_w,
    map_ofNat, formX, formT]
  simp only [map_zero]
  ring

/-- The normalized quartic form is the pullback of `Q=x^4+4xw` under
`w=t^3`. -/
theorem eSourceCubeSubstitutionForm_sourceQ :
    eSourceCubeSubstitutionForm (eSourceQ ℂ) =
      quarticForm 1 0 0 4 0 := by
  simp only [eSourceQ, quarticForm, map_add, map_pow, map_mul,
    eSourceCubeSubstitutionForm_x, eSourceCubeSubstitutionForm_w,
    map_ofNat, formX, formT]
  simp only [map_zero, map_one]
  ring

@[simp]
theorem e_pderiv_x_sourceX :
    MvPolynomial.pderiv ESourceCoordinate.x (eSourceX ℂ) = 1 := by
  simp [eSourceX]

@[simp]
theorem e_pderiv_x_sourceW :
    MvPolynomial.pderiv ESourceCoordinate.x (eSourceW ℂ) = 0 := by
  simp [eSourceW]

@[simp]
theorem e_pderiv_w_sourceX :
    MvPolynomial.pderiv ESourceCoordinate.w (eSourceX ℂ) = 0 := by
  simp [eSourceX]

@[simp]
theorem e_pderiv_w_sourceW :
    MvPolynomial.pderiv ESourceCoordinate.w (eSourceW ℂ) = 1 := by
  simp [eSourceW]

@[simp]
theorem e_pderiv_x_formX :
    MvPolynomial.pderiv (0 : Fin 2) (formX : Form ℂ) = 1 := by
  simp [formX]

@[simp]
theorem e_pderiv_x_formT :
    MvPolynomial.pderiv (0 : Fin 2) (formT : Form ℂ) = 0 := by
  simp [formT]

@[simp]
theorem e_pderiv_t_formX :
    MvPolynomial.pderiv (1 : Fin 2) (formX : Form ℂ) = 0 := by
  simp [formX]

@[simp]
theorem e_pderiv_t_formT :
    MvPolynomial.pderiv (1 : Fin 2) (formT : Form ℂ) = 1 := by
  simp [formT]

/-- Differentiation in `x` commutes with cubic substitution. -/
theorem e_pderiv_x_sourceCubeSubstitutionForm
    (Rzero : ESourceRing ℂ) :
    MvPolynomial.pderiv (0 : Fin 2)
        (eSourceCubeSubstitutionForm Rzero) =
      eSourceCubeSubstitutionForm
        (MvPolynomial.pderiv ESourceCoordinate.x Rzero) := by
  induction Rzero using MvPolynomial.induction_on with
  | C a =>
      simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.pderiv_mul, hp]
      cases i with
      | x =>
          rw [show MvPolynomial.X ESourceCoordinate.x = eSourceX ℂ by
            rw [eSourceX]]
          simp only [eSourceCubeSubstitutionForm_x,
            e_pderiv_x_formX, e_pderiv_x_sourceX,
            map_add, map_mul, map_one]
      | w =>
          rw [show MvPolynomial.X ESourceCoordinate.w = eSourceW ℂ by
            rw [eSourceW]]
          simp only [eSourceCubeSubstitutionForm_w,
            MvPolynomial.pderiv_pow, e_pderiv_x_formT,
            e_pderiv_x_sourceW, mul_zero, map_add, map_mul, map_zero]

/-- Differentiation in `t` after cubic substitution contributes the factor
`3t^2`. -/
theorem e_pderiv_t_sourceCubeSubstitutionForm
    (Rzero : ESourceRing ℂ) :
    MvPolynomial.pderiv (1 : Fin 2)
        (eSourceCubeSubstitutionForm Rzero) =
      3 * formT ^ 2 *
        eSourceCubeSubstitutionForm
          (MvPolynomial.pderiv ESourceCoordinate.w Rzero) := by
  induction Rzero using MvPolynomial.induction_on with
  | C a =>
      simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.pderiv_mul, hp]
      cases i with
      | x =>
          rw [show MvPolynomial.X ESourceCoordinate.x = eSourceX ℂ by
            rw [eSourceX]]
          simp only [eSourceCubeSubstitutionForm_x,
            e_pderiv_t_formX, e_pderiv_w_sourceX,
            map_add, map_mul, map_zero, mul_zero]
          ring
      | w =>
          rw [show MvPolynomial.X ESourceCoordinate.w = eSourceW ℂ by
            rw [eSourceW]]
          simp only [eSourceCubeSubstitutionForm_w,
            MvPolynomial.pderiv_pow, e_pderiv_t_formT,
            e_pderiv_w_sourceW, mul_one, map_add, map_mul]
          ring

/-- The `x` derivative of the normalized cubic coordinate. -/
theorem e_pderiv_x_cubicForm_E :
    MvPolynomial.pderiv (0 : Fin 2) (cubicForm 0 3 : Form ℂ) =
      3 * formX ^ 2 := by
  simp only [Fin.isValue, cubicForm, formX, MvPolynomial.C_0,
    zero_mul, formT, add_zero, map_add, Derivation.leibniz_pow,
    Nat.add_one_sub_one, MvPolynomial.pderiv_X, Pi.single_eq_same,
    smul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_ofNat,
    Derivation.leibniz, ne_eq, one_ne_zero, not_false_eq_true,
    Pi.single_eq_of_ne, mul_zero,
    MvPolynomial.derivation_C]

/-- The `t` derivative of the normalized cubic coordinate. -/
theorem e_pderiv_t_cubicForm_E :
    MvPolynomial.pderiv (1 : Fin 2) (cubicForm 0 3 : Form ℂ) =
      9 * formT ^ 2 := by
  simp only [Fin.isValue, cubicForm, formX, MvPolynomial.C_0, zero_mul,
    formT, add_zero, map_add, Derivation.leibniz_pow,
    Nat.add_one_sub_one, MvPolynomial.pderiv_X, ne_eq,
    zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
    smul_eq_mul, mul_zero, Derivation.leibniz,
    Pi.single_eq_same, mul_one, nsmul_eq_mul, Nat.cast_ofNat,
    MvPolynomial.derivation_C, zero_add]
  rw [show MvPolynomial.C (3 : ℂ) = (3 : Form ℂ) by
    exact map_natCast (MvPolynomial.C : ℂ →+* Form ℂ) 3]
  ring

/-- The Jacobian of `P=x^3+3t^3` with a cubic pullback is the pullback of
the characteristic derivative, multiplied by `-9t^2`. -/
theorem e_jacobian_sourceCubeSubstitutionForm
    (Rzero : ESourceRing ℂ) :
    OnLeConjecture.Polynomial.jacobian
        (cubicForm 0 3) (eSourceCubeSubstitutionForm Rzero) =
      -9 * formT ^ 2 *
        eSourceCubeSubstitutionForm
          (eCharacteristicDerivation ℂ Rzero) := by
  rw [OnLeConjecture.Polynomial.jacobian,
    e_pderiv_x_cubicForm_E, e_pderiv_t_cubicForm_E,
    e_pderiv_x_sourceCubeSubstitutionForm,
    e_pderiv_t_sourceCubeSubstitutionForm,
    eCharacteristicDerivation_apply]
  simp only [map_sub, map_mul, map_pow,
    eSourceCubeSubstitutionForm_x]
  ring

/-- Restriction of a homogeneous form to `t=0`. -/
noncomputable def eFormAtTZero :
    Form ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun i => if i = 0 then X else 0

@[simp]
theorem eFormAtTZero_x :
    eFormAtTZero formX = X := by
  rw [eFormAtTZero, formX, MvPolynomial.aeval_X]
  simp

@[simp]
theorem eFormAtTZero_t :
    eFormAtTZero formT = 0 := by
  rw [eFormAtTZero, formT, MvPolynomial.aeval_X]
  simp

theorem eFormAtTZero_comp_sourceCubeSubstitutionForm :
    eFormAtTZero.comp eSourceCubeSubstitutionForm =
      eSourceAtWZero ℂ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | x =>
      change eFormAtTZero
          (eSourceCubeSubstitutionForm (eSourceX ℂ)) =
        eSourceAtWZero ℂ (eSourceX ℂ)
      rw [eSourceCubeSubstitutionForm_x, eFormAtTZero_x,
        eSourceAtWZero_x]
  | w =>
      change eFormAtTZero
          (eSourceCubeSubstitutionForm (eSourceW ℂ)) =
        eSourceAtWZero ℂ (eSourceW ℂ)
      rw [eSourceCubeSubstitutionForm_w, map_pow,
        eFormAtTZero_t, zero_pow (by norm_num : 3 ≠ 0),
        eSourceAtWZero_w]

/-- Evaluation of the outer variable of an iterated polynomial at zero. -/
noncomputable def eIteratedAtOuterZero :
    EIteratedSourceRing →ₐ[ℂ] Polynomial ℂ :=
  Polynomial.eval₂AlgHom (AlgHom.id ℂ (Polynomial ℂ)) 0
    fun _ ↦ Commute.all _ _

theorem eIteratedAtOuterZero_eq_coeff_zero
    (F : EIteratedSourceRing) :
    eIteratedAtOuterZero F = F.coeff 0 := by
  simp [eIteratedAtOuterZero, _root_.Polynomial.eval₂_at_zero]

theorem eIteratedAtOuterZero_comp_sourceToIterated :
    eIteratedAtOuterZero.comp eSourceToIterated =
      eSourceAtWZero ℂ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | x =>
      change eIteratedAtOuterZero
          (eSourceToIterated (eSourceX ℂ)) =
        eSourceAtWZero ℂ (eSourceX ℂ)
      rw [eSourceToIterated_x, eIteratedAtOuterZero_eq_coeff_zero,
        coeff_C, eSourceAtWZero_x]
      simp
  | w =>
      change eIteratedAtOuterZero
          (eSourceToIterated (eSourceW ℂ)) =
        eSourceAtWZero ℂ (eSourceW ℂ)
      rw [eSourceToIterated_w, eIteratedAtOuterZero_eq_coeff_zero,
        coeff_X_zero, eSourceAtWZero_w]

/-- Divisibility of a cubic pullback by `t^3` reflects to divisibility by
`w` before substitution. -/
theorem eSourceW_dvd_of_formT_cube_dvd_sourceCubeSubstitutionForm
    (F : ESourceRing ℂ)
    (hdiv : formT ^ 3 ∣ eSourceCubeSubstitutionForm F) :
    eSourceW ℂ ∣ F := by
  have hzero : eSourceAtWZero ℂ F = 0 := by
    obtain ⟨A, hA⟩ := hdiv
    have heval := congrArg eFormAtTZero hA
    rw [map_mul, map_pow, eFormAtTZero_t,
      zero_pow (by norm_num : 3 ≠ 0), zero_mul] at heval
    calc
      eSourceAtWZero ℂ F =
          eFormAtTZero (eSourceCubeSubstitutionForm F) := by
            exact (AlgHom.congr_fun
              eFormAtTZero_comp_sourceCubeSubstitutionForm F).symm
      _ = 0 := heval
  have hcoeff : (eSourceToIterated F).coeff 0 = 0 := by
    calc
      (eSourceToIterated F).coeff 0 =
          eIteratedAtOuterZero (eSourceToIterated F) := by
            rw [eIteratedAtOuterZero_eq_coeff_zero]
      _ = eSourceAtWZero ℂ F :=
        AlgHom.congr_fun eIteratedAtOuterZero_comp_sourceToIterated F
      _ = 0 := hzero
  have hXd : X ∣ eSourceToIterated F :=
    _root_.Polynomial.X_dvd_iff.mpr hcoeff
  have hmap := map_dvd eIteratedToSource hXd
  have hback : eIteratedToSource (eSourceToIterated F) = F := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eIteratedToSource_comp_sourceToIterated F
  rw [eIteratedToSource_outerX, hback] at hmap
  exact hmap

/-- Divisibility of the original Jacobian by `t^5` implies divisibility of
the pulled back characteristic derivative by `t^3`. -/
theorem e_formT_cube_dvd_characteristic_of_formT_five_dvd_jacobian
    (Rzero : ESourceRing ℂ)
    (hdiv :
      formT ^ 5 ∣
        OnLeConjecture.Polynomial.jacobian (cubicForm 0 3)
          (eSourceCubeSubstitutionForm Rzero)) :
    formT ^ 3 ∣
      eSourceCubeSubstitutionForm
        (eCharacteristicDerivation ℂ Rzero) := by
  obtain ⟨A, hA⟩ := hdiv
  let inverseNine : Form ℂ := MvPolynomial.C ((-9 : ℂ)⁻¹)
  have hscalar :
      (-9 : Form ℂ) * inverseNine = 1 := by
    dsimp only [inverseNine]
    rw [show (-9 : Form ℂ) = MvPolynomial.C (-9 : ℂ) by
      calc
        (-9 : Form ℂ) = -(9 : Form ℂ) := rfl
        _ = -MvPolynomial.C (9 : ℂ) := by
          rw [show (9 : Form ℂ) = MvPolynomial.C (9 : ℂ) by
            exact (map_natCast
              (MvPolynomial.C : ℂ →+* Form ℂ) 9).symm]
        _ = MvPolynomial.C (-9 : ℂ) := by rw [map_neg]]
    rw [← map_mul]
    norm_num
  have ht : (formT : Form ℂ) ≠ 0 := by
    simpa only [formT] using
      (MvPolynomial.X_ne_zero (R := ℂ) (1 : Fin 2))
  have hfactor :
      (-9 : Form ℂ) * formT ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)
  refine ⟨inverseNine * A, ?_⟩
  apply mul_left_cancel₀ hfactor
  calc
    ((-9 : Form ℂ) * formT ^ 2) *
        eSourceCubeSubstitutionForm
            (eCharacteristicDerivation ℂ Rzero) =
        OnLeConjecture.Polynomial.jacobian (cubicForm 0 3)
          (eSourceCubeSubstitutionForm Rzero) :=
      (e_jacobian_sourceCubeSubstitutionForm Rzero).symm
    _ = formT ^ 5 * A := hA
    _ = ((-9 : Form ℂ) * formT ^ 2) *
        (formT ^ 3 * (inverseNine * A)) := by
      calc
        formT ^ 5 * A = 1 * (formT ^ 5 * A) := by ring
        _ = ((-9 : Form ℂ) * inverseNine) *
            (formT ^ 5 * A) := by rw [hscalar]
        _ = ((-9 : Form ℂ) * formT ^ 2) *
            (formT ^ 3 * (inverseNine * A)) := by ring

/-- The original `t^5` Jacobian divisibility condition descends to
`w | (partial_x - x^2 partial_w)(Rzero)`. -/
theorem eSourceW_dvd_characteristic_of_formT_five_dvd_jacobian
    (Rzero : ESourceRing ℂ)
    (hdiv :
      formT ^ 5 ∣
        OnLeConjecture.Polynomial.jacobian (cubicForm 0 3)
          (eSourceCubeSubstitutionForm Rzero)) :
    eSourceW ℂ ∣ eCharacteristicDerivation ℂ Rzero := by
  apply eSourceW_dvd_of_formT_cube_dvd_sourceCubeSubstitutionForm
  exact e_formT_cube_dvd_characteristic_of_formT_five_dvd_jacobian
    Rzero hdiv

/-- Substitute `omega t` for `t` in a homogeneous form, using the natural
iterated presentation. -/
@[expose]
noncomputable def eRotateForm (omega : ℂ) (R : Form ℂ) : Form ℂ :=
  eIteratedToForm (eRotateThirdVariable omega (eFormToIterated R))

theorem eFormToIterated_rotateForm (omega : ℂ) (R : Form ℂ) :
    eFormToIterated (eRotateForm omega R) =
      eRotateThirdVariable omega (eFormToIterated R) := by
  have h := AlgHom.congr_fun
    eFormToIterated_comp_iteratedToForm
      (eRotateThirdVariable omega (eFormToIterated R))
  simpa only [eRotateForm, AlgHom.comp_apply, AlgHom.id_apply] using h

@[simp]
theorem eRotateForm_x (omega : ℂ) :
    eRotateForm omega formX = formX := by
  apply (eFormEquivIterated).injective
  change eFormToIterated (eRotateForm omega formX) =
    eFormToIterated formX
  rw [eFormToIterated_rotateForm, eFormToIterated_x]
  simp [eRotateThirdVariable_eq]

@[simp]
theorem eRotateForm_t (omega : ℂ) :
    eRotateForm omega formT = MvPolynomial.C omega * formT := by
  apply (eFormEquivIterated).injective
  change eFormToIterated (eRotateForm omega formT) =
    eFormToIterated (MvPolynomial.C omega * formT)
  rw [eFormToIterated_rotateForm, eFormToIterated_t,
    map_mul, eFormToIterated_t]
  have hconstant :
      eFormToIterated (MvPolynomial.C omega) = C (C omega) :=
    (eFormToIterated).commutes omega
  rw [hconstant]
  simp [eRotateThirdVariable_eq]

/-- Invariance under `t -> omega t` and divisibility of the original
Jacobian by `t^5` produce a descended polynomial whose characteristic
derivative is divisible by `w`. -/
theorem exists_e_source_descent_of_rotationInvariant_and_jacobian_dvd
    {omega : ℂ} (R : Form ℂ)
    (homega : IsPrimitiveRoot omega 3)
    (hinvariant : R = eRotateForm omega R)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R) :
    ∃ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R ∧
        eSourceW ℂ ∣ eCharacteristicDerivation ℂ Rzero := by
  have hinvariantIterated :
      eFormToIterated R =
        eRotateThirdVariable omega (eFormToIterated R) := by
    calc
      eFormToIterated R = eFormToIterated (eRotateForm omega R) := by
        exact congrArg eFormToIterated hinvariant
      _ = eRotateThirdVariable omega (eFormToIterated R) :=
        eFormToIterated_rotateForm omega R
  obtain ⟨Rzero, hRzeroIterated⟩ :=
    exists_e_source_cube_descent_of_rotationInvariant
      (eFormToIterated R) homega hinvariantIterated
  have hRzeroForm : eSourceCubeSubstitutionForm Rzero = R := by
    apply (eFormEquivIterated).injective
    change eFormToIterated (eSourceCubeSubstitutionForm Rzero) =
      eFormToIterated R
    calc
      eFormToIterated (eSourceCubeSubstitutionForm Rzero) =
          eSourceCubeSubstitution Rzero :=
        AlgHom.congr_fun
          eFormToIterated_comp_sourceCubeSubstitutionForm Rzero
      _ = eFormToIterated R := hRzeroIterated
  refine ⟨Rzero, hRzeroForm, ?_⟩
  apply eSourceW_dvd_characteristic_of_formT_five_dvd_jacobian
  rwa [hRzeroForm]

/-- The invariant Jacobian hypotheses produce canonical basis coefficients
whose residual difference polynomial contains the square of the diagonal. -/
theorem exists_e_theta_diagonal_square_of_rotationInvariant_and_jacobian_dvd
    {omega : ℂ} (R : Form ℂ)
    (homega : IsPrimitiveRoot omega 3)
    (hinvariant : R = eRotateForm omega R)
    (hdiv : formT ^ 5 ∣
      OnLeConjecture.Polynomial.jacobian (cubicForm 0 3) R) :
    ∃ Rzero : ESourceRing ℂ, ∃ c : Fin 4 → EBaseRing ℂ,
      eSourceCubeSubstitutionForm Rzero = R ∧
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ) ∧
      ePairDiagonal ℂ ^ 2 ∣ eThetaPolynomial ℂ c := by
  obtain ⟨Rzero, hRzero, hcharacteristic⟩ :=
    exists_e_source_descent_of_rotationInvariant_and_jacobian_dvd
      R homega hinvariant hdiv
  obtain ⟨c, hdecomposition, _hunique⟩ :=
    e_source_basis_decomposition_unique ℂ Rzero
  refine ⟨Rzero, c, hRzero, hdecomposition, ?_⟩
  exact ePairDiagonal_sq_dvd_thetaPolynomial_of_basis_and_w_dvd
    ℂ Rzero c hdecomposition hcharacteristic

end OnLeConjecture.DThree
