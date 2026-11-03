/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ENoninvariantRotation
public import OnLeConjecture.DThree.HJacobianDescent

/-!
# The reflection difference for the H pair

The first two forms in the H case are invariant under `t` replaced by `-t`.
A homogeneous third form either has a reflection line collision away from
`[1:0]` or is the sum of a polynomial in `x,t^2` and a nonzero odd power of
`t`.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Reflection invariance forces every exponent of the second variable to be
even. -/
theorem two_dvd_exponent_of_h_reflectionInvariant
    {omega : ℂ} (R : EIteratedSourceRing)
    (homega : IsPrimitiveRoot omega 2)
    (hinvariant : R = eRotateThirdVariable omega R)
    {h : ℕ} (hcoeff : R.coeff h ≠ 0) :
    2 ∣ h := by
  have hsector :
      R = C (C (omega ^ 0)) *
        OnLeConjecture.DTwo.rotateSecondVariable (omega ^ 1) R := by
    simpa only [pow_zero, pow_one, map_one, one_mul,
      eRotateThirdVariable_eq,
      OnLeConjecture.DTwo.rotateSecondVariable_eq] using hinvariant
  have hdiv := OnLeConjecture.DTwo.dvd_character_of_sectorIdentity
    R homega hsector hcoeff
  simpa using hdiv

/-- Divide every exponent of the second variable by two. -/
noncomputable def hSquareDescent (R : EIteratedSourceRing) :
    HIteratedWeightedRing ℂ :=
  OnLeConjecture.DTwo.descendSector 2 0 1 R

/-- Substitution of the square of the outer variable recovers a polynomial
whose nonzero exponents are even. -/
theorem hSquareDescent_eval₂
    (R : EIteratedSourceRing)
    (hdiv : ∀ h : ℕ, R.coeff h ≠ 0 → 2 ∣ h) :
    (hSquareDescent R).eval₂ C (X ^ 2) = R := by
  have hdiv' : ∀ h : ℕ, R.coeff h ≠ 0 → 2 ∣ 0 + 1 * h := by
    intro h hcoeff
    simpa using hdiv h hcoeff
  simpa [hSquareDescent] using
    (OnLeConjecture.DTwo.eval₂_descendSector
      (k := 2) (e := 0) (L := 1) R hdiv')

/-- Evaluation of the outer variable at its square. -/
@[expose]
noncomputable def hIteratedSquareEvaluation :
    HIteratedWeightedRing ℂ →ₐ[ℂ] EIteratedSourceRing :=
  Polynomial.eval₂AlgHom Polynomial.CAlgHom (X ^ 2)
    fun _ ↦ Commute.all _ _

/-- Passing through the weighted polynomial ring and substituting `w=t^2`
agrees with square evaluation in the iterated presentation. -/
theorem hQuadraticSubstitution_iteratedToWeightedForm
    (S : HIteratedWeightedRing ℂ) :
    hQuadraticSubstitutionForm (hIteratedToWeightedForm S) =
      eIteratedToForm (hIteratedSquareEvaluation S) := by
  have hmaps :
      hQuadraticSubstitutionForm.comp hIteratedToWeightedForm =
        eIteratedToForm.comp hIteratedSquareEvaluation := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      change hQuadraticSubstitutionForm
          (hIteratedToWeightedForm (C X)) =
        eIteratedToForm (hIteratedSquareEvaluation (C X))
      rw [hIteratedToWeightedForm_innerX,
        hQuadraticSubstitutionForm_x]
      simp [hIteratedSquareEvaluation]
    · change hQuadraticSubstitutionForm
          (hIteratedToWeightedForm X) =
        eIteratedToForm (hIteratedSquareEvaluation X)
      rw [hIteratedToWeightedForm_outerX,
        hQuadraticSubstitutionForm_w]
      simp [hIteratedSquareEvaluation]
  exact AlgHom.congr_fun hmaps S

/-- A polynomial invariant under a primitive square root of unity descends
to a weighted polynomial in `x,w`, with `w=t^2`. -/
theorem exists_h_weighted_descent_of_reflectionInvariant
    {omega : ℂ} (R : Form ℂ)
    (homega : IsPrimitiveRoot omega 2)
    (hinvariant : R = eRotateForm omega R) :
    ∃ Rzero : MvPolynomial (Fin 2) ℂ,
      hQuadraticSubstitutionForm Rzero = R := by
  have hiteratedInvariant :
      eFormToIterated R =
        eRotateThirdVariable omega (eFormToIterated R) := by
    calc
      eFormToIterated R = eFormToIterated (eRotateForm omega R) := by
        exact congrArg eFormToIterated hinvariant
      _ = eRotateThirdVariable omega (eFormToIterated R) :=
        eFormToIterated_rotateForm omega R
  let S := hSquareDescent (eFormToIterated R)
  have hS : S.eval₂ C (X ^ 2) = eFormToIterated R := by
    apply hSquareDescent_eval₂
    intro h hcoeff
    exact two_dvd_exponent_of_h_reflectionInvariant
      (eFormToIterated R) homega hiteratedInvariant hcoeff
  refine ⟨hIteratedToWeightedForm S, ?_⟩
  rw [hQuadraticSubstitution_iteratedToWeightedForm]
  change eIteratedToForm (S.eval₂ C (X ^ 2)) = R
  rw [hS]
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
    AlgHom.congr_fun eIteratedToForm_comp_formToIterated R

/-- A pure power reflection difference has odd exponent. -/
theorem two_not_dvd_of_hRotationDifference_eq_scalar_mul_formT_pow
    {omega coefficient : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 2)
    (hcoefficient : coefficient ≠ 0)
    (hdifference : eRotationDifference omega R =
      MvPolynomial.C coefficient * formT ^ N) :
    ¬ 2 ∣ N := by
  intro hdiv
  have homegaPower : omega ^ N = 1 :=
    (homega.pow_eq_one_iff_dvd N).mpr hdiv
  have hiterated := congrArg eFormToIterated hdifference
  have hcoefficientIdentity := congrArg
    (fun S : EIteratedSourceRing ↦ S.coeff N) hiterated
  simp only [eRotationDifference, map_sub,
    eFormToIterated_rotateForm, eRotateThirdVariable_eq,
    Polynomial.coeff_sub, Polynomial.comp_C_mul_X_coeff,
    map_mul, map_pow, eFormToIterated_t] at hcoefficientIdentity
  have hmapConstant :
      eFormToIterated (MvPolynomial.C coefficient) = C (C coefficient) :=
    eFormToIterated.commutes coefficient
  rw [hmapConstant, Polynomial.coeff_C_mul_X_pow, if_pos rfl,
    ← map_pow, homegaPower, map_one] at hcoefficientIdentity
  simp only [mul_one, sub_self] at hcoefficientIdentity
  have hconstant : (C coefficient : Polynomial ℂ) = 0 :=
    hcoefficientIdentity.symm
  apply hcoefficient
  apply Polynomial.C_injective
  simpa using hconstant

/-- If a reflection difference is supported at `[1:0]`, the form is an even
form plus one nonzero odd pure power. -/
theorem exists_h_weighted_descent_add_odd_power_of_projective_support
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 2)
    (hhomogeneous : R.IsHomogeneous N)
    (hsupport : EFormProjectiveZerosAtFirstCoordinate
      (eRotationDifference omega R)) :
    ∃ Rzero : MvPolynomial (Fin 2) ℂ, ∃ coefficient : ℂ,
      coefficient ≠ 0 ∧ ¬ 2 ∣ N ∧
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N := by
  obtain ⟨differenceCoefficient, hdifferenceCoefficient, hdifference⟩ :=
    eRotationDifference_eq_nonzero_scalar_mul_formT_pow
      omega hhomogeneous hsupport
  have hnotdiv : ¬ 2 ∣ N :=
    two_not_dvd_of_hRotationDifference_eq_scalar_mul_formT_pow
      homega hdifferenceCoefficient hdifference
  have homegaPowerNe : omega ^ N ≠ 1 :=
    (homega.pow_eq_one_iff_dvd N).not.mpr hnotdiv
  have hdenominator : (1 : ℂ) - omega ^ N ≠ 0 :=
    sub_ne_zero.mpr homegaPowerNe.symm
  let coefficient := differenceCoefficient / (1 - omega ^ N)
  have hcoefficient : coefficient ≠ 0 :=
    div_ne_zero hdifferenceCoefficient hdenominator
  have hcoefficientIdentity :
      coefficient * (1 - omega ^ N) = differenceCoefficient :=
    div_mul_cancel₀ differenceCoefficient hdenominator
  let remainder := R - MvPolynomial.C coefficient * formT ^ N
  have hremainderDifference : eRotationDifference omega remainder = 0 := by
    change eRotationDifference omega
      (R - MvPolynomial.C coefficient * formT ^ N) = 0
    rw [eRotationDifference_sub, hdifference,
      eRotationDifference_scalar_mul_formT_pow,
      hcoefficientIdentity, sub_self]
  have hremainderInvariant : remainder = eRotateForm omega remainder :=
    sub_eq_zero.mp hremainderDifference
  obtain ⟨Rzero, hRzero⟩ :=
    exists_h_weighted_descent_of_reflectionInvariant
      remainder homega hremainderInvariant
  refine ⟨Rzero, coefficient, hcoefficient, hnotdiv, ?_⟩
  rw [hRzero]
  change R =
    (R - MvPolynomial.C coefficient * formT ^ N) +
      MvPolynomial.C coefficient * formT ^ N
  ring

/-- A homogeneous form has a reflection zero away from `[1:0]` or has the
even form plus odd power decomposition. -/
theorem exists_h_reflection_zero_away_first_or_weighted_descent_add_odd_power
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 2)
    (hhomogeneous : R.IsHomogeneous N) :
    (∃ x t : ℂ, (x ≠ 0 ∨ t ≠ 0) ∧
      MvPolynomial.eval ![x, t] (eRotationDifference omega R) = 0 ∧
      t ≠ 0) ∨
    ∃ Rzero : MvPolynomial (Fin 2) ℂ, ∃ coefficient : ℂ,
      coefficient ≠ 0 ∧ ¬ 2 ∣ N ∧
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N := by
  by_cases hsupport : EFormProjectiveZerosAtFirstCoordinate
      (eRotationDifference omega R)
  · right
    exact exists_h_weighted_descent_add_odd_power_of_projective_support
      homega hhomogeneous hsupport
  · left
    by_contra hnone
    apply hsupport
    rw [EFormProjectiveZerosAtFirstCoordinate]
    intro x t hnonzero hzero
    by_contra ht
    apply hnone
    exact ⟨x, t, hnonzero, hzero, ht⟩

/-- Data for a collision on the reflection line of the H pair. -/
structure HReflectionLineCollisionCertificate (R : Form ℂ) where
  x : ℂ
  t : ℂ
  t_ne_zero : t ≠ 0
  reflectionDifference_ne_zero : eRotationDifference (-1) R ≠ 0
  sourcePoints_ne : ((x, t) : ℂ × ℂ) ≠ (x, -t)
  cubicValues_eq :
    MvPolynomial.eval ![x, t] (cubicForm 3 0) =
      MvPolynomial.eval ![x, -t] (cubicForm 3 0)
  quarticValues_eq :
    MvPolynomial.eval ![x, t] (quarticForm 1 0 4 0 2) =
      MvPolynomial.eval ![x, -t] (quarticForm 1 0 4 0 2)
  thirdValues_eq :
    MvPolynomial.eval ![x, t] R =
      MvPolynomial.eval ![x, -t] R

/-- A nonzero reflection zero with nonzero second coordinate gives a
reflection line collision certificate. -/
theorem exists_hReflectionLineCollisionCertificate_of_reflection_zero
    {R : Form ℂ} {x t : ℂ}
    (ht : t ≠ 0)
    (hdifferenceNe : eRotationDifference (-1) R ≠ 0)
    (hzero : MvPolynomial.eval ![x, t]
      (eRotationDifference (-1) R) = 0) :
    Nonempty (HReflectionLineCollisionCertificate R) := by
  have hsource : ((x, t) : ℂ × ℂ) ≠ (x, -t) := by
    intro heq
    have hsecond : t = -t := congrArg Prod.snd heq
    have htwo : (2 : ℂ) * t = 0 := by
      calc
        (2 : ℂ) * t = t - (-t) := by ring
        _ = 0 := sub_eq_zero.mpr hsecond
    exact ht ((mul_eq_zero.mp htwo).resolve_left (by norm_num))
  have hcubic :
      MvPolynomial.eval ![x, t] (cubicForm 3 0) =
        MvPolynomial.eval ![x, -t] (cubicForm 3 0) := by
    simp [cubicForm, formX, formT]
  have hquartic :
      MvPolynomial.eval ![x, t] (quarticForm 1 0 4 0 2) =
        MvPolynomial.eval ![x, -t] (quarticForm 1 0 4 0 2) := by
    simp [quarticForm, formX, formT]
    ring
  have hthird :
      MvPolynomial.eval ![x, t] R =
        MvPolynomial.eval ![x, -t] R := by
    rw [eRotationDifference] at hzero
    simp only [map_sub, eRotateForm_eval] at hzero
    norm_num at hzero
    exact sub_eq_zero.mp hzero
  exact ⟨{
    x := x
    t := t
    t_ne_zero := ht
    reflectionDifference_ne_zero := hdifferenceNe
    sourcePoints_ne := hsource
    cubicValues_eq := hcubic
    quarticValues_eq := hquartic
    thirdValues_eq := hthird
  }⟩

/-- A noninvariant homogeneous H form either has a reflection line collision
or has the even form plus odd power decomposition. -/
theorem h_noninvariant_reflectionLineCollision_or_weighted_descent_add_odd_power
    {R : Form ℂ} {N : ℕ}
    (hhomogeneous : R.IsHomogeneous N)
    (hnoninvariant : R ≠ eRotateForm (-1) R) :
    Nonempty (HReflectionLineCollisionCertificate R) ∨
    ∃ Rzero : MvPolynomial (Fin 2) ℂ, ∃ coefficient : ℂ,
      coefficient ≠ 0 ∧ ¬ 2 ∣ N ∧
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N := by
  have homega : IsPrimitiveRoot (-1 : ℂ) 2 := by
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hdifferenceNe : eRotationDifference (-1) R ≠ 0 := by
    intro hzero
    apply hnoninvariant
    exact sub_eq_zero.mp hzero
  rcases
      exists_h_reflection_zero_away_first_or_weighted_descent_add_odd_power
        homega hhomogeneous with hreflection | hpower
  · left
    obtain ⟨x, t, _, hzero, ht⟩ := hreflection
    exact exists_hReflectionLineCollisionCertificate_of_reflection_zero
      ht hdifferenceNe hzero
  · exact Or.inr hpower

end OnLeConjecture.DThree
