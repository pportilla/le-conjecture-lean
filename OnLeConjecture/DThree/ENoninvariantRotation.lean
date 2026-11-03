/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EThetaHomogeneous

/-!
# The noninvariant rotation difference for the `E` pair

This file isolates the algebraic reduction in the noninvariant branch of
the degree three argument.  If the homogeneous rotation difference has no
projective zero except `[1:0]`, then it is a nonzero scalar multiple of a
power of `t`.  The original form is consequently the sum of a polynomial in
`x,t^3` and a nonzero pure power of `t` whose exponent is not divisible by
three.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Every projective zero of a binary form is represented by a point whose
second coordinate is zero. -/
@[expose]
def EFormProjectiveZerosAtFirstCoordinate (F : Form ℂ) : Prop :=
  ∀ x t : ℂ, x ≠ 0 ∨ t ≠ 0 →
    MvPolynomial.eval ![x, t] F = 0 → t = 0

/-- The linear involution `(x,t) ↦ (x,x - t)` sends `[1:0]` to the
diagonal. -/
noncomputable def eFirstCoordinateToDiagonal : Form ℂ →ₐ[ℂ] Form ℂ :=
  MvPolynomial.aeval ![formX, formX - formT]

@[simp]
theorem eFirstCoordinateToDiagonal_x :
    eFirstCoordinateToDiagonal formX = formX := by
  simp [eFirstCoordinateToDiagonal, formX]

@[simp]
theorem eFirstCoordinateToDiagonal_t :
    eFirstCoordinateToDiagonal formT = formX - formT := by
  simp [eFirstCoordinateToDiagonal, formT]

theorem eFirstCoordinateToDiagonal_comp_self :
    eFirstCoordinateToDiagonal.comp eFirstCoordinateToDiagonal =
      AlgHom.id ℂ (Form ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change eFirstCoordinateToDiagonal
      (eFirstCoordinateToDiagonal formX) = formX
    rw [eFirstCoordinateToDiagonal_x, eFirstCoordinateToDiagonal_x]
  · change eFirstCoordinateToDiagonal
      (eFirstCoordinateToDiagonal formT) = formT
    rw [eFirstCoordinateToDiagonal_t, map_sub,
      eFirstCoordinateToDiagonal_x, eFirstCoordinateToDiagonal_t]
    ring

theorem eFirstCoordinateToDiagonal_isHomogeneous
    {F : Form ℂ} {N : ℕ} (hF : F.IsHomogeneous N) :
    (eFirstCoordinateToDiagonal F).IsHomogeneous N := by
  rw [eFirstCoordinateToDiagonal, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq]
  apply isHomogeneous_eval₂_of_isWeightedHomogeneous
    (1 : Fin 2 → ℕ) hF
  intro i
  fin_cases i
  · exact MvPolynomial.isHomogeneous_X ℂ 0
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).sub
      (MvPolynomial.isHomogeneous_X ℂ 1)

theorem eFirstCoordinateToDiagonal_eval
    (F : Form ℂ) (x t : ℂ) :
    MvPolynomial.eval ![x, t] (eFirstCoordinateToDiagonal F) =
      MvPolynomial.eval ![x, x - t] F := by
  change MvPolynomial.aeval ![x, t]
      (MvPolynomial.aeval ![formX, formX - formT] F) =
    MvPolynomial.aeval ![x, x - t] F
  rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_bind₁]
  congr
  funext i
  fin_cases i
  all_goals simp [formX, formT]

private theorem e_eval_homogenize_one_zero
    (p : Polynomial ℂ) (N : ℕ) :
    MvPolynomial.eval ![(1 : ℂ), 0] (p.homogenize N) = p.coeff N := by
  simp only [Polynomial.homogenize, map_sum,
    MvPolynomial.eval_monomial]
  rw [Finset.sum_eq_single (N, 0)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    have hsum : a + b = N := Finset.mem_antidiagonal.mp hab
    have hb : b ≠ 0 := by
      intro hb
      apply hne
      subst b
      simp only [add_zero] at hsum
      exact Prod.ext hsum rfl
    simp [hb]
  · simp

private theorem e_polynomial_eq_leadingCoeff_mul_X_sub_one_pow
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (hroot : ∀ z : ℂ, p.eval z = 0 → z = 1) :
    p = C p.leadingCoeff * (X - C 1) ^ p.natDegree := by
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroots : p.roots = Multiset.replicate p.natDegree 1 := by
    apply Multiset.eq_replicate.mpr
    constructor
    · exact IsAlgClosed.card_roots_eq_natDegree
    · intro z hz
      apply hroot z
      exact (Polynomial.mem_roots hp).mp hz
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
      hsplits.eq_prod_roots
    _ = C p.leadingCoeff * (X - C 1) ^ p.natDegree := by
      rw [hroots, Multiset.map_replicate, Multiset.prod_replicate]

/-- A nonzero homogeneous binary form supported at `[1:0]` is a scalar
multiple of the corresponding power of `t`. -/
theorem eq_nonzero_scalar_mul_formT_pow_of_projective_support
    {F : Form ℂ} {N : ℕ}
    (hhomogeneous : F.IsHomogeneous N)
    (hsupport : EFormProjectiveZerosAtFirstCoordinate F) :
    ∃ coefficient : ℂ, coefficient ≠ 0 ∧
      F = MvPolynomial.C coefficient * formT ^ N := by
  let changed := eFirstCoordinateToDiagonal F
  let theta : EPairRing ℂ := eFormToIterated changed
  have hchanged : changed.IsHomogeneous N :=
    eFirstCoordinateToDiagonal_isHomogeneous hhomogeneous
  have hthetaHomogeneous : EPairIsHomogeneous theta N := by
    apply (ePairIsHomogeneous_iff theta N).mpr
    dsimp only [theta]
    have hback : eIteratedToForm (eFormToIterated changed) = changed := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        AlgHom.congr_fun eIteratedToForm_comp_formToIterated changed
    rwa [hback]
  let p := ePairDehomogenize theta
  have hroot : ∀ z : ℂ, p.eval z = 0 → z = 1 := by
    intro z hzero
    have hback : eIteratedToForm theta = changed := by
      change eIteratedToForm (eFormToIterated changed) = changed
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        AlgHom.congr_fun eIteratedToForm_comp_formToIterated changed
    have hchangedZero : MvPolynomial.eval ![z, 1] changed = 0 := by
      rw [← hback, ← ePairDehomogenize_eval]
      exact hzero
    have hsourceNonzero : z ≠ 0 ∨ z - 1 ≠ 0 := by
      by_contra hnone
      simp only [not_or, not_ne_iff] at hnone
      have hfalse := hnone.2
      rw [hnone.1] at hfalse
      norm_num at hfalse
    have hsourceZero : MvPolynomial.eval ![z, z - 1] F = 0 := by
      rw [← eFirstCoordinateToDiagonal_eval]
      exact hchangedZero
    have hdifference := hsupport z (z - 1) hsourceNonzero hsourceZero
    exact sub_eq_zero.mp hdifference
  have hp : p ≠ 0 := by
    intro hpzero
    have hzero : p.eval 0 = 0 := by rw [hpzero, Polynomial.eval_zero]
    have := hroot 0 hzero
    norm_num at this
  have hdegree : p.natDegree = N := by
    apply le_antisymm (ePairDehomogenize_natDegree_le hthetaHomogeneous)
    by_contra hle
    have hlt : p.natDegree < N := Nat.lt_of_not_ge hle
    have hcoeff : p.coeff N = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    have hthetaZero :
        MvPolynomial.eval ![(1 : ℂ), 0] (eIteratedToForm theta) = 0 := by
      rw [← ePair_homogenize_dehomogenize hthetaHomogeneous,
        e_eval_homogenize_one_zero, hcoeff]
    have hback : eIteratedToForm theta = changed := by
      change eIteratedToForm (eFormToIterated changed) = changed
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        AlgHom.congr_fun eIteratedToForm_comp_formToIterated changed
    have hchangedZero :
        MvPolynomial.eval ![(1 : ℂ), 0] changed = 0 := by
      rwa [hback] at hthetaZero
    have hsourceZero :
        MvPolynomial.eval ![(1 : ℂ), 1] F = 0 := by
      calc
        MvPolynomial.eval ![(1 : ℂ), 1] F =
            MvPolynomial.eval ![(1 : ℂ), 0] changed := by
          simpa using (eFirstCoordinateToDiagonal_eval F 1 0).symm
        _ = 0 := hchangedZero
    have hone := hsupport 1 1 (Or.inl one_ne_zero) hsourceZero
    exact one_ne_zero hone
  have hpFactor : p = C p.leadingCoeff * (X - C 1) ^ N := by
    rw [← hdegree]
    exact e_polynomial_eq_leadingCoeff_mul_X_sub_one_pow p hp hroot
  let diagonalForm : Form ℂ := formX - formT
  have hdiagonalHomogeneous : diagonalForm.IsHomogeneous 1 := by
    exact (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).sub
      (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2))
  have hpowerHomogeneous :
      (MvPolynomial.C p.leadingCoeff * diagonalForm ^ N).IsHomogeneous N := by
    simpa only [one_mul] using
      (hdiagonalHomogeneous.pow N).C_mul p.leadingCoeff
  have hdehomogenizePower :
      MvPolynomial.aeval ![X, 1]
          (MvPolynomial.C p.leadingCoeff * diagonalForm ^ N) = p := by
    calc
      MvPolynomial.aeval ![X, 1]
          (MvPolynomial.C p.leadingCoeff * diagonalForm ^ N) =
          C p.leadingCoeff * (X - C 1) ^ N := by
        simp [diagonalForm, formX, formT]
      _ = p := hpFactor.symm
  have hformPower :
      p.homogenize N =
        MvPolynomial.C p.leadingCoeff * diagonalForm ^ N :=
    Polynomial.homogenize_eq_of_isHomogeneous
      hpowerHomogeneous hdehomogenizePower
  have hthetaForm :
      eIteratedToForm theta =
        MvPolynomial.C p.leadingCoeff * diagonalForm ^ N := by
    rw [← ePair_homogenize_dehomogenize hthetaHomogeneous, hformPower]
  let coefficient := p.leadingCoeff
  have hcoefficient : coefficient ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hp
  have htheta :
      theta = algebraMap ℂ (EPairRing ℂ) coefficient *
        (ePairFirst ℂ - ePairSecond ℂ) ^ N := by
    have htransport := congrArg eFormToIterated hthetaForm
    have hback : eFormToIterated (eIteratedToForm theta) = theta := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        AlgHom.congr_fun eFormToIterated_comp_iteratedToForm theta
    rw [hback] at htransport
    have hconstant :
        eFormToIterated (MvPolynomial.C coefficient) =
          algebraMap ℂ (EPairRing ℂ) coefficient :=
      eFormToIterated.commutes coefficient
    simp only [map_mul, map_pow, map_sub, diagonalForm] at htransport
    rw [hconstant, eFormToIterated_x, eFormToIterated_t] at htransport
    simpa only [ePairFirst, ePairSecond] using htransport
  have hchangedPower :
      changed = MvPolynomial.C coefficient * (formX - formT) ^ N := by
    have htransport := congrArg eIteratedToForm htheta
    have hback : eIteratedToForm theta = changed := by
      change eIteratedToForm (eFormToIterated changed) = changed
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        AlgHom.congr_fun eIteratedToForm_comp_formToIterated changed
    rw [hback] at htransport
    have hconstant :
        eIteratedToForm
            (algebraMap ℂ (EPairRing ℂ) coefficient) =
          MvPolynomial.C coefficient :=
      eIteratedToForm.commutes coefficient
    simp only [map_mul, map_pow, map_sub] at htransport
    rw [hconstant,
      show ePairFirst ℂ = C X by rfl,
      show ePairSecond ℂ = X by rfl,
      eIteratedToForm_innerX, eIteratedToForm_outerX] at htransport
    exact htransport
  refine ⟨coefficient, hcoefficient, ?_⟩
  have hrecover := congrArg eFirstCoordinateToDiagonal hchangedPower
  have hself : eFirstCoordinateToDiagonal changed = F := by
    change eFirstCoordinateToDiagonal
      (eFirstCoordinateToDiagonal F) = F
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
      AlgHom.congr_fun eFirstCoordinateToDiagonal_comp_self F
  rw [hself] at hrecover
  have hconstant :
      eFirstCoordinateToDiagonal (MvPolynomial.C coefficient) =
        MvPolynomial.C coefficient :=
    eFirstCoordinateToDiagonal.commutes coefficient
  simp only [map_mul, map_pow, map_sub,
    eFirstCoordinateToDiagonal_x, eFirstCoordinateToDiagonal_t,
    hconstant] at hrecover
  simpa only [sub_sub_cancel] using hrecover

/-- Substitution of `omega t` for the outer variable as an algebra
homomorphism of the iterated presentation. -/
noncomputable def eRotateThirdVariableAlgHom (omega : ℂ) :
    EIteratedSourceRing →ₐ[ℂ] EIteratedSourceRing where
  toFun S := S.comp (C (C omega) * X)
  map_one' := by simp
  map_mul' S T := by simp
  map_zero' := by simp
  map_add' S T := by simp
  commutes' c := by simp

/-- The rotation algebra homomorphism transported to homogeneous forms. -/
noncomputable def eRotateFormThroughIterated (omega : ℂ) :
    Form ℂ →ₐ[ℂ] Form ℂ :=
  eIteratedToForm.comp
    ((eRotateThirdVariableAlgHom omega).comp eFormToIterated)

theorem eRotateFormThroughIterated_apply (omega : ℂ) (R : Form ℂ) :
    eRotateFormThroughIterated omega R = eRotateForm omega R := by
  simp only [eRotateFormThroughIterated, AlgHom.comp_apply,
    eRotateThirdVariableAlgHom, eRotateForm]
  rw [eRotateThirdVariable_eq]
  rfl

/-- The rotation of a form is evaluation at `(x,omega t)`. -/
noncomputable def eRotateFormAlgHom (omega : ℂ) :
    Form ℂ →ₐ[ℂ] Form ℂ :=
  MvPolynomial.aeval ![formX, MvPolynomial.C omega * formT]

theorem eRotateFormAlgHom_eq_throughIterated (omega : ℂ) :
    eRotateFormAlgHom omega = eRotateFormThroughIterated omega := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change eRotateFormAlgHom omega formX =
      eRotateFormThroughIterated omega formX
    rw [eRotateFormThroughIterated_apply, eRotateForm_x]
    simp [eRotateFormAlgHom, formX]
  · change eRotateFormAlgHom omega formT =
      eRotateFormThroughIterated omega formT
    rw [eRotateFormThroughIterated_apply, eRotateForm_t]
    simp [eRotateFormAlgHom, formT]

theorem eRotateFormAlgHom_apply (omega : ℂ) (R : Form ℂ) :
    eRotateFormAlgHom omega R = eRotateForm omega R := by
  rw [eRotateFormAlgHom_eq_throughIterated,
    eRotateFormThroughIterated_apply]

/-- Rotation of the second coordinate preserves ordinary homogeneity. -/
theorem eRotateForm_isHomogeneous
    (omega : ℂ) {R : Form ℂ} {N : ℕ}
    (hR : R.IsHomogeneous N) :
    (eRotateForm omega R).IsHomogeneous N := by
  rw [← eRotateFormAlgHom_apply]
  rw [eRotateFormAlgHom, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq]
  apply isHomogeneous_eval₂_of_isWeightedHomogeneous
    (1 : Fin 2 → ℕ) hR
  intro i
  fin_cases i
  · exact MvPolynomial.isHomogeneous_X ℂ 0
  · exact (MvPolynomial.isHomogeneous_X ℂ 1).C_mul omega

/-- The difference between a form and its rotation. -/
@[expose]
noncomputable def eRotationDifference
    (omega : ℂ) (R : Form ℂ) : Form ℂ :=
  R - eRotateForm omega R

/-- The rotation difference of a homogeneous form is homogeneous of the
same degree. -/
theorem eRotationDifference_isHomogeneous
    (omega : ℂ) {R : Form ℂ} {N : ℕ}
    (hR : R.IsHomogeneous N) :
    (eRotationDifference omega R).IsHomogeneous N := by
  exact hR.sub (eRotateForm_isHomogeneous omega hR)

/-- If the nonzero rotation difference is supported at `[1:0]`, it is a
nonzero scalar multiple of `t^N`. -/
theorem eRotationDifference_eq_nonzero_scalar_mul_formT_pow
    (omega : ℂ) {R : Form ℂ} {N : ℕ}
    (hhomogeneous : R.IsHomogeneous N)
    (hsupport : EFormProjectiveZerosAtFirstCoordinate
      (eRotationDifference omega R)) :
    ∃ coefficient : ℂ, coefficient ≠ 0 ∧
      eRotationDifference omega R =
        MvPolynomial.C coefficient * formT ^ N := by
  exact eq_nonzero_scalar_mul_formT_pow_of_projective_support
    (eRotationDifference_isHomogeneous omega hhomogeneous) hsupport

/-- A nonzero pure power rotation difference cannot have exponent divisible
by three. -/
theorem three_not_dvd_of_eRotationDifference_eq_scalar_mul_formT_pow
    {omega coefficient : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 3)
    (hcoefficient : coefficient ≠ 0)
    (hdifference : eRotationDifference omega R =
      MvPolynomial.C coefficient * formT ^ N) :
    ¬ 3 ∣ N := by
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
  have hconstant : (C coefficient : Polynomial ℂ) = 0 := by
    exact hcoefficientIdentity.symm
  apply hcoefficient
  apply Polynomial.C_injective
  simpa using hconstant

theorem eRotateForm_scalar_mul_formT_pow
    (omega coefficient : ℂ) (N : ℕ) :
    eRotateForm omega (MvPolynomial.C coefficient * formT ^ N) =
      MvPolynomial.C (coefficient * omega ^ N) * formT ^ N := by
  calc
    eRotateForm omega (MvPolynomial.C coefficient * formT ^ N) =
        eRotateFormThroughIterated omega
          (MvPolynomial.C coefficient * formT ^ N) :=
      (eRotateFormThroughIterated_apply omega _).symm
    _ = MvPolynomial.C coefficient *
        (eRotateFormThroughIterated omega formT) ^ N := by
      rw [map_mul, map_pow]
      have hconstant :=
        (eRotateFormThroughIterated omega).commutes coefficient
      rw [show eRotateFormThroughIterated omega
          (MvPolynomial.C coefficient) = MvPolynomial.C coefficient by
        simpa only [MvPolynomial.algebraMap_eq] using hconstant]
    _ = MvPolynomial.C coefficient *
        (MvPolynomial.C omega * formT) ^ N := by
      rw [eRotateFormThroughIterated_apply, eRotateForm_t]
    _ = MvPolynomial.C (coefficient * omega ^ N) * formT ^ N := by
      rw [mul_pow, ← map_pow, ← mul_assoc, ← MvPolynomial.C_mul]

theorem eRotationDifference_scalar_mul_formT_pow
    (omega coefficient : ℂ) (N : ℕ) :
    eRotationDifference omega
        (MvPolynomial.C coefficient * formT ^ N) =
      MvPolynomial.C (coefficient * (1 - omega ^ N)) * formT ^ N := by
  rw [eRotationDifference, eRotateForm_scalar_mul_formT_pow]
  simp only [map_mul, map_sub, map_one]
  ring

theorem eRotationDifference_sub
    (omega : ℂ) (R S : Form ℂ) :
    eRotationDifference omega (R - S) =
      eRotationDifference omega R - eRotationDifference omega S := by
  have hrotationSub :
      eRotateForm omega (R - S) =
        eRotateForm omega R - eRotateForm omega S := by
    calc
      eRotateForm omega (R - S) =
          eRotateFormThroughIterated omega (R - S) :=
        (eRotateFormThroughIterated_apply omega _).symm
      _ = eRotateFormThroughIterated omega R -
          eRotateFormThroughIterated omega S := map_sub _ _ _
      _ = eRotateForm omega R - eRotateForm omega S := by
        rw [eRotateFormThroughIterated_apply,
          eRotateFormThroughIterated_apply]
  rw [eRotationDifference, hrotationSub]
  simp only [eRotationDifference]
  ring

/-- In the branch where the rotation difference is supported at `[1:0]`,
the form is the sum of a cubic invariant form and one nonzero pure power.
The exponent of the pure power is not divisible by three. -/
theorem exists_e_source_descent_add_pure_power_of_projective_support
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 3)
    (hhomogeneous : R.IsHomogeneous N)
    (hsupport : EFormProjectiveZerosAtFirstCoordinate
      (eRotationDifference omega R)) :
    ∃ Rzero : ESourceRing ℂ, ∃ coefficient : ℂ,
      coefficient ≠ 0 ∧ ¬ 3 ∣ N ∧
      R = eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N := by
  obtain ⟨differenceCoefficient, hdifferenceCoefficient, hdifference⟩ :=
    eRotationDifference_eq_nonzero_scalar_mul_formT_pow
      omega hhomogeneous hsupport
  have hnotdiv : ¬ 3 ∣ N :=
    three_not_dvd_of_eRotationDifference_eq_scalar_mul_formT_pow
      homega hdifferenceCoefficient hdifference
  have homegaPowerNe : omega ^ N ≠ 1 := by
    exact (homega.pow_eq_one_iff_dvd N).not.mpr hnotdiv
  have hdenominator : (1 : ℂ) - omega ^ N ≠ 0 :=
    sub_ne_zero.mpr homegaPowerNe.symm
  let coefficient := differenceCoefficient / (1 - omega ^ N)
  have hcoefficient : coefficient ≠ 0 :=
    div_ne_zero hdifferenceCoefficient hdenominator
  have hcoefficientIdentity :
      coefficient * (1 - omega ^ N) = differenceCoefficient := by
    exact div_mul_cancel₀ differenceCoefficient hdenominator
  let remainder := R - MvPolynomial.C coefficient * formT ^ N
  have hremainderDifference : eRotationDifference omega remainder = 0 := by
    change eRotationDifference omega
      (R - MvPolynomial.C coefficient * formT ^ N) = 0
    rw [eRotationDifference_sub, hdifference,
      eRotationDifference_scalar_mul_formT_pow,
      hcoefficientIdentity, sub_self]
  have hremainderInvariant :
      remainder = eRotateForm omega remainder := by
    exact sub_eq_zero.mp hremainderDifference
  have hremainderInvariantIterated :
      eFormToIterated remainder =
        eRotateThirdVariable omega (eFormToIterated remainder) := by
    calc
      eFormToIterated remainder =
          eFormToIterated (eRotateForm omega remainder) := by
        exact congrArg eFormToIterated hremainderInvariant
      _ = eRotateThirdVariable omega (eFormToIterated remainder) :=
        eFormToIterated_rotateForm omega remainder
  obtain ⟨Rzero, hRzeroIterated⟩ :=
    exists_e_source_cube_descent_of_rotationInvariant
      (eFormToIterated remainder) homega hremainderInvariantIterated
  have hRzeroForm : eSourceCubeSubstitutionForm Rzero = remainder := by
    have hiterated :
        eFormToIterated (eSourceCubeSubstitutionForm Rzero) =
          eFormToIterated remainder := by
      calc
      eFormToIterated (eSourceCubeSubstitutionForm Rzero) =
          eSourceCubeSubstitution Rzero :=
        AlgHom.congr_fun
          eFormToIterated_comp_sourceCubeSubstitutionForm Rzero
      _ = eFormToIterated remainder := hRzeroIterated
    have hbackLeft :
        eIteratedToForm
            (eFormToIterated (eSourceCubeSubstitutionForm Rzero)) =
          eSourceCubeSubstitutionForm Rzero := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        AlgHom.congr_fun eIteratedToForm_comp_formToIterated
          (eSourceCubeSubstitutionForm Rzero)
    have hbackRight :
        eIteratedToForm (eFormToIterated remainder) = remainder := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        AlgHom.congr_fun eIteratedToForm_comp_formToIterated remainder
    exact hbackLeft.symm.trans
      ((congrArg eIteratedToForm hiterated).trans hbackRight)
  refine ⟨Rzero, coefficient, hcoefficient, hnotdiv, ?_⟩
  rw [hRzeroForm]
  change R =
    (R - MvPolynomial.C coefficient * formT ^ N) +
      MvPolynomial.C coefficient * formT ^ N
  ring

/-- A homogeneous form has either a projective rotation zero away from
`[1:0]` or the cubic invariant decomposition with one pure power. -/
theorem exists_e_rotation_zero_away_first_or_source_descent_add_pure_power
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 3)
    (hhomogeneous : R.IsHomogeneous N) :
    (∃ x t : ℂ, (x ≠ 0 ∨ t ≠ 0) ∧
      MvPolynomial.eval ![x, t] (eRotationDifference omega R) = 0 ∧
      t ≠ 0) ∨
    ∃ Rzero : ESourceRing ℂ, ∃ coefficient : ℂ,
      coefficient ≠ 0 ∧ ¬ 3 ∣ N ∧
      R = eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N := by
  by_cases hsupport : EFormProjectiveZerosAtFirstCoordinate
      (eRotationDifference omega R)
  · right
    exact exists_e_source_descent_add_pure_power_of_projective_support
      homega hhomogeneous hsupport
  · left
    by_contra hnone
    apply hsupport
    rw [EFormProjectiveZerosAtFirstCoordinate]
    intro x t hnonzero hzero
    by_contra ht
    apply hnone
    exact ⟨x, t, hnonzero, hzero, ht⟩

theorem eRotateForm_eval (omega : ℂ) (R : Form ℂ) (x t : ℂ) :
    MvPolynomial.eval ![x, t] (eRotateForm omega R) =
      MvPolynomial.eval ![x, omega * t] R := by
  rw [← eRotateFormAlgHom_apply]
  change MvPolynomial.aeval ![x, t]
      (MvPolynomial.aeval
        ![formX, MvPolynomial.C omega * formT] R) =
    MvPolynomial.aeval ![x, omega * t] R
  rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_bind₁]
  congr
  funext i
  fin_cases i
  all_goals simp [formX, formT]

/-- A projective zero on a nontrivial rotation line gives two distinct
points with equal values under the three homogeneous coordinates. -/
structure ERotationLineCollisionCertificate
    (omega : ℂ) (R : Form ℂ) where
  x : ℂ
  t : ℂ
  t_ne_zero : t ≠ 0
  rotationDifference_ne_zero : eRotationDifference omega R ≠ 0
  sourcePoints_ne : ((x, t) : ℂ × ℂ) ≠ (x, omega * t)
  cubicValues_eq :
    MvPolynomial.eval ![x, t] (cubicForm 0 3) =
      MvPolynomial.eval ![x, omega * t] (cubicForm 0 3)
  quarticValues_eq :
    MvPolynomial.eval ![x, t] (quarticForm 1 0 0 4 0) =
      MvPolynomial.eval ![x, omega * t] (quarticForm 1 0 0 4 0)
  thirdValues_eq :
    MvPolynomial.eval ![x, t] R =
      MvPolynomial.eval ![x, omega * t] R

theorem exists_eRotationLineCollisionCertificate_of_rotation_zero
    {omega : ℂ} {R : Form ℂ} {x t : ℂ}
    (homega : IsPrimitiveRoot omega 3)
    (ht : t ≠ 0)
    (hdifferenceNe : eRotationDifference omega R ≠ 0)
    (hzero : MvPolynomial.eval ![x, t]
      (eRotationDifference omega R) = 0) :
    Nonempty (ERotationLineCollisionCertificate omega R) := by
  have homegaCube : omega ^ 3 = 1 := homega.pow_eq_one
  have homegaOne : omega ≠ 1 := homega.ne_one (by norm_num)
  have hsource : ((x, t) : ℂ × ℂ) ≠ (x, omega * t) := by
    intro heq
    have hsecond : t = omega * t := congrArg Prod.snd heq
    have hfactor : (1 - omega) * t = 0 := by
      linear_combination hsecond
    exact (mul_ne_zero (sub_ne_zero.mpr homegaOne.symm) ht) hfactor
  have hcubic :
      MvPolynomial.eval ![x, t] (cubicForm 0 3) =
        MvPolynomial.eval ![x, omega * t] (cubicForm 0 3) := by
    simp [cubicForm, formX, formT, mul_pow, homegaCube]
  have hquartic :
      MvPolynomial.eval ![x, t] (quarticForm 1 0 0 4 0) =
        MvPolynomial.eval ![x, omega * t]
          (quarticForm 1 0 0 4 0) := by
    simp [quarticForm, formX, formT, mul_pow, homegaCube]
  have hthird :
      MvPolynomial.eval ![x, t] R =
        MvPolynomial.eval ![x, omega * t] R := by
    rw [eRotationDifference] at hzero
    simp only [map_sub, eRotateForm_eval] at hzero
    exact sub_eq_zero.mp hzero
  exact ⟨{
    x := x
    t := t
    t_ne_zero := ht
    rotationDifference_ne_zero := hdifferenceNe
    sourcePoints_ne := hsource
    cubicValues_eq := hcubic
    quarticValues_eq := hquartic
    thirdValues_eq := hthird
  }⟩

/-- A noninvariant homogeneous form either has a collision on a rotation
line away from `[1:0]` or has the pure power decomposition. -/
theorem e_noninvariant_rotationLineCollision_or_source_descent_add_pure_power
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (homega : IsPrimitiveRoot omega 3)
    (hhomogeneous : R.IsHomogeneous N)
    (hnoninvariant : R ≠ eRotateForm omega R) :
    Nonempty (ERotationLineCollisionCertificate omega R) ∨
    ∃ Rzero : ESourceRing ℂ, ∃ coefficient : ℂ,
      coefficient ≠ 0 ∧ ¬ 3 ∣ N ∧
      R = eSourceCubeSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N := by
  have hdifferenceNe : eRotationDifference omega R ≠ 0 := by
    intro hzero
    apply hnoninvariant
    exact sub_eq_zero.mp hzero
  rcases
      exists_e_rotation_zero_away_first_or_source_descent_add_pure_power
        homega hhomogeneous with hrotation | hpower
  · left
    obtain ⟨x, t, _, hzero, ht⟩ := hrotation
    exact exists_eRotationLineCollisionCertificate_of_rotation_zero
      homega ht hdifferenceNe hzero
  · exact Or.inr hpower

end OnLeConjecture.DThree
