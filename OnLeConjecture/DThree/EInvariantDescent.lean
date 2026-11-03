/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EFreeBasis
public import OnLeConjecture.DTwo.HomogeneousEqualizer
public import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Cubic invariant descent for the `E` pair

This file proves the descent used at the start of the invariant branch of
Lemma `dthree-Edouble`.  A polynomial in `x,t` fixed by
`t -> omega t`, where `omega` is a primitive cube root of unity, is a
polynomial in `x,t^3`.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- The iterated presentation `C[x][t]` of the source polynomial ring. -/
abbrev EIteratedSourceRing := Polynomial (Polynomial ℂ)

/-- Evaluation identifies the iterated presentation `C[x][w]` with the
multivariate source ring used by the quartic presentation. -/
noncomputable def eIteratedToSource :
    EIteratedSourceRing →ₐ[ℂ] ESourceRing ℂ :=
  Polynomial.aevalAeval (eSourceX ℂ) (eSourceW ℂ)

/-- The inverse map sends the source coordinates `x,w` to the inner and
outer variables of `C[x][w]`. -/
noncomputable def eSourceToIterated :
    ESourceRing ℂ →ₐ[ℂ] EIteratedSourceRing :=
  MvPolynomial.aeval fun
    | ESourceCoordinate.x => C X
    | ESourceCoordinate.w => X

@[simp]
theorem eIteratedToSource_innerX :
    eIteratedToSource (C X) = eSourceX ℂ := by
  exact Polynomial.aevalAeval_X (eSourceX ℂ) (eSourceW ℂ)

@[simp]
theorem eIteratedToSource_outerX :
    eIteratedToSource X = eSourceW ℂ := by
  exact Polynomial.aevalAeval_Y (eSourceX ℂ) (eSourceW ℂ)

@[simp]
theorem eSourceToIterated_x :
    eSourceToIterated (eSourceX ℂ) = C X := by
  rw [eSourceToIterated, eSourceX, MvPolynomial.aeval_X]

@[simp]
theorem eSourceToIterated_w :
    eSourceToIterated (eSourceW ℂ) = X := by
  rw [eSourceToIterated, eSourceW, MvPolynomial.aeval_X]

theorem eIteratedToSource_comp_sourceToIterated :
    eIteratedToSource.comp eSourceToIterated =
      AlgHom.id ℂ (ESourceRing ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | x =>
      change eIteratedToSource (eSourceToIterated (eSourceX ℂ)) =
        eSourceX ℂ
      rw [eSourceToIterated_x, eIteratedToSource_innerX]
  | w =>
      change eIteratedToSource (eSourceToIterated (eSourceW ℂ)) =
        eSourceW ℂ
      rw [eSourceToIterated_w, eIteratedToSource_outerX]

theorem eSourceToIterated_comp_iteratedToSource :
    eSourceToIterated.comp eIteratedToSource =
      AlgHom.id ℂ EIteratedSourceRing := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    change eSourceToIterated (eIteratedToSource (C X)) = C X
    rw [eIteratedToSource_innerX, eSourceToIterated_x]
  · change eSourceToIterated (eIteratedToSource X) = X
    rw [eIteratedToSource_outerX, eSourceToIterated_w]

/-- The iterated and multivariate presentations of `C[x,w]` are
isomorphic. -/
noncomputable def eIteratedEquivSource :
    EIteratedSourceRing ≃ₐ[ℂ] ESourceRing ℂ :=
  AlgEquiv.ofAlgHom eIteratedToSource eSourceToIterated
    eIteratedToSource_comp_sourceToIterated
    eSourceToIterated_comp_iteratedToSource

/-- Substitute the inner variable for `x` and the cube of the outer variable
for `w`. -/
noncomputable def eSourceCubeSubstitution :
    ESourceRing ℂ →ₐ[ℂ] EIteratedSourceRing :=
  MvPolynomial.aeval fun
    | ESourceCoordinate.x => C X
    | ESourceCoordinate.w => X ^ 3

@[simp]
theorem eSourceCubeSubstitution_x :
    eSourceCubeSubstitution (eSourceX ℂ) = C X := by
  rw [eSourceCubeSubstitution, eSourceX, MvPolynomial.aeval_X]

@[simp]
theorem eSourceCubeSubstitution_w :
    eSourceCubeSubstitution (eSourceW ℂ) = X ^ 3 := by
  rw [eSourceCubeSubstitution, eSourceW, MvPolynomial.aeval_X]

/-- Evaluation of the outer variable of `C[x][w]` at `t^3`. -/
noncomputable def eIteratedCubeEvaluation :
    EIteratedSourceRing →ₐ[ℂ] EIteratedSourceRing :=
  Polynomial.eval₂AlgHom Polynomial.CAlgHom (X ^ 3)
    fun _ ↦ Commute.all _ _

theorem eSourceCubeSubstitution_comp_iteratedToSource :
    eSourceCubeSubstitution.comp eIteratedToSource =
      eIteratedCubeEvaluation := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    change eSourceCubeSubstitution (eIteratedToSource (C X)) =
      eIteratedCubeEvaluation (C X)
    rw [eIteratedToSource_innerX, eSourceCubeSubstitution_x]
    simp [eIteratedCubeEvaluation]
  · change eSourceCubeSubstitution (eIteratedToSource X) =
      eIteratedCubeEvaluation X
    rw [eIteratedToSource_outerX, eSourceCubeSubstitution_w]
    simp [eIteratedCubeEvaluation]

/-- The coordinate substitution through the multivariate presentation agrees
with direct evaluation at `w = t^3`. -/
theorem eSourceCubeSubstitution_iteratedToSource
    (Rzero : EIteratedSourceRing) :
    eSourceCubeSubstitution (eIteratedToSource Rzero) =
      Rzero.eval₂ C (X ^ 3) := by
  have h := AlgHom.congr_fun
    eSourceCubeSubstitution_comp_iteratedToSource Rzero
  rw [eIteratedCubeEvaluation,
    _root_.Polynomial.eval₂AlgHom_apply] at h
  have hC :
      (Polynomial.CAlgHom :
        Polynomial ℂ →ₐ[ℂ] EIteratedSourceRing).toRingHom =
      (Polynomial.C : Polynomial ℂ →+* EIteratedSourceRing) := by
    apply DFunLike.ext _ _
    intro a
    exact Polynomial.CAlgHom_apply (R := ℂ) (A := Polynomial ℂ) a
  calc
    eSourceCubeSubstitution (eIteratedToSource Rzero) =
        (eSourceCubeSubstitution.comp eIteratedToSource) Rzero := rfl
    _ = Rzero.eval₂
        (Polynomial.CAlgHom :
          Polynomial ℂ →ₐ[ℂ] EIteratedSourceRing).toRingHom
        (X ^ 3) := h
    _ = Rzero.eval₂ C (X ^ 3) := by rw [hC]

/-- Substitute `omega t` for `t`. -/
noncomputable def eRotateThirdVariable
    (omega : ℂ) (R : EIteratedSourceRing) : EIteratedSourceRing :=
  R.comp (C (C omega) * X)

theorem eRotateThirdVariable_eq
    (omega : ℂ) (R : EIteratedSourceRing) :
    eRotateThirdVariable omega R = R.comp (C (C omega) * X) := by
  rfl

/-- Invariance under a primitive cube root forces every occurring exponent
of `t` to be divisible by three. -/
theorem three_dvd_exponent_of_e_rotationInvariant
    {omega : ℂ} (R : EIteratedSourceRing)
    (homega : IsPrimitiveRoot omega 3)
    (hinvariant : R = eRotateThirdVariable omega R)
    {h : ℕ} (hcoeff : R.coeff h ≠ 0) :
    3 ∣ h := by
  have hsector :
      R = C (C (omega ^ 0)) *
        OnLeConjecture.DTwo.rotateSecondVariable (omega ^ 1) R := by
    simpa only [pow_zero, pow_one, map_one, one_mul,
      eRotateThirdVariable_eq,
      OnLeConjecture.DTwo.rotateSecondVariable_eq] using hinvariant
  have hdiv := OnLeConjecture.DTwo.dvd_character_of_sectorIdentity
    R homega hsector hcoeff
  simpa using hdiv

/-- Divide every exponent of `t` by three.  The evaluation theorem below
applies when all nonzero coefficients occur in degrees divisible by three. -/
noncomputable def eCubeDescent (R : EIteratedSourceRing) :
    EIteratedSourceRing :=
  OnLeConjecture.DTwo.descendSector 3 0 1 R

/-- Substituting `t^3` in the descended polynomial recovers the original
polynomial. -/
theorem eCubeDescent_eval₂
    (R : EIteratedSourceRing)
    (hdiv : ∀ h : ℕ, R.coeff h ≠ 0 → 3 ∣ h) :
    (eCubeDescent R).eval₂ C (X ^ 3) = R := by
  have hdiv' : ∀ h : ℕ, R.coeff h ≠ 0 → 3 ∣ 0 + 1 * h := by
    intro h hcoeff
    simpa using hdiv h hcoeff
  simpa [eCubeDescent] using
    (OnLeConjecture.DTwo.eval₂_descendSector
      (k := 3) (e := 0) (L := 1) R hdiv')

/-- A polynomial invariant under `t -> omega t` descends to a polynomial in
`x,w`, with `w = t^3`. -/
theorem exists_e_cube_descent_of_rotationInvariant
    {omega : ℂ} (R : EIteratedSourceRing)
    (homega : IsPrimitiveRoot omega 3)
    (hinvariant : R = eRotateThirdVariable omega R) :
    ∃ Rzero : EIteratedSourceRing,
      Rzero.eval₂ C (X ^ 3) = R := by
  refine ⟨eCubeDescent R, eCubeDescent_eval₂ R ?_⟩
  intro h hcoeff
  exact three_dvd_exponent_of_e_rotationInvariant
    R homega hinvariant hcoeff

/-- The invariant polynomial descends to the multivariate source ring used
by the quartic basis theorem. -/
theorem exists_e_source_cube_descent_of_rotationInvariant
    {omega : ℂ} (R : EIteratedSourceRing)
    (homega : IsPrimitiveRoot omega 3)
    (hinvariant : R = eRotateThirdVariable omega R) :
    ∃ Rzero : ESourceRing ℂ,
      eSourceCubeSubstitution Rzero = R := by
  obtain ⟨Rzero, hRzero⟩ :=
    exists_e_cube_descent_of_rotationInvariant R homega hinvariant
  refine ⟨eIteratedToSource Rzero, ?_⟩
  rw [eSourceCubeSubstitution_iteratedToSource]
  exact hRzero

end OnLeConjecture.DThree
