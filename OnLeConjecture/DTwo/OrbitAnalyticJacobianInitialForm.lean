/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitAnalyticNormalization
public import OnLeConjecture.Analytic.Derivation

/-!
# Analytic Jacobians and homogeneous initial forms for the quadratic orbit pair

This module proves the filtered derivative step used in the analytic orbit
normalization. A partial derivative lowers maximal ideal order by at most one.
Consequently the first homogeneous term of the analytic Jacobian of germs with
initial forms `Phi` and `R` is the polynomial Jacobian `Jac(Phi,R)`.

The two maximal minor divisibilities from the article are then preserved under
every polynomial correction in the first two components. Divisibility by the
cube of the second analytic coordinate passes to divisibility of each
polynomial Jacobian initial form by `lambda ^ 3`. This establishes
`OrbitReductionJacobianCondition` from the analytic divisibility hypotheses.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

private theorem derivation_mem_ideal_pow_of_mem_pow_succ
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (I : Ideal A) {d : ℕ} {x : A}
    (hx : x ∈ I ^ (d + 1)) :
    D x ∈ I ^ d := by
  induction d generalizing x with
  | zero => simp
  | succ d ih =>
      have hx' : x ∈ I ^ (d + 1) * I := by
        simpa only [show d + 1 + 1 = (d + 1) + 1 by rfl,
          pow_succ] using hx
      refine Submodule.mul_induction_on hx' ?_ ?_
      · intro a ha b hb
        rw [D.leibniz]
        simp only [smul_eq_mul]
        apply (I ^ (d + 1)).add_mem
        · exact Ideal.mul_mem_right (D b) (I ^ (d + 1)) ha
        · have hproduct := Ideal.mul_mem_mul (ih ha) hb
          simpa only [pow_succ, mul_comm] using hproduct
      · intro a b ha hb
        rw [map_add]
        exact (I ^ (d + 1)).add_mem ha hb

/-- A partial derivative lowers maximal ideal order by at most one. -/
theorem Germ.partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ
    {n d : ℕ} (i : Fin n) {f : Germ n}
    (hf : f ∈ Germ.maximalIdeal n ^ (d + 1)) :
    Germ.partialDerivative i f ∈ Germ.maximalIdeal n ^ d := by
  exact derivation_mem_ideal_pow_of_mem_pow_succ
    (Germ.partialDerivation i) (Germ.maximalIdeal n) hf

/-- Partial differentiation commutes with evaluation at the coordinate germs. -/
theorem Germ.partialDerivative_coordinatePolynomialAlgHom
    {n : ℕ} (i : Fin n) (P : MvPolynomial (Fin n) ℂ) :
    Germ.partialDerivative i (Germ.coordinatePolynomialAlgHom n P) =
      Germ.coordinatePolynomialAlgHom n (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [Germ.coordinatePolynomialAlgHom_C,
        Germ.partialDerivative_const, MvPolynomial.pderiv_C, map_zero]
  | add P Q hP hQ =>
      rw [map_add, Germ.partialDerivative_add, map_add, map_add, hP, hQ]
  | mul_X P j hP =>
      rw [map_mul, Germ.partialDerivative_mul, hP,
        MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
      rw [Germ.coordinatePolynomialAlgHom_X]
      by_cases hij : i = j
      · subst j
        rw [MvPolynomial.pderiv_X_self,
          Germ.partialDerivative_coordinate_same, map_one]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij),
          Germ.partialDerivative_coordinate_ne hij, map_zero]

/-- The analytic Jacobian of coordinate polynomials is the coordinate
evaluation of their polynomial Jacobian. -/
theorem Germ.jacobian_coordinatePolynomialAlgHom
    (P Q : MvPolynomial (Fin 2) ℂ) :
    Germ.jacobian (Germ.coordinatePolynomialAlgHom 2 P)
        (Germ.coordinatePolynomialAlgHom 2 Q) =
      Germ.coordinatePolynomialAlgHom 2
        (OnLeConjecture.Polynomial.jacobian P Q) := by
  simp only [Germ.jacobian_eq, OnLeConjecture.Polynomial.jacobian,
    Germ.partialDerivative_coordinatePolynomialAlgHom, map_mul, map_sub]

private theorem coordinatePolynomial_mem_maximalIdeal_pow_of_isHomogeneous
    {n d : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hP : P.IsHomogeneous d) :
    Germ.coordinatePolynomialAlgHom n P ∈ Germ.maximalIdeal n ^ d := by
  apply Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro e he
  exact hP.coeff_eq_zero (by omega)

private theorem mul_mem_ideal_pow_add
    {A : Type*} [CommRing A] (I : Ideal A)
    {a b : ℕ} {x y : A} (hx : x ∈ I ^ a) (hy : y ∈ I ^ b) :
    x * y ∈ I ^ (a + b) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul hx hy

private theorem mul_sub_mul_mem_ideal_pow_add_one
    {A : Type*} [CommRing A] (I : Ideal A)
    {m n : ℕ} {a p b q : A}
    (hap : a - p ∈ I ^ (m + 1))
    (hbq : b - q ∈ I ^ (n + 1))
    (hp : p ∈ I ^ m) (hb : b ∈ I ^ n) :
    a * b - p * q ∈ I ^ (m + n + 1) := by
  have hfirst := mul_mem_ideal_pow_add I hap hb
  have hsecond := mul_mem_ideal_pow_add I hp hbq
  rw [show m + 1 + n = m + n + 1 by omega] at hfirst
  rw [show m + (n + 1) = m + n + 1 by omega] at hsecond
  have hsum := (I ^ (m + n + 1)).add_mem
    hfirst hsecond
  convert hsum using 1
  ring

/-- If the first analytic coordinate has initial form `Phi` and a residual has
homogeneous initial form `R`, then their analytic Jacobian has polynomial
initial form `Jac(Phi, R)`. -/
theorem orbitJacobian_sub_initial_mem_maximalIdeal_pow
    (F₁ h : Germ 2)
    (hphi : F₁ -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    {R : OrbitSourceForm} {r : ℕ} (hr : 4 ≤ r)
    (hR : R.IsHomogeneous r)
    (hinitial : h - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.maximalIdeal 2 ^ (r + 1)) :
    Germ.jacobian F₁ h -
        Germ.coordinatePolynomialAlgHom 2
          (OnLeConjecture.Polynomial.jacobian
            (orbitPolynomialPhi ℂ) R) ∈
      Germ.maximalIdeal 2 ^ (r + 1) := by
  let PhiGerm := Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)
  let RGerm := Germ.coordinatePolynomialAlgHom 2 R
  have hphiDerivative : ∀ i : Fin 2,
      Germ.partialDerivative i F₁ - Germ.partialDerivative i PhiGerm ∈
        Germ.maximalIdeal 2 ^ 2 := by
    intro i
    rw [← Germ.partialDerivative_sub]
    exact Germ.partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ i hphi
  have hresidualDerivative : ∀ i : Fin 2,
      Germ.partialDerivative i h - Germ.partialDerivative i RGerm ∈
        Germ.maximalIdeal 2 ^ r := by
    intro i
    rw [← Germ.partialDerivative_sub]
    exact Germ.partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ i hinitial
  have hphiPolynomialDerivative : ∀ i : Fin 2,
      Germ.partialDerivative i PhiGerm ∈ Germ.maximalIdeal 2 := by
    intro i
    change Germ.partialDerivative i
      (Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    have hPhi : (orbitPolynomialPhi ℂ).IsHomogeneous 2 :=
      orbitPolynomialPhi_isHomogeneous (K := ℂ)
    have hhomogeneous :
        (MvPolynomial.pderiv i (orbitPolynomialPhi ℂ)).IsHomogeneous 1 := by
      simpa only [Nat.reduceSub] using hPhi.pderiv
    simpa only [pow_one] using
      coordinatePolynomial_mem_maximalIdeal_pow_of_isHomogeneous hhomogeneous
  have hRPolynomialDerivative : ∀ i : Fin 2,
      Germ.partialDerivative i RGerm ∈ Germ.maximalIdeal 2 ^ (r - 1) := by
    intro i
    change Germ.partialDerivative i
      (Germ.coordinatePolynomialAlgHom 2 R) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    apply coordinatePolynomial_mem_maximalIdeal_pow_of_isHomogeneous
    exact hR.pderiv
  have hresidualDerivativeOrder : ∀ i : Fin 2,
      Germ.partialDerivative i h ∈ Germ.maximalIdeal 2 ^ (r - 1) := by
    intro i
    have hdifference :
        Germ.partialDerivative i h - Germ.partialDerivative i RGerm ∈
          Germ.maximalIdeal 2 ^ (r - 1) :=
      Ideal.pow_le_pow_right (by omega) (hresidualDerivative i)
    have hsum := (Germ.maximalIdeal 2 ^ (r - 1)).add_mem
      hdifference (hRPolynomialDerivative i)
    convert hsum using 1
    ring
  have hfirst := mul_sub_mul_mem_ideal_pow_add_one
    (Germ.maximalIdeal 2)
    (m := 1) (n := r - 1)
    (hphiDerivative 0)
    (by simpa only [show r - 1 + 1 = r by omega] using
      hresidualDerivative 1)
    (by simpa only [pow_one] using hphiPolynomialDerivative 0)
    (hresidualDerivativeOrder 1)
  have hsecond := mul_sub_mul_mem_ideal_pow_add_one
    (Germ.maximalIdeal 2)
    (m := 1) (n := r - 1)
    (hphiDerivative 1)
    (by simpa only [show r - 1 + 1 = r by omega] using
      hresidualDerivative 0)
    (by simpa only [pow_one] using hphiPolynomialDerivative 1)
    (hresidualDerivativeOrder 0)
  have hdifference := (Germ.maximalIdeal 2 ^ (r + 1)).sub_mem
    (by simpa only [show 1 + (r - 1) + 1 = r + 1 by omega] using hfirst)
    (by simpa only [show 1 + (r - 1) + 1 = r + 1 by omega] using hsecond)
  rw [← Germ.jacobian_coordinatePolynomialAlgHom]
  simp only [Germ.jacobian_eq]
  convert hdifference using 1
  ring

/-- The Jacobian is additive across subtraction in its second argument. -/
theorem Germ.jacobian_sub_right (g h q : Germ 2) :
    Germ.jacobian g (h - q) = Germ.jacobian g h - Germ.jacobian g q := by
  simp only [Germ.jacobian_eq, Germ.partialDerivative_sub]
  ring

/-- If `y ^ 3` divides `Jac(F₁,F₂)`, it divides the Jacobian of `F₁`
with every polynomial in `F₁,F₂`. -/
theorem orbitCoordinateCube_dvd_jacobian_analyticEvaluation
    (g : PointedMapGerm 2 2)
    (hminor₁₂ : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (S : OrbitBaseRing ℂ) :
    Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0)
        (orbitAnalyticEvaluationAlgHom g S) := by
  induction S using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.C_eq_algebraMap,
        (orbitAnalyticEvaluationAlgHom g).commutes c]
      change Germ.coordinate (1 : Fin 2) ^ 3 ∣
        Germ.jacobian (g.1.component 0) (Germ.constRingHom 2 c)
      rw [Germ.jacobian_const_right]
      exact dvd_zero _
  | add P Q hP hQ =>
      rw [map_add, Germ.jacobian_add_right]
      exact dvd_add hP hQ
  | mul_X P i hP =>
      rw [map_mul, Germ.jacobian_mul_right]
      apply dvd_add
      · cases i with
        | phi =>
            rw [show MvPolynomial.X OrbitBaseCoordinate.phi =
              orbitBasePhi ℂ by rfl, orbitAnalyticEvaluationAlgHom_phi,
              Germ.jacobian_self]
            rw [mul_zero]
            exact dvd_zero _
        | psi =>
            rw [show MvPolynomial.X OrbitBaseCoordinate.psi =
              orbitBasePsi ℂ by rfl, orbitAnalyticEvaluationAlgHom_psi]
            exact dvd_mul_of_dvd_right hminor₁₂ _
      · exact dvd_mul_of_dvd_right hP _

/-- The two maximal minor divisibilities from the article persist after
subtracting any polynomial orbit correction from the third coordinate. -/
theorem orbitCoordinateCube_dvd_jacobian_residual
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (hminor₁₂ : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hminor₁₃ : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) f)
    (S : OrbitBaseRing ℂ) :
    Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0)
        (f - orbitAnalyticEvaluationAlgHom g S) := by
  rw [Germ.jacobian_sub_right]
  exact dvd_sub hminor₁₃
    (orbitCoordinateCube_dvd_jacobian_analyticEvaluation g hminor₁₂ S)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If a plane analytic germ is divisible by the cube of the second
coordinate, then every homogeneous initial form of degree at least three is
divisible by the cube of the second polynomial variable. -/
theorem orbitLambdaCube_dvd_initialForm_of_coordinateCube_dvd
    (h : Germ 2) {J : OrbitSourceForm} {r : ℕ} (hr : 3 ≤ r)
    (hJ : J.IsHomogeneous r)
    (hinitial : h - Germ.coordinatePolynomialAlgHom 2 J ∈
      Germ.maximalIdeal 2 ^ (r + 1))
    (hdivides : Germ.coordinate (1 : Fin 2) ^ 3 ∣ h) :
    orbitPolynomialLambda ℂ ^ 3 ∣ J := by
  classical
  let lambdaCube : OrbitSourceForm := orbitPolynomialLambda ℂ ^ 3
  have hlambdaEvaluation : Germ.coordinatePolynomialAlgHom 2 lambdaCube =
      Germ.coordinate (1 : Fin 2) ^ 3 := by
    dsimp only [lambdaCube]
    rw [map_pow, orbitPolynomialLambda,
      Germ.coordinatePolynomialAlgHom_X]
  rcases hdivides with ⟨A, hA⟩
  obtain ⟨P, hP⟩ :=
    Germ.exists_coordinatePolynomial_mod_maximalIdeal_pow 2 (r - 2) A
  have hcoordinateCube : Germ.coordinate (1 : Fin 2) ^ 3 ∈
      Germ.maximalIdeal 2 ^ 3 :=
    Ideal.pow_mem_pow (Germ.coordinate_mem_maximalIdeal 1) 3
  have hproductRemainder := mul_mem_ideal_pow_add
    (Germ.maximalIdeal 2) hcoordinateCube hP
  rw [show 3 + (r - 2) = r + 1 by omega] at hproductRemainder
  have hproductCongruence :
      Germ.coordinate (1 : Fin 2) ^ 3 * A -
          Germ.coordinatePolynomialAlgHom 2 (lambdaCube * P) ∈
        Germ.maximalIdeal 2 ^ (r + 1) := by
    rw [map_mul, hlambdaEvaluation]
    convert hproductRemainder using 1
    ring
  have hanalyticCongruence :
      h - Germ.coordinatePolynomialAlgHom 2 (lambdaCube * P) ∈
        Germ.maximalIdeal 2 ^ (r + 1) := by
    rw [hA]
    exact hproductCongruence
  have hgermDifference := (Germ.maximalIdeal 2 ^ (r + 1)).sub_mem
    hanalyticCongruence hinitial
  have hcoordinateDifference :
      Germ.coordinatePolynomialAlgHom 2 (J - lambdaCube * P) ∈
        Germ.maximalIdeal 2 ^ (r + 1) := by
    rw [map_sub]
    convert hgermDifference using 1
    ring
  have hpolynomialDifference :
      J - lambdaCube * P ∈
        MvPolynomial.idealOfVars (Fin 2) ℂ ^ (r + 1) :=
    Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mpr
      hcoordinateDifference
  have hcomponentZero :
      MvPolynomial.homogeneousComponent r (J - lambdaCube * P) = 0 := by
    ext e
    rw [MvPolynomial.coeff_homogeneousComponent,
      MvPolynomial.coeff_zero]
    by_cases he : e.degree = r
    · rw [if_pos he]
      exact (MvPolynomial.mem_pow_idealOfVars_iff' (r + 1)
        (J - lambdaCube * P)).mp hpolynomialDifference e (by omega)
    · rw [if_neg he]
  have hcomponentEquality :
      J = MvPolynomial.homogeneousComponent r (lambdaCube * P) := by
    rw [map_sub] at hcomponentZero
    have hJcomponent : MvPolynomial.homogeneousComponent r J = J := by
      rw [MvPolynomial.homogeneousComponent_of_mem hJ, if_pos rfl]
    rw [hJcomponent] at hcomponentZero
    exact sub_eq_zero.mp hcomponentZero
  have hlambdaHomogeneous : lambdaCube.IsHomogeneous 3 := by
    dsimp only [lambdaCube, orbitPolynomialLambda]
    simpa only [Nat.reduceMul, one_mul] using
      (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow 3
  let principal : Ideal OrbitSourceForm := Ideal.span {lambdaCube}
  have hprincipalHomogeneous : principal.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) := by
    apply Ideal.homogeneous_span
    intro q hq
    have hqEquality : q = lambdaCube := by
      simpa only [Set.mem_singleton_iff] using hq
    subst q
    exact ⟨3, hlambdaHomogeneous⟩
  have hlambdaMem : lambdaCube ∈ principal :=
    Ideal.subset_span (Set.mem_singleton lambdaCube)
  have hproductMem : lambdaCube * P ∈ principal :=
    Ideal.mul_mem_right P principal hlambdaMem
  have hcomponentMem := MvPolynomial.homogeneousComponent_mem_of_mem
    hprincipalHomogeneous hproductMem r
  rw [← hcomponentEquality] at hcomponentMem
  exact Ideal.mem_span_singleton.mp hcomponentMem

/-- Analytic divisibility of a Jacobian by the coordinate cube passes to
divisibility of its homogeneous polynomial initial Jacobian by `lambda ^ 3`. -/
theorem orbitLambdaCube_dvd_polynomialJacobian_of_coordinateCube_dvd
    (F₁ h : Germ 2)
    (hphi : F₁ -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    {R : OrbitSourceForm} {r : ℕ} (hr : 4 ≤ r)
    (hR : R.IsHomogeneous r)
    (hinitial : h - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.maximalIdeal 2 ^ (r + 1))
    (hdivides : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian F₁ h) :
    orbitPolynomialLambda ℂ ^ 3 ∣
      OnLeConjecture.Polynomial.jacobian (orbitPolynomialPhi ℂ) R := by
  have hPhi : (orbitPolynomialPhi ℂ).IsHomogeneous 2 :=
    orbitPolynomialPhi_isHomogeneous (K := ℂ)
  have hJacobianHomogeneous :
      (OnLeConjecture.Polynomial.jacobian
        (orbitPolynomialPhi ℂ) R).IsHomogeneous r := by
    have hraw := OnLeConjecture.Polynomial.isWeightedHomogeneous_jacobian
      (1 : Fin 2 → ℕ) (orbitPolynomialPhi ℂ) R 2 r hPhi hR
        (by simp) (by simp)
        (by simpa only [Pi.one_apply] using (show 1 ≤ r by omega))
        (by simpa only [Pi.one_apply] using (show 1 ≤ r by omega))
    have hdegree : (2 - (1 : Fin 2 → ℕ) 0) +
        (r - (1 : Fin 2 → ℕ) 1) = r := by
      simp only [Pi.one_apply]
      omega
    rw [hdegree] at hraw
    exact hraw
  apply orbitLambdaCube_dvd_initialForm_of_coordinateCube_dvd
    (Germ.jacobian F₁ h) (by omega) hJacobianHomogeneous
  · exact orbitJacobian_sub_initial_mem_maximalIdeal_pow
      F₁ h hphi hr hR hinitial
  · exact hdivides

/-- The two maximal minor divisibilities in the quadratic orbit case
imply the Jacobian condition at every stage of the canonical reduction. -/
theorem orbitReductionJacobianCondition_of_coordinateCube_dvd_minors
    (g : PointedMapGerm 2 2) (f : Germ 2)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hminor₁₂ : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hminor₁₃ : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) f) :
    OrbitReductionJacobianCondition g f := by
  intro k R hR hinitial
  let residual := f - orbitAnalyticEvaluationAlgHom g
    (orbitReductionPolynomial g f k)
  have hresidualDivides : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) residual := by
    exact orbitCoordinateCube_dvd_jacobian_residual g f
      hminor₁₂ hminor₁₃ (orbitReductionPolynomial g f k)
  apply orbitLambdaCube_dvd_polynomialJacobian_of_coordinateCube_dvd
    (g.1.component 0) residual hphi (r := 4 + k) (by omega) hR
  · simpa only [residual, show 4 + k + 1 = 5 + k by omega] using hinitial
  · exact hresidualDivides

/-- The analytic normalization dichotomy under the two maximal minor
divisibilities appearing in the quadratic orbit case. -/
theorem orbitAnalyticImage_or_first_nonbaseLambdaFour_initialForm_of_minors
    (g : PointedMapGerm 2 2) (hfinite : g.IsFiniteAtOrigin)
    (hphi : g.1.component 0 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
      Germ.maximalIdeal 2 ^ 3)
    (hpsi : g.1.component 1 -
        Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
      Germ.maximalIdeal 2 ^ 4)
    (f : Germ 2) (horder : f ∈ Germ.maximalIdeal 2 ^ 4)
    (hminor₁₂ : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) (g.1.component 1))
    (hminor₁₃ : Germ.coordinate (1 : Fin 2) ^ 3 ∣
      Germ.jacobian (g.1.component 0) f) :
    (∃ q : Germ 2, g.pullbackRingHom q = f) ∨
      ∃ k : ℕ, ∃ Q : OrbitBaseRing ℂ, ∃ R : OrbitSourceForm,
        (∀ j < k, OrbitStageRemovable g f j) ∧
        ¬ OrbitStageRemovable g f k ∧
        R.IsHomogeneous (4 + k) ∧
        R ≠ 0 ∧
        orbitPolynomialLambda ℂ ^ 4 ∣ R ∧
        R ∉ Set.range (orbitBaseToSource ℂ) ∧
        (f - orbitAnalyticEvaluationAlgHom g Q) -
            Germ.coordinatePolynomialAlgHom 2 R ∈
          Germ.maximalIdeal 2 ^ (5 + k) := by
  apply orbitAnalyticImage_or_first_nonbaseLambdaFour_initialForm
    g hfinite hphi hpsi f horder
  exact orbitReductionJacobianCondition_of_coordinateCube_dvd_minors
    g f hphi hminor₁₂ hminor₁₃

end OnLeConjecture.DTwo
