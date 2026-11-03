/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitConicSurjectivity
public import OnLeConjecture.DTwo.OrbitDifferenceDescent
public import Mathlib.Tactic.Push

/-!
# Collision for the quadratic orbit map

This file proves the algebraic collision statement used in the case of
quadratic initial degree. The isolation certificate records a nonzero
homogeneous pullback difference and an off node projective zero. Topological
and scheme theoretic isolation are outside the certificate.
-/

public section

namespace OnLeConjecture.DTwo

/-- Two distinct nonzero source points with the same three polynomial
values. -/
@[expose]
def HasOrbitCollision (R : OrbitSourceForm) : Prop :=
  ∃ s lambda t zeta : ℂ,
    s ≠ t ∧
      (s ≠ 0 ∨ lambda ≠ 0) ∧
      (t ≠ 0 ∨ zeta ≠ 0) ∧
      orbitPhi s lambda = orbitPhi t zeta ∧
      orbitPsi s lambda = orbitPsi t zeta ∧
      MvPolynomial.eval ![s, lambda] R =
        MvPolynomial.eval ![t, zeta] R

/-- Algebraic data certifying a zero away from the two points over the
diagonal node. -/
@[expose]
def OrbitAlgebraicIsolationCertificate
    (delta : ℂ) (R : OrbitSourceForm) : Prop :=
  orbitConicDifference delta R ≠ 0 ∧
    ∃ u v : ℂ,
      (u ≠ 0 ∨ v ≠ 0) ∧
      MvPolynomial.eval ![u, v] (orbitConicDifference delta R) = 0 ∧
      u ≠ Complex.I * v ∧ u ≠ -Complex.I * v

/-- A finite chart version of the algebraic zero certificate. -/
@[expose]
def OrbitFiniteChartRootCertificate
    (delta : ℂ) (R : OrbitSourceForm) : Prop :=
  let polynomial := orbitParameterDehomogenize
    (orbitConicDifference delta R)
  polynomial ≠ 0 ∧
    ∃ z : ℂ,
      polynomial.eval z = 0 ∧
        z ≠ Complex.I ∧ z ≠ -Complex.I

/-- Distinct source points in one orbit fibre are both nonzero. -/
theorem orbit_same_values_nonzero_of_first_ne
    {s lambda t zeta : ℂ} (hst : s ≠ t)
    (hphi : orbitPhi s lambda = orbitPhi t zeta)
    (hpsi : orbitPsi s lambda = orbitPsi t zeta) :
    (s ≠ 0 ∨ lambda ≠ 0) ∧ (t ≠ 0 ∨ zeta ≠ 0) := by
  constructor
  · by_contra hzero
    push Not at hzero
    rcases hzero with ⟨hs, hlambda⟩
    subst s
    subst lambda
    have hzetaSq : zeta ^ 2 = t ^ 2 := by
      norm_num [orbitPhi] at hphi
      linear_combination hphi
    have htCube : t ^ 3 = 0 := by
      norm_num [orbitPsi] at hpsi
      rw [hzetaSq] at hpsi
      calc
        t ^ 3 = -(2 * t ^ 3 - 3 * t * t ^ 2) := by ring
        _ = 0 := by
          rw [← hpsi]
          ring
    have ht : t = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp htCube
    exact hst ht.symm
  · by_contra hzero
    push Not at hzero
    rcases hzero with ⟨ht, hzeta⟩
    subst t
    subst zeta
    have hlambdaSq : lambda ^ 2 = s ^ 2 := by
      norm_num [orbitPhi] at hphi
      linear_combination -hphi
    have hsCube : s ^ 3 = 0 := by
      norm_num [orbitPsi] at hpsi
      rw [hlambdaSq] at hpsi
      calc
        s ^ 3 = -(2 * s ^ 3 - 3 * s * s ^ 2) := by ring
        _ = 0 := by
          rw [hpsi]
          ring
    have hs : s = 0 :=
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hsCube
    exact hst hs

private theorem orbit_three_fibre_values
    {lambdaSide lambdaMiddle : ℂ}
    (hside : lambdaSide ^ 2 = 2 / 3)
    (hmiddle : lambdaMiddle ^ 2 = -(1 / 3)) :
    orbitPhi (-1) lambdaSide = 1 / 3 ∧
      orbitPsi (-1) lambdaSide = 0 ∧
      orbitPhi 0 lambdaMiddle = 1 / 3 ∧
      orbitPsi 0 lambdaMiddle = 0 ∧
      orbitPhi 1 lambdaSide = 1 / 3 ∧
      orbitPsi 1 lambdaSide = 0 := by
  simp only [orbitPhi, orbitPsi]
  constructor
  · rw [hside]
    norm_num
  constructor
  · rw [hside]
    norm_num
  constructor
  · rw [hmiddle]
    norm_num
  constructor
  · ring
  constructor
  · rw [hside]
    norm_num
  · rw [hside]
    norm_num

/-- Node support for a nonzero pullback difference contradicts the cyclic
identity on the fibre over `(1/3,0)`. -/
theorem not_orbitProjectiveZerosAtNodes_of_degree_ge_four
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r) (hr : 4 ≤ r) :
    ¬ OrbitProjectiveZerosAtNodes (orbitConicDifference delta R) := by
  intro hsupport
  have hodd := orbitConicDifference_degree_odd_of_projective_support
    hR delta hsupport
  obtain ⟨coefficient, hcoefficient, hidentity⟩ :=
    orbitConicDifference_eq_scalar_mul_T_sub_S_pow hR delta hsupport
  obtain ⟨lambdaSide, hside⟩ :=
    IsAlgClosed.exists_pow_nat_eq (2 / 3 : ℂ) (by norm_num : 0 < 2)
  obtain ⟨lambdaMiddle, hmiddle⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-(1 / 3) : ℂ) (by norm_num : 0 < 2)
  obtain ⟨hphiNeg, hpsiNeg, hphiZero, hpsiZero,
      hphiOne, hpsiOne⟩ :=
    orbit_three_fibre_values hside hmiddle
  have hresidualNegZero :
      IsOrbitResidualPair (-1) lambdaSide 0 lambdaMiddle :=
    (orbit_same_values_iff_residual (by norm_num)).mp
      ⟨hphiNeg.trans hphiZero.symm, hpsiNeg.trans hpsiZero.symm⟩
  have hresidualZeroOne :
      IsOrbitResidualPair 0 lambdaMiddle 1 lambdaSide :=
    (orbit_same_values_iff_residual (by norm_num)).mp
      ⟨hphiZero.trans hphiOne.symm, hpsiZero.trans hpsiOne.symm⟩
  have hresidualOneNeg :
      IsOrbitResidualPair 1 lambdaSide (-1) lambdaSide :=
    (orbit_same_values_iff_residual (by norm_num)).mp
      ⟨hphiOne.trans hphiNeg.symm, hpsiOne.trans hpsiNeg.symm⟩
  have hNegZero := orbitConicDifference_identity_on_residualPair
    hdelta hidentity hresidualNegZero hresidualNegZero.conicEquation
  have hZeroOne := orbitConicDifference_identity_on_residualPair
    hdelta hidentity hresidualZeroOne hresidualZeroOne.conicEquation
  have hOneNeg := orbitConicDifference_identity_on_residualPair
    hdelta hidentity hresidualOneNeg hresidualOneNeg.conicEquation
  exact orbit_odd_power_differences_not_cocycle r (by omega) hodd
    coefficient
    (MvPolynomial.eval ![(-1 : ℂ), lambdaSide] R)
    (MvPolynomial.eval ![(0 : ℂ), lambdaMiddle] R)
    (MvPolynomial.eval ![(1 : ℂ), lambdaSide] R)
    hcoefficient hNegZero hZeroOne hOneNeg

/-- Failure of node support produces an off node projective zero of the
pullback difference. -/
theorem orbitAlgebraicIsolationCertificate_of_not_support
    {delta : ℂ} {R : OrbitSourceForm}
    (hdifference : orbitConicDifference delta R ≠ 0)
    (hnotSupport :
      ¬ OrbitProjectiveZerosAtNodes (orbitConicDifference delta R)) :
    OrbitAlgebraicIsolationCertificate delta R := by
  rw [OrbitProjectiveZerosAtNodes] at hnotSupport
  push Not at hnotSupport
  obtain ⟨u, v, hparameter, hzero, hnodes⟩ := hnotSupport
  exact ⟨hdifference, u, v, hparameter, hzero,
    hnodes.1, hnodes.2⟩

/-- An off node projective zero in the chart `v ≠ 0` gives a root of a
nonzero chart polynomial away from `i` and `-i`. -/
theorem orbitFiniteChartRootCertificate_of_projective_zero
    {delta : ℂ} {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r)
    (hdifference : orbitConicDifference delta R ≠ 0)
    {u v : ℂ} (hv : v ≠ 0)
    (hzero : MvPolynomial.eval ![u, v]
      (orbitConicDifference delta R) = 0)
    (hfirst : u ≠ Complex.I * v)
    (hsecond : u ≠ -Complex.I * v) :
    OrbitFiniteChartRootCertificate delta R := by
  let form := orbitConicDifference delta R
  let polynomial := orbitParameterDehomogenize form
  have hformHomogeneous : form.IsHomogeneous (4 * r) :=
    orbitConicDifference_isHomogeneous hR delta
  have hdegree : polynomial.natDegree ≤ 4 * r :=
    orbitParameterDehomogenize_natDegree_le hformHomogeneous
  have hrecover : polynomial.homogenize (4 * r) = form :=
    orbitParameter_homogenize_dehomogenize hformHomogeneous
  have hpolynomial : polynomial ≠ 0 := by
    intro hpolynomialZero
    apply hdifference
    change form = 0
    rw [← hrecover, hpolynomialZero, Polynomial.homogenize_zero]
  have hevaluation := Polynomial.eval_homogenize hdegree ![u, v] hv
  rw [hrecover, hzero] at hevaluation
  have hroot : polynomial.eval (u / v) = 0 := by
    apply (mul_eq_zero.mp hevaluation.symm).resolve_right
    exact pow_ne_zero (4 * r) hv
  have hrootFirst : u / v ≠ Complex.I := by
    intro heq
    apply hfirst
    exact (div_eq_iff hv).mp heq
  have hrootSecond : u / v ≠ -Complex.I := by
    intro heq
    apply hsecond
    exact (div_eq_iff hv).mp heq
  exact ⟨hpolynomial, u / v, hroot, hrootFirst, hrootSecond⟩

private theorem orbitConicRhoValue_ne_zero_of_not_nodes
    {delta u v : ℂ} (hdelta : delta ^ 2 = 3)
    (hnotNodes : u ≠ Complex.I * v ∧ u ≠ -Complex.I * v) :
    orbitConicRhoValue delta u v ≠ 0 := by
  have hdeltaNe : delta ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hdelta
    norm_num at hdelta
  rw [orbitConicRhoValue_eq]
  apply mul_ne_zero hdeltaNe
  intro hsum
  have hfactor :
      (u - Complex.I * v) * (u + Complex.I * v) = 0 := by
    calc
      (u - Complex.I * v) * (u + Complex.I * v) =
          u ^ 2 - Complex.I ^ 2 * v ^ 2 := by ring
      _ = u ^ 2 + v ^ 2 := by
        rw [Complex.I_sq]
        ring
      _ = 0 := hsum
  rcases mul_eq_zero.mp hfactor with hfirst | hsecond
  · exact hnotNodes.1 (sub_eq_zero.mp hfirst)
  · apply hnotNodes.2
    simpa only [neg_mul] using eq_neg_of_add_eq_zero_left hsecond

/-- The collision and its algebraic projective zero certificate for a fixed
square root of three. -/
theorem hasOrbitCollision_and_certificate
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r) (hr : 4 ≤ r)
    (_hdivides : orbitPolynomialLambda ℂ ^ 4 ∣ R)
    (hnotBase : R ∉ Set.range (orbitBaseToSource ℂ)) :
    HasOrbitCollision R ∧
      OrbitAlgebraicIsolationCertificate delta R := by
  have hdifference : orbitConicDifference delta R ≠ 0 := by
    intro hzero
    exact hnotBase
      (orbitConicDifference_eq_zero_mem_base_of_isHomogeneous
        hdelta hR hzero)
  by_cases hsupport : OrbitProjectiveZerosAtNodes
      (orbitConicDifference delta R)
  · exact (not_orbitProjectiveZerosAtNodes_of_degree_ge_four
      hdelta hR hr hsupport).elim
  have hcertificate := orbitAlgebraicIsolationCertificate_of_not_support
    hdifference hsupport
  rcases hcertificate.2 with
    ⟨u, v, hparameter, hzero, hfirstNode, hsecondNode⟩
  have hrho := orbitConicRhoValue_ne_zero_of_not_nodes hdelta
    ⟨hfirstNode, hsecondNode⟩
  have hcollision := orbitConicDifference_zero_gives_collision
    hdelta R hrho hzero
  let alpha := orbitConicAlphaValue u v
  let beta := orbitConicBetaValue u v
  let rho := orbitConicRhoValue delta u v
  let s := -(alpha ^ 2 + 2 * beta ^ 2)
  let lambda := rho * beta
  let t := 2 * alpha ^ 2 + beta ^ 2
  let zeta := rho * alpha
  change s ≠ t ∧
      orbitPhi s lambda = orbitPhi t zeta ∧
      orbitPsi s lambda = orbitPsi t zeta ∧
      MvPolynomial.eval ![s, lambda] R =
        MvPolynomial.eval ![t, zeta] R at hcollision
  have hnonzero := orbit_same_values_nonzero_of_first_ne
    hcollision.1 hcollision.2.1 hcollision.2.2.1
  refine ⟨?_, ⟨hdifference, u, v, hparameter, hzero,
    hfirstNode, hsecondNode⟩⟩
  exact ⟨s, lambda, t, zeta, hcollision.1,
    hnonzero.1, hnonzero.2, hcollision.2.1,
    hcollision.2.2.1, hcollision.2.2.2⟩

/-- The orbit collision together with an algebraic certificate for a
projective zero away from the node. -/
theorem hasOrbitCollision_and_exists_certificate
    {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r) (hr : 4 ≤ r)
    (hdivides : orbitPolynomialLambda ℂ ^ 4 ∣ R)
    (hnotBase : R ∉ Set.range (orbitBaseToSource ℂ)) :
    HasOrbitCollision R ∧
      ∃ delta : ℂ, delta ^ 2 = 3 ∧
        OrbitAlgebraicIsolationCertificate delta R := by
  obtain ⟨delta, hdelta⟩ :=
    IsAlgClosed.exists_pow_nat_eq (3 : ℂ) (by norm_num : 0 < 2)
  have hresult := hasOrbitCollision_and_certificate hdelta hR hr
    hdivides hnotBase
  exact ⟨hresult.1, delta, hdelta, hresult.2⟩

/-- The algebraic collision conclusion corresponding to the quadratic
orbit lemma. -/
theorem hasOrbitCollision_of_homogeneous_not_mem_base
    {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r) (hr : 4 ≤ r)
    (hdivides : orbitPolynomialLambda ℂ ^ 4 ∣ R)
    (hnotBase : R ∉ Set.range (orbitBaseToSource ℂ)) :
    HasOrbitCollision R :=
  (hasOrbitCollision_and_exists_certificate hR hr hdivides hnotBase).1

end OnLeConjecture.DTwo
