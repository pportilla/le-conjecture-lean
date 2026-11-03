/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitWeightedPairRescaling

/-!
# A finite chart for the quadratic orbit collision

The involution of the conic parameter line moves a point at infinity into
the chart where the second parameter is one. Thus every algebraic isolation
certificate gives a root of the dehomogenized difference away from the two
node parameters.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- Every algebraic isolation certificate has a representative in the
finite parameter chart. -/
theorem orbitFiniteChartRootCertificate_of_algebraicIsolation
    {delta : ℂ} {R : OrbitSourceForm} {r : ℕ}
    (hR : R.IsHomogeneous r)
    (hcertificate : OrbitAlgebraicIsolationCertificate delta R) :
    OrbitFiniteChartRootCertificate delta R := by
  rcases hcertificate with
    ⟨hdifference, u, v, hparameter, hzero, hfirst, hsecond⟩
  by_cases hv : v = 0
  · subst v
    have hu : u ≠ 0 := by simpa using hparameter
    have heigen := orbitParameterLinearChange_conicDifference hR delta
    have heval := congrArg
      (fun form : OrbitParameterForm ↦ MvPolynomial.eval ![u, 0] form)
      heigen
    have hchangeEvaluation : MvPolynomial.eval ![u, 0]
        (orbitParameterLinearChange (orbitConicDifference delta R)) =
      MvPolynomial.eval ![-u, u] (orbitConicDifference delta R) := by
      rw [orbitParameterLinearChange]
      change MvPolynomial.aeval ![u, 0]
        (MvPolynomial.bind₁ ![orbitLinearFirst, orbitLinearSecond]
          (orbitConicDifference delta R)) = _
      rw [MvPolynomial.aeval_bind₁]
      have hvalues :
          (fun i : Fin 2 ↦ MvPolynomial.aeval ![u, 0]
            (![orbitLinearFirst, orbitLinearSecond] i)) = ![-u, u] := by
        funext i
        fin_cases i <;> simp [orbitLinearFirst, orbitLinearSecond]
      rw [hvalues]
      simp [MvPolynomial.aeval_def]
    have hchangedZero : MvPolynomial.eval ![-u, u]
        (orbitConicDifference delta R) = 0 := by
      rw [hchangeEvaluation] at heval
      simpa [hzero] using heval
    have hfirstChanged : -u ≠ Complex.I * u := by
      intro heq
      have hproduct : (-1 - Complex.I) * u = 0 := by
        linear_combination heq
      have hcoefficient := (mul_eq_zero.mp hproduct).resolve_right hu
      have himaginary := congrArg Complex.im hcoefficient
      norm_num at himaginary
    have hsecondChanged : -u ≠ -Complex.I * u := by
      intro heq
      have hproduct : (-1 + Complex.I) * u = 0 := by
        linear_combination heq
      have hcoefficient := (mul_eq_zero.mp hproduct).resolve_right hu
      have himaginary := congrArg Complex.im hcoefficient
      norm_num at himaginary
    exact orbitFiniteChartRootCertificate_of_projective_zero
      hR hdifference hu hchangedZero hfirstChanged hsecondChanged
  · exact orbitFiniteChartRootCertificate_of_projective_zero
      hR hdifference hv hzero hfirst hsecond

/-- The finite chart coordinates of the first source point on the conic. -/
@[expose]
noncomputable def orbitFiniteChartFirstPoint
    (delta z : ℂ) : ℂ × ℂ :=
  (MvPolynomial.eval ![z, 1] orbitConicS,
    MvPolynomial.eval ![z, 1] (orbitConicLambda delta))

/-- The finite chart coordinates of the second source point on the conic. -/
@[expose]
noncomputable def orbitFiniteChartSecondPoint
    (delta z : ℂ) : ℂ × ℂ :=
  (MvPolynomial.eval ![z, 1] orbitConicT,
    MvPolynomial.eval ![z, 1] (orbitConicZeta delta))

/-- The ordered pair of source points on the finite conic chart. -/
@[expose]
noncomputable def orbitFiniteChartPair
    (delta z : ℂ) : (ℂ × ℂ) × (ℂ × ℂ) :=
  (orbitFiniteChartFirstPoint delta z,
    orbitFiniteChartSecondPoint delta z)

/-- The pullback difference is the third coordinate difference along the
finite conic chart. -/
theorem orbitPairInitialDifference_finiteChart
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    (R : OrbitSourceForm) (z : ℂ) :
    orbitPairInitialDifference
        (OnLeConjecture.DThree.weightedPolynomialMap
          (orbitInitialPolynomialMap R))
        (orbitFiniteChartPair delta z) =
      ![0, 0, (orbitParameterDehomogenize
        (orbitConicDifference delta R)).eval z] := by
  rw [orbitPairInitialDifference,
    weightedPolynomialMap_orbitInitialPolynomialMap,
    weightedPolynomialMap_orbitInitialPolynomialMap]
  simp only [orbitFiniteChartPair]
  funext i
  fin_cases i
  · simp only [Pi.sub_apply, Fin.zero_eta, Matrix.cons_val_zero]
    simp only [orbitFiniteChartFirstPoint, orbitFiniteChartSecondPoint,
      orbitPhi, orbitConicS_eval, orbitConicLambda_eval,
      orbitConicT_eval, orbitConicZeta_eval]
    rw [orbitConicRhoValue_eq, orbitConicAlphaValue_eq,
      orbitConicBetaValue_eq]
    ring_nf
    rw [hdelta]
    ring
  · simp only [Pi.sub_apply, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    simp only [orbitFiniteChartFirstPoint, orbitFiniteChartSecondPoint,
      orbitPsi, orbitConicS_eval, orbitConicLambda_eval,
      orbitConicT_eval, orbitConicZeta_eval]
    rw [orbitConicRhoValue_eq, orbitConicAlphaValue_eq,
      orbitConicBetaValue_eq]
    ring_nf
    rw [hdelta]
    ring
  · simp only [Pi.sub_apply, Fin.reduceFinMk, Matrix.cons_val]
    simp only [orbitFiniteChartFirstPoint, orbitFiniteChartSecondPoint,
      orbitParameterDehomogenize_eval]
    rw [orbitConicDifference_eval]
    simp only [orbitConicS_eval, orbitConicLambda_eval,
      orbitConicT_eval, orbitConicZeta_eval]

/-- A finite chart parameter away from the two node values has nonzero
conic coordinate `rho`. -/
theorem orbitConicRhoValue_ne_zero_of_finite_not_nodes
    {delta z : ℂ} (hdelta : delta ^ 2 = 3)
    (hfirst : z ≠ Complex.I) (hsecond : z ≠ -Complex.I) :
    orbitConicRhoValue delta z 1 ≠ 0 := by
  have hdeltaNe : delta ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hdelta
    norm_num at hdelta
  rw [orbitConicRhoValue_eq]
  apply mul_ne_zero hdeltaNe
  intro hsum
  have hfactor :
      (z - Complex.I) * (z + Complex.I) = 0 := by
    calc
      (z - Complex.I) * (z + Complex.I) =
          z ^ 2 - Complex.I ^ 2 := by ring
      _ = z ^ 2 + 1 := by rw [Complex.I_sq]; ring
      _ = 0 := by simpa using hsum
  rcases mul_eq_zero.mp hfactor with hz | hz
  · exact hfirst (sub_eq_zero.mp hz)
  · apply hsecond
    simpa using eq_neg_of_add_eq_zero_left hz

/-- At a distinct orbit collision, the two second source coordinates do
not both vanish. -/
theorem orbit_second_coordinates_not_both_zero
    {s lambda t zeta : ℂ} (hst : s ≠ t)
    (hphi : orbitPhi s lambda = orbitPhi t zeta)
    (hpsi : orbitPsi s lambda = orbitPsi t zeta) :
    lambda ≠ 0 ∨ zeta ≠ 0 := by
  by_contra hzero
  push Not at hzero
  rcases hzero with ⟨hlambda, hzeta⟩
  subst lambda
  subst zeta
  have hsSquare : s ^ 2 = t ^ 2 := by
    simpa [orbitPhi] using hphi
  have hsCube : s ^ 3 = t ^ 3 := by
    simpa [orbitPsi] using hpsi
  have hfactor : (s - t) * (s + t) = 0 := by
    linear_combination hsSquare
  have hsum : s + t = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hst)
  have hs : s = -t := eq_neg_of_add_eq_zero_left hsum
  have ht : t = 0 := by
    rw [hs] at hsCube
    have htCube : t ^ 3 = 0 := by
      linear_combination (-1 / 2 : ℂ) * hsCube
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp htCube
  apply hst
  rw [hs, ht, neg_zero]

/-- Finite chart data for an isolated algebraic orbit collision. -/
structure OrbitFiniteChartCollisionData
    (delta : ℂ) (R : OrbitSourceForm) : Type where
  parameter : ℂ
  polynomial_ne :
    orbitParameterDehomogenize (orbitConicDifference delta R) ≠ 0
  parameter_root :
    (orbitParameterDehomogenize
      (orbitConicDifference delta R)).IsRoot parameter
  parameter_ne_first_node : parameter ≠ Complex.I
  parameter_ne_second_node : parameter ≠ -Complex.I
  first_ne_second :
    (orbitFiniteChartPair delta parameter).1 ≠
      (orbitFiniteChartPair delta parameter).2
  second_coordinates_ne :
    (orbitFiniteChartPair delta parameter).1.2 ≠ 0 ∨
      (orbitFiniteChartPair delta parameter).2.2 ≠ 0

/-- An algebraic isolation certificate produces finite chart collision
data. -/
theorem exists_orbitFiniteChartCollisionData
    {delta : ℂ} (hdelta : delta ^ 2 = 3)
    {R : OrbitSourceForm} {r : ℕ} (hR : R.IsHomogeneous r)
    (hcertificate : OrbitAlgebraicIsolationCertificate delta R) :
    Nonempty (OrbitFiniteChartCollisionData delta R) := by
  have hchart := orbitFiniteChartRootCertificate_of_algebraicIsolation
    hR hcertificate
  dsimp only [OrbitFiniteChartRootCertificate] at hchart
  rcases hchart with ⟨hpolynomial, z, hz, hfirst, hsecond⟩
  have hrho := orbitConicRhoValue_ne_zero_of_finite_not_nodes
    hdelta hfirst hsecond
  have hzero : MvPolynomial.eval ![z, 1]
      (orbitConicDifference delta R) = 0 := by
    exact (orbitParameterDehomogenize_eval
      (orbitConicDifference delta R) z).symm.trans hz
  have hcollision := orbitConicDifference_zero_gives_collision
    hdelta R hrho hzero
  dsimp only at hcollision
  have hpair :
      orbitFiniteChartPair delta z =
        ((-(orbitConicAlphaValue z 1 ^ 2 +
              2 * orbitConicBetaValue z 1 ^ 2),
            orbitConicRhoValue delta z 1 * orbitConicBetaValue z 1),
          (2 * orbitConicAlphaValue z 1 ^ 2 +
              orbitConicBetaValue z 1 ^ 2,
            orbitConicRhoValue delta z 1 * orbitConicAlphaValue z 1)) := by
    ext <;> simp [orbitFiniteChartPair, orbitFiniteChartFirstPoint,
      orbitFiniteChartSecondPoint, orbitConicS_eval,
      orbitConicLambda_eval, orbitConicT_eval, orbitConicZeta_eval]
  refine ⟨⟨z, hpolynomial, hz, hfirst, hsecond,
    ?_, ?_⟩⟩
  · rw [hpair]
    exact ne_of_apply_ne Prod.fst hcollision.1
  · rw [hpair]
    exact orbit_second_coordinates_not_both_zero hcollision.1
      hcollision.2.1 hcollision.2.2.1

/-- The finite chart polynomial has its exact local factorization at the
selected collision parameter. -/
theorem OrbitFiniteChartCollisionData.exists_local_factorization
    {delta : ℂ} {R : OrbitSourceForm}
    (data : OrbitFiniteChartCollisionData delta R) :
    0 < (orbitParameterDehomogenize
        (orbitConicDifference delta R)).rootMultiplicity data.parameter ∧
      ∃ quotient : ℂ[X],
        orbitParameterDehomogenize (orbitConicDifference delta R) =
            (X - C data.parameter) ^
              (orbitParameterDehomogenize
                (orbitConicDifference delta R)).rootMultiplicity
                  data.parameter * quotient ∧
          quotient.eval data.parameter ≠ 0 := by
  let p := orbitParameterDehomogenize (orbitConicDifference delta R)
  have hm : 0 < p.rootMultiplicity data.parameter :=
    (Polynomial.rootMultiplicity_pos data.polynomial_ne).2
      data.parameter_root
  let quotient := p /ₘ
    (X - C data.parameter) ^ p.rootMultiplicity data.parameter
  exact ⟨hm, quotient,
    (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq
      p data.parameter).symm,
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero
      data.parameter data.polynomial_ne⟩

end OnLeConjecture.DTwo
