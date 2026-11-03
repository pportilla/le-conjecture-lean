/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.InitialCollision
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneity of the residual initial map

The collision calculation in `DTwo.InitialCollision` uses only the values of
the prepared family.  Weighted radial rescaling also requires compatibility
between the polynomial variable and its parameter.  This file records that
compatibility by a bivariate polynomial of weights `![1, 2]` and proves the
scaling law for the residual initial map with source weights `![L, 2]`.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- Specialize the second variable of a bivariate polynomial while retaining
the first variable as a polynomial variable. -/
noncomputable def parameterSpecialization
    (P : MvPolynomial (Fin 2) ℂ) (T : ℂ) : _root_.Polynomial ℂ :=
  MvPolynomial.eval₂Hom _root_.Polynomial.C
    ![_root_.Polynomial.X, _root_.Polynomial.C T] P

@[simp]
theorem parameterSpecialization_eval
    (P : MvPolynomial (Fin 2) ℂ) (T x : ℂ) :
    (parameterSpecialization P T).eval x = MvPolynomial.eval ![x, T] P := by
  rw [parameterSpecialization, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.polynomial_eval_eval₂]
  have hscalar :
      (_root_.Polynomial.evalRingHom x).comp _root_.Polynomial.C =
        RingHom.id ℂ := by
    ext a
    simp
  rw [hscalar, MvPolynomial.eval₂_id]
  have hcoordinates :
      (fun i : Fin 2 ↦ _root_.Polynomial.eval x
        (![_root_.Polynomial.X, _root_.Polynomial.C T] i)) = ![x, T] := by
    funext i
    fin_cases i <;> simp
  rw [hcoordinates]

/-- A bivariate polynomial whose specialization is the prepared odd family
and whose variables have weights one and two. -/
structure PreparedOddFamily.BivariateModel
    {N : ℕ} (Psi : PreparedOddFamily N) where
  polynomial : MvPolynomial (Fin 2) ℂ
  specialization : ∀ T,
    Psi.polynomial T = parameterSpecialization polynomial T
  weightedHomogeneous :
    polynomial.IsWeightedHomogeneous ![1, 2] N

/-- The bivariate polynomial determined by coefficients of the terms
`X ^ (N - 2 * h) * T ^ h`. -/
@[expose]
noncomputable def preparedOddBivariatePolynomial
    (N : ℕ) (alpha : ℕ → ℂ) : MvPolynomial (Fin 2) ℂ :=
  ∑ h ∈ Finset.range (N / 2 + 1),
    MvPolynomial.C (alpha h) *
      MvPolynomial.X 0 ^ (N - 2 * h) * MvPolynomial.X 1 ^ h

/-- Every term in the coefficient formula has bivariate weighted degree
`N` for weights `![1, 2]`. -/
theorem preparedOddBivariatePolynomial_isWeightedHomogeneous
    (N : ℕ) (alpha : ℕ → ℂ) :
    (preparedOddBivariatePolynomial N alpha).IsWeightedHomogeneous
      ![1, 2] N := by
  classical
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro h hh
  have hhLe : h ≤ N / 2 := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hh
  have htwo : 2 * h ≤ N := by
    omega
  have hc := MvPolynomial.isWeightedHomogeneous_C
    (![1, 2] : Fin 2 → ℕ) (alpha h)
  have hx := MvPolynomial.isWeightedHomogeneous_X
    ℂ (![1, 2] : Fin 2 → ℕ) (0 : Fin 2)
  have hT := MvPolynomial.isWeightedHomogeneous_X
    ℂ (![1, 2] : Fin 2 → ℕ) (1 : Fin 2)
  have hproduct := (hc.mul (hx.pow (N - 2 * h))).mul (hT.pow h)
  have hdegree :
      0 + (N - 2 * h) • (![1, 2] (0 : Fin 2)) +
          h • (![1, 2] (1 : Fin 2)) = N := by
    simp
    omega
  rw [hdegree] at hproduct
  exact hproduct

/-- Specializing the parameter of the bivariate coefficient formula gives
the corresponding univariate polynomial. -/
theorem parameterSpecialization_preparedOddBivariatePolynomial
    (N : ℕ) (alpha : ℕ → ℂ) (T : ℂ) :
    parameterSpecialization (preparedOddBivariatePolynomial N alpha) T =
      ∑ h ∈ Finset.range (N / 2 + 1),
        _root_.Polynomial.C (alpha h * T ^ h) *
          _root_.Polynomial.X ^ (N - 2 * h) := by
  classical
  simp [parameterSpecialization, preparedOddBivariatePolynomial, mul_comm,
    mul_left_comm]

/-- The coefficient formula occurring in the prepared odd polynomial. -/
def PreparedOddFamily.HasCoefficientFormula
    {N : ℕ} (Psi : PreparedOddFamily N) (alpha : ℕ → ℂ) : Prop :=
  ∀ T,
    Psi.polynomial T =
      ∑ h ∈ Finset.range (N / 2 + 1),
        _root_.Polynomial.C (alpha h * T ^ h) *
          _root_.Polynomial.X ^ (N - 2 * h)

/-- The explicit coefficient formula produces the bivariate model needed
for weighted radial rescaling. -/
noncomputable def PreparedOddFamily.BivariateModel.ofCoefficientFormula
    {N : ℕ} {Psi : PreparedOddFamily N} {alpha : ℕ → ℂ}
    (hformula : Psi.HasCoefficientFormula alpha) : Psi.BivariateModel where
  polynomial := preparedOddBivariatePolynomial N alpha
  specialization T := by
    rw [hformula T,
      parameterSpecialization_preparedOddBivariatePolynomial]
  weightedHomogeneous :=
    preparedOddBivariatePolynomial_isWeightedHomogeneous N alpha

/-- The residual initial map with an exported formula for use in weighted
radial rescaling. -/
@[expose]
noncomputable def residualWeightedInitialMap
    (k L N : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.2 ^ k,
    -c * (z.1 ^ 2 + T * z.2 ^ L),
    (Psi.polynomial (T * z.2 ^ L)).eval z.1]

/-- Evaluation of a weighted homogeneous polynomial commutes with scaling
each variable by its weight. -/
theorem eval_weighted_smul_of_isWeightedHomogeneous
    {P : MvPolynomial (Fin 2) ℂ} {w : Fin 2 → ℕ} {D : ℕ}
    (hP : P.IsWeightedHomogeneous w D) (lambda : ℂ) (z : Fin 2 → ℂ) :
    MvPolynomial.eval (fun i ↦ lambda ^ w i * z i) P =
      lambda ^ D * MvPolynomial.eval z P := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [MvPolynomial.eval_add, ihp, ihq, mul_add]
  | monomial d c hd =>
      rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      rw [Finsupp.prod_pow, Finsupp.prod_pow]
      simp_rw [mul_pow, ← pow_mul]
      rw [Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
      have hsum : ∑ i, w i * d i = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
      rw [hsum]
      ring

/-- A bivariate model supplies the joint scaling identity required by the
weighted radial substitution. -/
theorem PreparedOddFamily.BivariateModel.eval_scaled
    {N : ℕ} {Psi : PreparedOddFamily N}
    (model : Psi.BivariateModel) (lambda T x : ℂ) :
    (Psi.polynomial (lambda ^ 2 * T)).eval (lambda * x) =
      lambda ^ N * (Psi.polynomial T).eval x := by
  rw [model.specialization, model.specialization]
  simp only [parameterSpecialization_eval]
  have hcoordinates :
      ![lambda * x, lambda ^ 2 * T] =
        fun i : Fin 2 ↦ lambda ^ (![1, 2] i) * (![x, T] i) := by
    funext i
    fin_cases i <;> simp
  rw [hcoordinates]
  exact eval_weighted_smul_of_isWeightedHomogeneous
    model.weightedHomogeneous lambda ![x, T]

/-- Weighted radial substitution with source weights `(L, 2)`. -/
@[expose]
noncomputable def residualWeightedRadialSource
    (L : ℕ) (lambda : ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (lambda ^ L * z.1, lambda ^ 2 * z.2)

/-- The target degrees of the three coordinates of the residual initial
map. -/
@[expose]
noncomputable def residualWeightedDegrees
    (k L N : ℕ) : Fin 3 → ℕ :=
  ![2 * k, 2 * L, N * L]

/-- Weighted homogeneity for a map with source weights `(L, 2)` and three
specified target degrees. -/
def IsResidualWeightedHomogeneousMap
    (L : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap : ℂ × ℂ → Fin 3 → ℂ) : Prop :=
  ∀ lambda z i,
    initialMap (residualWeightedRadialSource L lambda z) i =
      lambda ^ degrees i * initialMap z i

/-- The bivariate scaling law for the prepared family makes every coordinate
of the residual initial map weighted homogeneous. -/
theorem residualWeightedInitialMap_isResidualWeightedHomogeneous
    (k L N : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (model : Psi.BivariateModel) :
    IsResidualWeightedHomogeneousMap L (residualWeightedDegrees k L N)
      (residualWeightedInitialMap k L N c T Psi) := by
  intro lambda z i
  fin_cases i
  · simp [residualWeightedInitialMap, residualWeightedRadialSource,
      residualWeightedDegrees, mul_pow, pow_mul]
  · simp [residualWeightedInitialMap, residualWeightedRadialSource,
      residualWeightedDegrees, pow_mul]
    ring
  · have hparameter :
        T * (lambda ^ 2 * z.2) ^ L =
          (lambda ^ L) ^ 2 * (T * z.2 ^ L) := by
        simp only [mul_pow]
        ring
    simp only [residualWeightedInitialMap, residualWeightedRadialSource,
      residualWeightedDegrees]
    rw [hparameter, model.eval_scaled]
    simp [pow_mul, Nat.mul_comm]

/-- The explicit coefficient formula is sufficient for the weighted
homogeneity of the residual initial map. -/
theorem residualWeightedInitialMap_isResidualWeightedHomogeneous_ofCoefficientFormula
    (k L N : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (alpha : ℕ → ℂ) (hformula : Psi.HasCoefficientFormula alpha) :
    IsResidualWeightedHomogeneousMap L (residualWeightedDegrees k L N)
      (residualWeightedInitialMap k L N c T Psi) :=
  residualWeightedInitialMap_isResidualWeightedHomogeneous k L N c T Psi
    (.ofCoefficientFormula hformula)

/-- The collision certificate for the residual calculation also gives equal
values for the map whose formula is exported in this file. -/
theorem InitialCollisionCertificate.residualWeightedInitialMap_values_eq
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (certificate : InitialCollisionCertificate k L N c T Psi) :
    residualWeightedInitialMap k L N c T Psi (certificate.x, 1) =
      residualWeightedInitialMap k L N c T Psi
        (-certificate.x, certificate.eta) := by
  have hpositive : (2 : ℂ) ≠ 0 := by norm_num
  have hxRoot : (Psi.polynomial T).eval certificate.x = 0 := by
    have hzero := certificate.third_difference_zero
    rw [restrictedThirdDifference_eq_two_mul] at hzero
    simpa [hpositive] using hzero
  have hnegRoot : (Psi.polynomial T).eval (-certificate.x) = 0 := by
    rw [Psi.eval_neg, hxRoot, neg_zero]
  funext i
  fin_cases i
  · simp [residualWeightedInitialMap, certificate.eta_pow_k]
  · simp [residualWeightedInitialMap, certificate.eta_pow_L]
  · simp [residualWeightedInitialMap, certificate.eta_pow_L,
      hxRoot, hnegRoot]

/-- Under the hypotheses of the residual collision theorem, the exported
initial map is weighted homogeneous and has the certified collision. -/
theorem exists_weightedHomogeneousInitialCollision
    (a k L N : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (model : Psi.BivariateModel)
    (ha : 2 ≤ a) (hk : k = 2 * a) (haL : a ∣ L)
    (hN : 3 ≤ N) (hc : c ≠ 0) (hT : T ≠ 0) :
    ∃ certificate : InitialCollisionCertificate k L N c T Psi,
      IsResidualWeightedHomogeneousMap L (residualWeightedDegrees k L N)
        (residualWeightedInitialMap k L N c T Psi) ∧
      residualWeightedInitialMap k L N c T Psi (certificate.x, 1) =
        residualWeightedInitialMap k L N c T Psi
          (-certificate.x, certificate.eta) := by
  obtain ⟨certificate⟩ :=
    exists_initialCollisionCertificate a k L N c T Psi
      ha hk haL hN hc hT
  exact ⟨certificate,
    residualWeightedInitialMap_isResidualWeightedHomogeneous
      k L N c T Psi model,
    certificate.residualWeightedInitialMap_values_eq⟩

end OnLeConjecture.DTwo
