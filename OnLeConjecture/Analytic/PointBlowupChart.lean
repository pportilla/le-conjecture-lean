/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrdinaryWeightedOrder
public import OnLeConjecture.Analytic.WeightedInitialFormExistence
public import OnLeConjecture.Analytic.DepressedCubicCoefficientOrder
public import OnLeConjecture.Analytic.PolynomialJets
public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

/-!
# Analytic point blowup charts

The pointed chart map is `(x,y) ↦ (y*(x+c),y)`. Pullback of a germ of
ordinary order at least `m` is divisible by `y^m` in the analytic germ
ring. Its quotient restricts to the translated chart polynomial of the
degree-`m` ordinary initial form. For exact order `m`, that polynomial is
nonzero and has degree at most `m`, proving that the transformed germ has
order at most `m`. The case `m=0` is included.
-/

public section

namespace OnLeConjecture.Analytic

open Filter _root_.Polynomial
open scoped Topology

namespace Germ

/-- The local point blowup chart centered at exceptional coordinate `c`. -/
@[expose] noncomputable def pointBlowupChart (c : ℂ) (z : Source 2) : Source 2 :=
  ![z 1 * (z 0 + c), z 1]

theorem pointBlowupChart_analyticAt (c : ℂ) : AnalyticAt ℂ (pointBlowupChart c) 0 := by
  apply AnalyticAt.pi
  intro i
  have hzero := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
  have hone := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
  fin_cases i
  · exact hone.mul (hzero.add analyticAt_const)
  · exact hone

@[simp] theorem pointBlowupChart_zero (c : ℂ) : pointBlowupChart c 0 = 0 := by
  ext i
  fin_cases i <;> simp [pointBlowupChart]

/-- The actual pointed analytic germ of the point blowup chart. -/
@[expose] noncomputable def pointBlowupChartGerm (c : ℂ) : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (pointBlowupChart c) (pointBlowupChart_analyticAt c)
    (pointBlowupChart_zero c)

@[simp] theorem pointBlowupChartGerm_pullback_zero (c : ℂ) :
    (pointBlowupChartGerm c).pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (1 : Fin 2) * (coordinate (0 : Fin 2) + constRingHom 2 c) := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  exact MapGerm.component_ofFunction (pointBlowupChart c) (pointBlowupChart_analyticAt c) 0

@[simp] theorem pointBlowupChartGerm_pullback_one (c : ℂ) :
    (pointBlowupChartGerm c).pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinate (1 : Fin 2) := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  exact MapGerm.component_ofFunction (pointBlowupChart c) (pointBlowupChart_analyticAt c) 1

/-- The inclusion of the exceptional coordinate line `y=0`. -/
@[expose] noncomputable def pointBlowupExceptionalLine : PointedMapGerm 1 2 :=
  PointedMapGerm.ofFunction (fun t : Source 1 ↦ ![t 0, 0])
    (by
      apply AnalyticAt.pi
      intro i
      fin_cases i
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0
      · exact analyticAt_const)
    (by ext i; fin_cases i <;> rfl)

@[simp] theorem pointBlowupExceptionalLine_pullback_zero :
    pointBlowupExceptionalLine.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (0 : Fin 1) := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [pointBlowupExceptionalLine, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

@[simp] theorem pointBlowupExceptionalLine_pullback_one :
    pointBlowupExceptionalLine.pullbackRingHom (coordinate (1 : Fin 2)) = 0 := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [pointBlowupExceptionalLine, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

/-- The blowup chart maps the whole exceptional line to the old origin. -/
theorem pointBlowupExceptionalLine_pullback_chart (c : ℂ) (f : Germ 2) :
    pointBlowupExceptionalLine.pullbackRingHom
      ((pointBlowupChartGerm c).pullbackRingHom f) = constRingHom 1 (valueRingHom 2 f) := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  change compPointed (compPointed (ofFunction F hF) (pointBlowupChartGerm c))
    pointBlowupExceptionalLine = _
  simp only [pointBlowupChartGerm, pointBlowupExceptionalLine,
    compPointed_ofFunction, valueRingHom_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Eventually.of_forall fun t ↦ by
    change F (pointBlowupChart c (![t 0, 0])) = F 0
    congr 1
    ext i
    fin_cases i <;> simp [pointBlowupChart]

/-- Evaluation of a univariate complex polynomial at the one-variable
analytic coordinate. -/
@[expose] noncomputable def oneVariablePolynomialEvaluation : ℂ[X] →ₐ[ℂ] Germ 1 :=
  Polynomial.aeval (coordinate (0 : Fin 1))

/-- Taylor expansion of a coordinate polynomial is the same polynomial,
viewed as a formal power series. -/
theorem oneVariableTaylor_polynomialEvaluation (P : ℂ[X]) :
    oneVariableTaylorRingHom (oneVariablePolynomialEvaluation P) = (P : PowerSeries ℂ) := by
  have heq : oneVariableTaylorAlgHom.comp oneVariablePolynomialEvaluation =
      Polynomial.coeToPowerSeries.algHom ℂ := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, oneVariablePolynomialEvaluation, Polynomial.aeval_X]
    change oneVariableTaylorRingHom (coordinate (0 : Fin 1)) =
      ((X : ℂ[X]) : PowerSeries ℂ)
    rw [Polynomial.coe_X]
    exact oneVariableTaylorSeries_coordinate_eq_X
  exact AlgHom.congr_fun heq P

/-- A nonzero polynomial of degree at most `m` cannot vanish to analytic
order `m+1` at the origin. -/
theorem oneVariablePolynomialEvaluation_not_mem_pow
    (m : ℕ) (P : ℂ[X]) (hP : P ≠ 0) (hdegree : P.natDegree ≤ m) :
    oneVariablePolynomialEvaluation P ∉ maximalIdeal 1 ^ (m + 1) := by
  intro hmem
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hmem
  have hdiv := map_dvd oneVariableTaylorRingHom hmem
  rw [map_pow, oneVariableTaylorRingHom_apply,
    oneVariableTaylorSeries_coordinate_eq_X, oneVariableTaylor_polynomialEvaluation] at hdiv
  have hcoeff := (PowerSeries.X_pow_dvd_iff.mp hdiv) P.natDegree (by omega)
  apply hP
  apply Polynomial.leadingCoeff_eq_zero.mp
  simpa only [Polynomial.coeff_coe, Polynomial.coeff_natDegree] using hcoeff

/-- Each ordinary degree-`m` monomial has exceptional factor `y^m` in
the chart. -/
theorem pointBlowupChart_pullback_generator
    (c : ℂ) (m : ℕ) (k : Fin (m + 1)) :
    (pointBlowupChartGerm c).pullbackRingHom (weightedOrderGenerator 1 m k) =
      coordinate (1 : Fin 2) ^ m *
        (coordinate (0 : Fin 2) + constRingHom 2 c) ^ k.1 := by
  simp only [weightedOrderGenerator, one_mul, map_mul, map_pow,
    pointBlowupChartGerm_pullback_zero, pointBlowupChartGerm_pullback_one, mul_pow]
  calc
    coordinate (1 : Fin 2) ^ k.1 * (coordinate (0 : Fin 2) + constRingHom 2 c) ^ k.1 *
        coordinate (1 : Fin 2) ^ (m - k.1) =
      (coordinate (1 : Fin 2) ^ k.1 * coordinate (1 : Fin 2) ^ (m - k.1)) *
        (coordinate (0 : Fin 2) + constRingHom 2 c) ^ k.1 := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le (show k.1 ≤ m by omega)]

/-- The pullback of an analytic germ of order at least `m` is divisible
by `y^m` in the analytic germ ring, including `m=0`. -/
theorem exists_pointBlowupChart_factor
    (c : ℂ) (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) :
    ∃ g : Germ 2, (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g := by
  have hfweight : f ∈ weightedOrderIdeal 1 m := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf
  obtain ⟨a, ha⟩ := (mem_weightedOrderIdeal_iff 1 m f).mp hfweight
  refine ⟨∑ k, (pointBlowupChartGerm c).pullbackRingHom (a k) *
    (coordinate (0 : Fin 2) + constRingHom 2 c) ^ k.1, ?_⟩
  rw [← ha, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, pointBlowupChart_pullback_generator]
  ring

private theorem coefficient_sum_C_mul_X_pow
    (m : ℕ) (a : Fin (m + 1) → ℂ) (k : Fin (m + 1)) :
    (∑ j : Fin (m + 1), C (a j) * (X : ℂ[X]) ^ j.1).coeff k.1 = a k := by
  classical
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    have hne : j.1 ≠ k.1 := fun h ↦ hj (Fin.ext h)
    simp [coeff_C_mul, coeff_X_pow, Ne.symm hne]
  · simp

private theorem constant_coefficients_not_all_zero
    (m : ℕ) (f : Germ 2) (a : Fin (m + 1) → Germ 2)
    (ha : ∑ k, a k * weightedOrderGenerator 1 m k = f)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) :
    (∑ k : Fin (m + 1), C (valueRingHom 2 (a k)) * (X : ℂ[X]) ^ k.1) ≠ 0 := by
  intro hzero
  apply hnext
  rw [← ha]
  apply (maximalIdeal 2 ^ (m + 1)).sum_mem
  intro k _
  have hak : a k ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    have h := coefficient_sum_C_mul_X_pow m (fun j ↦ valueRingHom 2 (a j)) k
    rw [hzero, coeff_zero] at h
    exact h.symm
  have hg : weightedOrderGenerator 1 m k ∈ maximalIdeal 2 ^ m := by
    rw [← weightedOrderIdeal_one_eq_maximalIdeal_pow]
    exact weightedOrderGenerator_mem 1 m k
  simpa only [pow_succ'] using Ideal.mul_mem_mul hak hg

/-- The strict transform exists analytically, and its exceptional
restriction is the translated chart of the ordinary initial polynomial.
The initial polynomial is characterized by homogeneity and congruence
modulo the next maximal-ideal power. -/
theorem exists_pointBlowupTransform_with_initial
    (c : ℂ) (m : ℕ) (f : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) :
    ∃ g : Germ 2, ∃ P : MvPolynomial (Fin 2) ℂ, ∃ T : ℂ[X],
      (pointBlowupChartGerm c).pullbackRingHom f = coordinate (1 : Fin 2) ^ m * g ∧
      P ≠ 0 ∧ P.IsWeightedHomogeneous ![1, 1] m ∧
      f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (m + 1) ∧
      T = MvPolynomial.aeval (![X + C c, 1] : Fin 2 → ℂ[X]) P ∧
      T ≠ 0 ∧ T.natDegree ≤ m ∧
      pointBlowupExceptionalLine.pullbackRingHom g = oneVariablePolynomialEvaluation T ∧
      g ∉ maximalIdeal 2 ^ (m + 1) := by
  classical
  have hfweight : f ∈ weightedOrderIdeal 1 m := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf
  obtain ⟨a, ha⟩ := (mem_weightedOrderIdeal_iff 1 m f).mp hfweight
  let A : ℂ[X] := ∑ k : Fin (m + 1), C (valueRingHom 2 (a k)) * X ^ k.1
  let T : ℂ[X] := A.taylor c
  let P : MvPolynomial (Fin 2) ℂ :=
    ∑ k : Fin (m + 1), MvPolynomial.C (valueRingHom 2 (a k)) *
      MvPolynomial.X (0 : Fin 2) ^ k.1 * MvPolynomial.X (1 : Fin 2) ^ (m - k.1)
  let g : Germ 2 := ∑ k : Fin (m + 1),
    (pointBlowupChartGerm c).pullbackRingHom (a k) *
      (coordinate (0 : Fin 2) + constRingHom 2 c) ^ k.1
  have hfactor : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g := by
    rw [← ha, map_sum]
    simp only [g, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, pointBlowupChart_pullback_generator]
    ring
  have hP : P.IsWeightedHomogeneous ![1, 1] m := by
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro k _
    have hx := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (0 : Fin 2)
    have hy := MvPolynomial.isWeightedHomogeneous_X ℂ (![1, 1] : Fin 2 → ℕ) (1 : Fin 2)
    have hterm := ((hx.pow k.1).mul (hy.pow (m - k.1))).C_mul (valueRingHom 2 (a k))
    have hk : k.1 ≤ m := by omega
    have hdegree : k.1 • (![1, 1] : Fin 2 → ℕ) 0 +
        (m - k.1) • (![1, 1] : Fin 2 → ℕ) 1 = m := by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        nsmul_eq_mul, mul_one]
      exact Nat.add_sub_of_le hk
    rw [hdegree] at hterm
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      nsmul_eq_mul, mul_one, Nat.add_sub_of_le hk, mul_assoc] using hterm
  have htail : f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (m + 1) := by
    have heq : f - coordinatePolynomialAlgHom 2 P =
        ∑ k : Fin (m + 1), (a k - constRingHom 2 (valueRingHom 2 (a k))) *
          weightedOrderGenerator 1 m k := by
      rw [← ha]
      simp only [P, map_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [map_mul, map_pow, coordinatePolynomialAlgHom_C,
        coordinatePolynomialAlgHom_X, weightedOrderGenerator, one_mul]
      ring
    rw [heq]
    apply (maximalIdeal 2 ^ (m + 1)).sum_mem
    intro k _
    have hak : a k - constRingHom 2 (valueRingHom 2 (a k)) ∈ maximalIdeal 2 := by
      simp [mem_maximalIdeal_iff]
    have hg : weightedOrderGenerator 1 m k ∈ maximalIdeal 2 ^ m := by
      rw [← weightedOrderIdeal_one_eq_maximalIdeal_pow]
      exact weightedOrderGenerator_mem 1 m k
    simpa only [pow_succ'] using Ideal.mul_mem_mul hak hg
  have hPne : P ≠ 0 := by
    intro hzero
    exact hnext (by simpa only [hzero, map_zero, sub_zero] using htail)
  have hA : A ≠ 0 := constant_coefficients_not_all_zero m f a ha hnext
  have hT : T ≠ 0 := (Polynomial.taylor_eq_zero c A).not.mpr hA
  have hAdegree : A.natDegree ≤ m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (by simpa only [natDegree_X_pow] using (show k.1 ≤ m by omega))
  have hTdegree : T.natDegree ≤ m := by
    simpa only [T, Polynomial.natDegree_taylor] using hAdegree
  have hTsum : T = ∑ k : Fin (m + 1),
      C (valueRingHom 2 (a k)) * (X + C c) ^ k.1 := by
    simp only [T, A, map_sum, Polynomial.taylor_mul, Polynomial.taylor_C,
      Polynomial.taylor_X_pow]
  have hchart : T = MvPolynomial.aeval (![X + C c, 1] : Fin 2 → ℂ[X]) P := by
    rw [hTsum]
    simp only [P, map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      one_pow, mul_one, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hrestriction : pointBlowupExceptionalLine.pullbackRingHom g =
      oneVariablePolynomialEvaluation T := by
    rw [hTsum]
    simp only [g, map_sum, map_mul, map_pow, pointBlowupExceptionalLine_pullback_chart,
      map_add, pointBlowupExceptionalLine_pullback_zero, PointedMapGerm.pullback_constRingHom,
      oneVariablePolynomialEvaluation, Polynomial.aeval_C, Polynomial.aeval_X,
      RingHom.algebraMap_toAlgebra]
  have hgnot : g ∉ maximalIdeal 2 ^ (m + 1) := by
    intro hg
    apply oneVariablePolynomialEvaluation_not_mem_pow m T hT hTdegree
    rw [← hrestriction]
    exact PointedMapGerm.pullback_mem_maximalIdeal_pow pointBlowupExceptionalLine hg
  exact ⟨g, P, T, hfactor, hPne, hP, htail, hchart, hT, hTdegree, hrestriction, hgnot⟩

/-- Multiplicity cannot increase at any point of this exceptional chart.
The conclusion applies to any analytic germ satisfying the strict-transform
identity, since cancellation proves that the transform is unique. -/
theorem pointBlowupTransform_not_mem_succ
    (c : ℂ) (m : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * g) :
    g ∉ maximalIdeal 2 ^ (m + 1) := by
  obtain ⟨g', P, T, hfactor, _, _, _, _, _, _, _, hg'⟩ :=
    exists_pointBlowupTransform_with_initial c m f hf hnext
  have hgg' : g = g' :=
    mul_left_cancel₀ (pow_ne_zero m (coordinate_ne_zero (1 : Fin 2)))
      (htransform.symm.trans hfactor)
  exact hgg' ▸ hg'

/-- Cancellation of the nonzero exceptional factor makes the analytic
strict transform unique. -/
theorem pointBlowupTransform_unique
    (c : ℂ) (m : ℕ) (f g h : Germ 2)
    (hg : (pointBlowupChartGerm c).pullbackRingHom f = coordinate (1 : Fin 2) ^ m * g)
    (hh : (pointBlowupChartGerm c).pullbackRingHom f = coordinate (1 : Fin 2) ^ m * h) :
    g = h :=
  mul_left_cancel₀ (pow_ne_zero m (coordinate_ne_zero (1 : Fin 2))) (hg.symm.trans hh)

/-- The analytic strict transform in this chart, defined from proved
divisibility rather than from an assumed transform certificate. -/
@[expose] noncomputable def pointBlowupTransform
    (c : ℂ) (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) : Germ 2 :=
  Classical.choose (exists_pointBlowupChart_factor c m f hf)

/-- The defining strict-transform identity holds in the analytic germ ring. -/
theorem pointBlowupTransform_factor
    (c : ℂ) (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) :
    (pointBlowupChartGerm c).pullbackRingHom f =
      coordinate (1 : Fin 2) ^ m * pointBlowupTransform c m f hf :=
  Classical.choose_spec (exists_pointBlowupChart_factor c m f hf)

/-- The constructed analytic strict transform has order at most the exact
ordinary order of the original germ. -/
theorem pointBlowupTransform_order_bound
    (c : ℂ) (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hnext : f ∉ maximalIdeal 2 ^ (m + 1)) :
    pointBlowupTransform c m f hf ∉ maximalIdeal 2 ^ (m + 1) :=
  pointBlowupTransform_not_mem_succ c m f _ hf hnext
    (pointBlowupTransform_factor c m f hf)

/-- Identification of the exceptional restriction using any prescribed
ordinary initial polynomial of `f`. -/
theorem pointBlowupTransform_exceptionalRestriction
    (c : ℂ) (m : ℕ) (f g : Germ 2) (P : MvPolynomial (Fin 2) ℂ)
    (hf : f ∈ maximalIdeal 2 ^ m) (hnext : f ∉ maximalIdeal 2 ^ (m + 1))
    (hP : P.IsWeightedHomogeneous ![1, 1] m)
    (htail : f - coordinatePolynomialAlgHom 2 P ∈ maximalIdeal 2 ^ (m + 1))
    (htransform : (pointBlowupChartGerm c).pullbackRingHom f = coordinate (1 : Fin 2) ^ m * g) :
    pointBlowupExceptionalLine.pullbackRingHom g = oneVariablePolynomialEvaluation
      (MvPolynomial.aeval (![X + C c, 1] : Fin 2 → ℂ[X]) P) := by
  obtain ⟨g', P', T, hfactor, _, hP', htail', hchart, _, _, hrestriction, _⟩ :=
    exists_pointBlowupTransform_with_initial c m f hf hnext
  have hPP' : P = P' := by
    apply sub_eq_zero.mp
    apply eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ 1 m (by decide)
      (hP.sub hP')
    rw [weightedOrderIdeal_one_eq_maximalIdeal_pow, map_sub]
    have h := (maximalIdeal 2 ^ (m + 1)).sub_mem htail' htail
    convert h using 1
    ring
  have hgg' := pointBlowupTransform_unique c m f g g' htransform hfactor
  rw [hgg', hrestriction, hchart, ← hPP']

end Germ

end OnLeConjecture.Analytic
