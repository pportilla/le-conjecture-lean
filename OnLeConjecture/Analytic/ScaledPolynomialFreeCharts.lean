/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupPolynomial
public import OnLeConjecture.Analytic.FreeChainStraightening
public import OnLeConjecture.Analytic.MonicWeierstrassInitialForm
public import OnLeConjecture.Analytic.DepressedCubicCoefficientOrder
import Mathlib.Tactic

/-!
# Free chart transforms of a root-scaled analytic polynomial

The identities concern convergent analytic germs. At the final scaling
level, a squarefree residue polynomial makes every vanishing finite
chart smooth. At an earlier level, every vanishing finite chart is
centered at zero and the transformed polynomial retains its full order.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem pullback_polynomialEvaluation_of_coordinates
    (B : PointedMapGerm 2 2) (z : Germ 2)
    (hx : B.pullbackRingHom (coordinate (0 : Fin 2)) = z)
    (ha : ∀ a, B.pullbackRingHom (hyperplaneExtension 1 a) = hyperplaneExtension 1 a)
    (P : Polynomial (Germ 1)) :
    B.pullbackRingHom (firstCoordinatePolynomialEvaluation P) =
      P.eval₂ (hyperplaneExtension 1) z := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [firstCoordinatePolynomialEvaluation, eval₂_add, map_add] using
        congrArg₂ (· + ·) hP hQ
  | monomial n a =>
      simp only [firstCoordinatePolynomialEvaluation, eval₂_monomial, map_mul, map_pow,
        hx, ha]

/-- Substitution through a specified free chart cancels the exact
exceptional power in the root-scaled polynomial. -/
theorem pullback_scaled_polynomial_of_coordinates
    (A : Polynomial (Germ 1)) (a j : ℕ) (hj : j ≤ a) (c : ℂ)
    (B : PointedMapGerm 2 2)
    (hx : B.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (1 : Fin 2) ^ j * (coordinate (0 : Fin 2) + constRingHom 2 c))
    (ha : ∀ b, B.pullbackRingHom (hyperplaneExtension 1 b) = hyperplaneExtension 1 b) :
    B.pullbackRingHom
        (firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1) ^ a))) =
      coordinate (1 : Fin 2) ^ (A.natDegree * j) *
        firstCoordinatePolynomialEvaluation
          (rootTranslation (A.scaleRoots (coordinate (0 : Fin 1) ^ (a - j))) c) := by
  rw [pullback_polynomialEvaluation_of_coordinates B _ hx ha]
  have hsplit : A.scaleRoots (coordinate (0 : Fin 1) ^ a) =
      (A.scaleRoots (coordinate (0 : Fin 1) ^ (a - j))).scaleRoots
        (coordinate (0 : Fin 1) ^ j) := by
    rw [← scaleRoots_mul, ← pow_add, Nat.sub_add_cancel hj]
  rw [hsplit]
  have hy : coordinate (1 : Fin 2) ^ j =
      hyperplaneExtension 1 (coordinate (0 : Fin 1) ^ j) := by
    rw [map_pow, hyperplaneExtension_coordinate_plane]
  rw [hy, scaleRoots_eval₂_mul, map_pow, hyperplaneExtension_coordinate_plane,
    natDegree_scaleRoots, ← pow_mul, Nat.mul_comm j A.natDegree]
  congr 1
  simp only [firstCoordinatePolynomialEvaluation, rootTranslation, taylor_apply,
    eval₂_comp, eval₂_add, eval₂_X, eval₂_C]
  congr 2

theorem freeChain_pullback_scaled_polynomial
    (A : Polynomial (Germ 1)) (a j : ℕ) (hj : j ≤ a) :
    (freeChainChartGerm j).pullbackRingHom
        (firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1) ^ a))) =
      coordinate (1 : Fin 2) ^ (A.natDegree * j) *
        firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1) ^ (a - j))) := by
  simpa only [map_zero, add_zero, rootTranslation, taylor_zero] using
    pullback_scaled_polynomial_of_coordinates A a j hj 0 (freeChainChartGerm j)
      (by simpa only [map_zero, add_zero] using freeChainChartGerm_pullback_zero j)
      (freeChainChartGerm_pullback_hyperplaneExtension j)

/-- A positive number of free blowups, with the last finite chart
translated to the specified exceptional center. -/
@[expose] noncomputable def centeredFreeChartGerm (j : ℕ) (c : ℂ) : PointedMapGerm 2 2 :=
  (freeChainChartGerm (j - 1)).comp (pointBlowupChartGerm c)

theorem centeredFreeChartGerm_pullback_zero (j : ℕ) (hj : 0 < j) (c : ℂ) :
    (centeredFreeChartGerm j c).pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (1 : Fin 2) ^ j * (coordinate (0 : Fin 2) + constRingHom 2 c) := by
  rw [centeredFreeChartGerm, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    freeChainChartGerm_pullback_zero, map_mul, map_pow,
    pointBlowupChartGerm_pullback_one, pointBlowupChartGerm_pullback_zero,
    ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hj]

theorem centeredFreeChartGerm_pullback_hyperplaneExtension
    (j : ℕ) (c : ℂ) (b : Germ 1) :
    (centeredFreeChartGerm j c).pullbackRingHom (hyperplaneExtension 1 b) =
      hyperplaneExtension 1 b := by
  rw [centeredFreeChartGerm, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    freeChainChartGerm_pullback_hyperplaneExtension,
    pointBlowupChart_pullback_hyperplaneExtension]

theorem centeredFreeChain_pullback_scaled_polynomial
    (A : Polynomial (Germ 1)) (a j : ℕ) (hjpos : 0 < j) (hj : j ≤ a) (c : ℂ) :
    (centeredFreeChartGerm j c).pullbackRingHom
        (firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1) ^ a))) =
      coordinate (1 : Fin 2) ^ (A.natDegree * j) *
        firstCoordinatePolynomialEvaluation
          (rootTranslation (A.scaleRoots (coordinate (0 : Fin 1) ^ (a - j))) c) :=
  pullback_scaled_polynomial_of_coordinates A a j hj c (centeredFreeChartGerm j c)
    (centeredFreeChartGerm_pullback_zero j hjpos c)
    (centeredFreeChartGerm_pullback_hyperplaneExtension j c)

theorem scaled_polynomial_residue_of_pos
    (A : Polynomial (Germ 1)) (hA : A.Monic) (d : ℕ) (hd : 0 < d) :
    (A.scaleRoots (coordinate (0 : Fin 1) ^ d)).map (valueRingHom 1) = X ^ A.natDegree := by
  rw [map_scaleRoots A _ _ (by rw [hA.leadingCoeff, map_one]; exact one_ne_zero),
    map_pow, valueRingHom_coordinate, zero_pow hd.ne', scaleRoots_zero,
    (hA.map _).leadingCoeff, one_smul, hA.natDegree_map]

/-- A positive scaling level retains ordinary order at least the monic
degree, including arbitrary analytic coefficients. -/
theorem scaled_polynomialEvaluation_mem_degree
    (A : Polynomial (Germ 1)) (d : ℕ) (hd : 0 < d) :
    firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1) ^ d)) ∈
      maximalIdeal 2 ^ A.natDegree := by
  apply (mem_weightedOrderIdeal_one_iff _ _).mp
  apply firstCoordinatePolynomialEvaluation_mem_weightedOrderIdeal 1 _ (by decide)
  intro i
  rw [coeff_scaleRoots, ← pow_mul]
  have hpow : coordinate (0 : Fin 1) ^ (d * (A.natDegree - i)) ∈
      maximalIdeal 1 ^ (A.natDegree - i) := by
    exact Ideal.pow_le_pow_right (by nlinarith : A.natDegree - i ≤ d * (A.natDegree - i))
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) _)
  simpa only [one_mul] using (maximalIdeal 1 ^ (A.natDegree - i)).mul_mem_left _ hpow

/-- A simple residue root is a smooth point of the convergent polynomial
evaluation translated to that root. -/
theorem rootTranslation_not_mem_square_of_squarefree_residue
    (A : Polynomial (Germ 1)) (hsquare : Squarefree (A.map (valueRingHom 1)))
    (c : ℂ) (hroot : (A.map (valueRingHom 1)).eval c = 0) :
    firstCoordinatePolynomialEvaluation (rootTranslation A c) ∉ maximalIdeal 2 ^ 2 := by
  intro hmem
  have hderiv := partialDerivative_mem_maximalIdeal_pow_of_mem_pow_succ (0 : Fin 2) hmem
  have hvalue := mem_maximalIdeal_iff.mp (by simpa only [pow_one] using hderiv)
  rw [partialDerivative_firstCoordinatePolynomialEvaluation,
    value_firstCoordinatePolynomialEvaluation, ← derivative_map,
    rootTranslation_residue, ← coeff_zero_eq_eval_zero, coeff_derivative,
    zero_add, Nat.cast_zero, zero_add, mul_one, taylor_coeff_one] at hvalue
  have hsep := PerfectField.separable_iff_squarefree.mpr hsquare
  exact hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) hroot hvalue

theorem not_mem_pow_of_unit_multiple
    (T u : Germ 2) (hu : IsUnit u) (k : ℕ) (hT : T ∉ maximalIdeal 2 ^ k) :
    T * u ∉ maximalIdeal 2 ^ k := by
  intro h
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hmul := (maximalIdeal 2 ^ k).mul_mem_right v h
  rw [mul_assoc, hv, mul_one] at hmul
  exact hT hmul

theorem firstAxis_pullback_hyperplaneExtension (a : Germ 1) :
    pointBlowupExceptionalLine.pullbackRingHom (hyperplaneExtension 1 a) =
      constRingHom 1 (valueRingHom 1 a) := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFunction a
  rw [hyperplaneExtension_ofFunction, PointedMapGerm.pullbackRingHom_apply]
  change compPointed _ (PointedMapGerm.ofFunction _ _ _) = _
  rw [compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [] with z
  change f (hyperplaneTail 1 (![z 0, 0] : Source 2)) = f 0
  congr 1
  ext i
  fin_cases i
  rfl

theorem firstAxis_pullback_polynomialEvaluation (A : Polynomial (Germ 1)) :
    pointBlowupExceptionalLine.pullbackRingHom (firstCoordinatePolynomialEvaluation A) =
      oneVariablePolynomialEvaluation (A.map (valueRingHom 1)) := by
  induction A using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [firstCoordinatePolynomialEvaluation, eval₂_add, map_add,
        oneVariablePolynomialEvaluation, Polynomial.map_add] using congrArg₂ (· + ·) hP hQ
  | monomial n a =>
      simp only [firstCoordinatePolynomialEvaluation, eval₂_monomial, map_mul, map_pow,
        firstAxis_pullback_hyperplaneExtension, pointBlowupExceptionalLine_pullback_zero,
        oneVariablePolynomialEvaluation, map_monomial, aeval_def, eval₂_monomial]
      rfl

theorem scaled_polynomial_first_axis
    (A : Polynomial (Germ 1)) (hA : A.Monic) (d : ℕ) (hd : 0 < d) :
    pointBlowupExceptionalLine.pullbackRingHom
        (firstCoordinatePolynomialEvaluation (A.scaleRoots (coordinate (0 : Fin 1) ^ d))) =
      coordinate (0 : Fin 1) ^ A.natDegree := by
  rw [firstAxis_pullback_polynomialEvaluation, scaled_polynomial_residue_of_pos A hA d hd]
  simp only [oneVariablePolynomialEvaluation, map_pow, aeval_X]

private theorem infinity_chart_second_axis (f : Germ 2) :
    hyperplaneRestriction 1 ((pointBlowupChartGerm 0).pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)) =
    pointBlowupExceptionalLine.pullbackRingHom f := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  change compPointed (compPointed (compPointed (ofFunction F hF)
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward) (pointBlowupChartGerm 0))
    (hyperplaneInclusionGerm 1) = compPointed (ofFunction F hF) pointBlowupExceptionalLine
  simp only [coordinateSwapPointedEquiv, pointedEquivGermOfContinuousLinearEquiv,
    pointBlowupChartGerm, hyperplaneInclusionGerm, pointBlowupExceptionalLine,
    compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  refine Filter.Eventually.of_forall fun t ↦ ?_
  change F (coordinateSwapEquiv (1 : Fin 2)
    (pointBlowupChart 0 (hyperplaneInclusion 1 t))) = F (![t 0, 0])
  congr 1
  ext i
  fin_cases i
  · simp [coordinateSwapEquiv_apply_zero, pointBlowupChart, hyperplaneInclusion]
    rfl
  · change (Equiv.piCongrLeft (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1)
      (pointBlowupChart 0 (hyperplaneInclusion 1 t))) 1 = 0
    simp [Equiv.piCongrLeft, pointBlowupChart, hyperplaneInclusion]

/-- A unit first-axis coefficient of exact order `m` excludes any
positive-order strict transform at the complementary point. -/
theorem no_infinity_child_of_first_axis_order
    (m : ℕ) (f g u : Germ 2) (hu : IsUnit u)
    (haxis : pointBlowupExceptionalLine.pullbackRingHom f =
      coordinate (0 : Fin 1) ^ m * pointBlowupExceptionalLine.pullbackRingHom u)
    (htransform : (pointBlowupChartGerm 0).pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) =
        coordinate (1 : Fin 2) ^ m * g)
    (hg : g ∈ maximalIdeal 2) : False := by
  have h := congrArg (hyperplaneRestriction 1) htransform
  have hy : hyperplaneRestriction 1 (coordinate (1 : Fin 2)) =
      coordinate (0 : Fin 1) := by
    convert hyperplaneRestriction_coordinate_succ 1 (0 : Fin 1) using 1
    congr 2
  rw [infinity_chart_second_axis, haxis, map_mul, map_pow, hy] at h
  have heq := mul_left_cancel₀ (pow_ne_zero m coordinate_zero_ne_zero) h
  have hv := congrArg (valueRingHom 1) heq
  rw [hyperplaneRestriction, PointedMapGerm.valueRingHom_pullback,
    PointedMapGerm.valueRingHom_pullback, mem_maximalIdeal_iff.mp hg] at hv
  exact (valueRingHom_ne_zero_of_isUnit hu) hv

end OnLeConjecture.Analytic.Germ
