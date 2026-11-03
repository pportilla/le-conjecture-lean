/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddFiniteBoundary
public import OnLeConjecture.DThree.HInvariantDescent

/-!
# The algebraic alternative for an odd hard H form

The norm count gives an affine collision unless its finite numerator root
lies at one of the two pole factors of the rational parametrization. A zero
descended difference is recorded as membership in the base ring.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial

/-- Evaluation of an odd hard decomposition in source coordinates. -/
theorem hHardOddDecomposition_eval
    (R Rzero : MvPolynomial (Fin 2) ℂ) (coefficient x t : ℂ)
    (N : ℕ)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N) :
    MvPolynomial.eval ![x, t] R =
      hFormEval x (t ^ 2) Rzero + coefficient * t ^ N := by
  rw [hdecomposition, map_add, map_mul, map_pow,
    MvPolynomial.eval_C]
  congr 1
  · simp only [hQuadraticSubstitutionForm, hFormEval,
      MvPolynomial.aeval_def]
    rw [MvPolynomial.hom_eval₂]
    congr 1
    · ext c
      simp
    · funext i
      fin_cases i
      · simp [formX]
      · simp [formT]
  · simp [formT]

/-- The odd norm count gives an affine collision or a numerator root at one
of the two finite boundary factors. -/
theorem exists_hard_odd_affine_fibre_or_norm_boundary
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference Rzero ≠ 0) :
    ∃ numerator : ℂ[X],
      numerator ≠ 0 ∧
      numerator.natDegree ≤ 10 * N ∧
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N)) ∧
      ((∃ X t T : ℂ,
          (1 : ℂ) ≠ X ∧
          hP 1 (t ^ 2) = hP X (T ^ 2) ∧
          hQ 1 (t ^ 2) = hQ X (T ^ 2) ∧
          hFormEval 1 (t ^ 2) Rzero + coefficient * t ^ N =
            hFormEval X (T ^ 2) Rzero + coefficient * T ^ N) ∨
        numerator.IsRoot (-1) ∨
        ∃ z : ℂ,
          hConicParamDenominator.IsRoot z ∧ numerator.IsRoot z) := by
  obtain ⟨numerator, hnumerator, hdegree, hrepresentation,
      halternative⟩ :=
    exists_hHardOddNorm_numerator_zero_away_or_degree_drop
      Rzero coefficient N hNodd hcoefficient hRzero hdifference
  refine ⟨numerator, hnumerator, hdegree, hrepresentation, ?_⟩
  rcases halternative with hdrop | ⟨z, hzPlus, hzMinus, hroot⟩
  · left
    obtain ⟨t, T, hdistinct, hPfiber, hQfiber, hthird⟩ :=
      exists_hard_odd_affine_fibre_of_norm_degree_drop
        Rzero coefficient N hNodd numerator hnumerator hdrop
          hrepresentation
    exact ⟨-1, t, T, hdistinct, hPfiber, hQfiber, hthird⟩
  · by_cases hprofile :
      (hPoleProfileDenominator (K := ℂ) (2 * N) (4 * N)).eval z = 0
    · rcases h_pole_profile_denominator_root_classification
        (2 * N) (4 * N) z hprofile with hz | hden
      · right
        left
        simpa [hz] using hroot
      · right
        right
        exact ⟨z, by simpa [Polynomial.IsRoot] using hden, hroot⟩
    · left
      obtain ⟨t, T, hdistinct, hPfiber, hQfiber, hthird⟩ :=
        exists_hard_odd_affine_fibre_of_norm_numerator_root
          Rzero coefficient z N hNodd numerator hrepresentation hroot
            hzPlus hzMinus hprofile
      exact ⟨RatFunc.eval (RingHom.id ℂ) z hConicParamX,
        t, T, hdistinct.symm, hPfiber, hQfiber, hthird⟩

/-- The pole boundary is excluded by oddness, so only the two roots of the
conic denominator remain beside the affine collision. -/
theorem exists_hard_odd_affine_fibre_or_finite_boundary
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference Rzero ≠ 0) :
    ∃ numerator : ℂ[X],
      numerator ≠ 0 ∧
      numerator.natDegree ≤ 10 * N ∧
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N)) ∧
      ((∃ X t T : ℂ,
          (1 : ℂ) ≠ X ∧
          hP 1 (t ^ 2) = hP X (T ^ 2) ∧
          hQ 1 (t ^ 2) = hQ X (T ^ 2) ∧
          hFormEval 1 (t ^ 2) Rzero + coefficient * t ^ N =
            hFormEval X (T ^ 2) Rzero + coefficient * T ^ N) ∨
        ∃ z : ℂ,
          hConicParamDenominator.IsRoot z ∧ numerator.IsRoot z) := by
  obtain ⟨numerator, hnumerator, hdegree, hrepresentation,
      hcollision | hpole | hboundary⟩ :=
    exists_hard_odd_affine_fibre_or_norm_boundary
      Rzero coefficient N hNodd hcoefficient hRzero hdifference
  · exact ⟨numerator, hnumerator, hdegree, hrepresentation,
      Or.inl hcollision⟩
  · exact (not_hHardOddNorm_numerator_isRoot_pole
      Rzero coefficient N hNodd hcoefficient hRzero numerator
        hrepresentation hpole).elim
  · exact ⟨numerator, hnumerator, hdegree, hrepresentation,
      Or.inr hboundary⟩

/-- Every alternative in the odd hard norm count gives an off diagonal
projective fibre pair once the descended difference is nonzero. -/
theorem exists_hard_odd_projective_fibre_of_difference_ne_zero
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference Rzero ≠ 0) :
    ∃ x t X T : ℂ,
      x ≠ X ∧
      hP x (t ^ 2) = hP X (T ^ 2) ∧
      hQ x (t ^ 2) = hQ X (T ^ 2) ∧
      hFormEval x (t ^ 2) Rzero + coefficient * t ^ N =
        hFormEval X (T ^ 2) Rzero + coefficient * T ^ N := by
  obtain ⟨numerator, _hnumerator, _hdegree, hrepresentation,
      hcollision | ⟨z, hden, hroot⟩⟩ :=
    exists_hard_odd_affine_fibre_or_finite_boundary
      Rzero coefficient N hNodd hcoefficient hRzero hdifference
  · obtain ⟨X, t, T, hdistinct, hPfiber, hQfiber, hthird⟩ :=
      hcollision
    exact ⟨1, t, X, T, hdistinct, hPfiber, hQfiber, hthird⟩
  · have hz : z ^ 2 + 2 = 0 := by
      simpa [hConicParamDenominator, Polynomial.IsRoot] using hden
    exact exists_hard_odd_finite_boundary_fibre_of_norm_numerator_root
      Rzero coefficient z N hNodd hRzero numerator hrepresentation
        hz hroot

/-- A homogeneous odd hard decomposition gives an affine collision, base
ring membership, or a norm root at a finite boundary factor. -/
theorem hHardOddDecomposition_affine_fibre_or_base_or_norm_boundary
    (R Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0) :
    Rzero ∈ Set.range (hBaseToWeightedForm ℂ) ∨
      ∃ numerator : ℂ[X],
        numerator ≠ 0 ∧
        numerator.natDegree ≤ 10 * N ∧
        hHardOddNorm Rzero coefficient N =
          algebraMap ℂ[X] (RatFunc ℂ) numerator /
            algebraMap ℂ[X] (RatFunc ℂ)
              (hPoleProfileDenominator (2 * N) (4 * N)) ∧
        ((∃ X t T : ℂ,
            (1 : ℂ) ≠ X ∧
            hP 1 (t ^ 2) = hP X (T ^ 2) ∧
            hQ 1 (t ^ 2) = hQ X (T ^ 2) ∧
            MvPolynomial.eval ![(1 : ℂ), t] R =
              MvPolynomial.eval ![X, T] R) ∨
          numerator.IsRoot (-1) ∨
          ∃ z : ℂ,
            hConicParamDenominator.IsRoot z ∧ numerator.IsRoot z) := by
  have hRzero : Rzero.IsWeightedHomogeneous hFormWeight N :=
    hHardOddDecomposition.Rzero_isWeightedHomogeneous
      hR hdecomposition
  by_cases hdifference : hConicDifference Rzero = 0
  · left
    exact hConicDifference_eq_zero_mem_base_of_isWeightedHomogeneous
      Rzero N hRzero hdifference
  · right
    obtain ⟨numerator, hnumerator, hdegree, hrepresentation,
      hcollision | hpole | hboundary⟩ :=
        exists_hard_odd_affine_fibre_or_norm_boundary
          Rzero coefficient N hNodd hcoefficient hRzero hdifference
    · refine ⟨numerator, hnumerator, hdegree, hrepresentation,
        Or.inl ?_⟩
      obtain ⟨X, t, T, hdistinct, hPfiber, hQfiber, hthird⟩ :=
        hcollision
      refine ⟨X, t, T, hdistinct, hPfiber, hQfiber, ?_⟩
      rw [hHardOddDecomposition_eval R Rzero coefficient 1 t N
          hdecomposition,
        hHardOddDecomposition_eval R Rzero coefficient X T N
          hdecomposition]
      exact hthird
    · exact ⟨numerator, hnumerator, hdegree, hrepresentation,
        Or.inr (Or.inl hpole)⟩
    · exact ⟨numerator, hnumerator, hdegree, hrepresentation,
        Or.inr (Or.inr hboundary)⟩

/-- The homogeneous odd hard alternative after excluding the pole boundary.
The remaining finite boundary consists of the two roots of `m² + 2`. -/
theorem hHardOddDecomposition_affine_fibre_or_base_or_finite_boundary
    (R Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0) :
    Rzero ∈ Set.range (hBaseToWeightedForm ℂ) ∨
      ∃ numerator : ℂ[X],
        numerator ≠ 0 ∧
        numerator.natDegree ≤ 10 * N ∧
        hHardOddNorm Rzero coefficient N =
          algebraMap ℂ[X] (RatFunc ℂ) numerator /
            algebraMap ℂ[X] (RatFunc ℂ)
              (hPoleProfileDenominator (2 * N) (4 * N)) ∧
        ((∃ X t T : ℂ,
            (1 : ℂ) ≠ X ∧
            hP 1 (t ^ 2) = hP X (T ^ 2) ∧
            hQ 1 (t ^ 2) = hQ X (T ^ 2) ∧
            MvPolynomial.eval ![(1 : ℂ), t] R =
              MvPolynomial.eval ![X, T] R) ∨
          ∃ z : ℂ,
            hConicParamDenominator.IsRoot z ∧ numerator.IsRoot z) := by
  have hRzero : Rzero.IsWeightedHomogeneous hFormWeight N :=
    hHardOddDecomposition.Rzero_isWeightedHomogeneous hR hdecomposition
  by_cases hdifference : hConicDifference Rzero = 0
  · left
    exact hConicDifference_eq_zero_mem_base_of_isWeightedHomogeneous
      Rzero N hRzero hdifference
  · right
    obtain ⟨numerator, hnumerator, hdegree, hrepresentation,
      hcollision | hboundary⟩ :=
        exists_hard_odd_affine_fibre_or_finite_boundary
          Rzero coefficient N hNodd hcoefficient hRzero hdifference
    · refine ⟨numerator, hnumerator, hdegree, hrepresentation,
        Or.inl ?_⟩
      obtain ⟨X, t, T, hdistinct, hPfiber, hQfiber, hthird⟩ :=
        hcollision
      refine ⟨X, t, T, hdistinct, hPfiber, hQfiber, ?_⟩
      rw [hHardOddDecomposition_eval R Rzero coefficient 1 t N
          hdecomposition,
        hHardOddDecomposition_eval R Rzero coefficient X T N
          hdecomposition]
      exact hthird
    · exact ⟨numerator, hnumerator, hdegree, hrepresentation,
        Or.inr hboundary⟩

/-- A homogeneous odd hard form has an off diagonal projective fibre pair
unless its descended summand belongs to the base ring. -/
theorem hHardOddDecomposition_projective_fibre_or_base
    (R Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hR : R.IsHomogeneous N)
    (hdecomposition :
      R = hQuadraticSubstitutionForm Rzero +
        MvPolynomial.C coefficient * formT ^ N)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0) :
    Rzero ∈ Set.range (hBaseToWeightedForm ℂ) ∨
      ∃ x t X T : ℂ,
        x ≠ X ∧
        hP x (t ^ 2) = hP X (T ^ 2) ∧
        hQ x (t ^ 2) = hQ X (T ^ 2) ∧
        MvPolynomial.eval ![x, t] R =
          MvPolynomial.eval ![X, T] R := by
  have hRzero : Rzero.IsWeightedHomogeneous hFormWeight N :=
    hHardOddDecomposition.Rzero_isWeightedHomogeneous hR hdecomposition
  by_cases hdifference : hConicDifference Rzero = 0
  · left
    exact hConicDifference_eq_zero_mem_base_of_isWeightedHomogeneous
      Rzero N hRzero hdifference
  · right
    obtain ⟨x, t, X, T, hdistinct, hPfiber, hQfiber, hthird⟩ :=
      exists_hard_odd_projective_fibre_of_difference_ne_zero
        Rzero coefficient N hNodd hcoefficient hRzero hdifference
    refine ⟨x, t, X, T, hdistinct, hPfiber, hQfiber, ?_⟩
    rw [hHardOddDecomposition_eval R Rzero coefficient x t N
        hdecomposition,
      hHardOddDecomposition_eval R Rzero coefficient X T N
        hdecomposition]
    exact hthird

end OnLeConjecture.DThree
