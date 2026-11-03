/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.BasepointFreePencilExclusion

/-!
# Linear choices for a full space of binary quadratic jets

Three independent binary quadratics can be changed by an invertible target
matrix to the ordered basis `x²,y²,xy`. In particular, the first two chosen
quadratic jets have no common projective zero.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def quadraticMonomialBasis : Fin 3 → OrbitSourceForm :=
  ![MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1]

private noncomputable def quadraticPresentationLinearMap :
    (Fin 3 → ℂ) →ₗ[ℂ] OrbitSourceForm where
  toFun v := ∑ j, v j • quadraticMonomialBasis j
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_smul, RingHom.id_apply, Finset.smul_sum, smul_eq_mul]

private noncomputable def quadraticCoefficientMatrix (P : Fin 3 → OrbitSourceForm) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i => ![binaryQuadraticCoefficients (P i) 0,
    binaryQuadraticCoefficients (P i) 2, binaryQuadraticCoefficients (P i) 1]

private theorem quadraticPresentation_coefficientMatrix
    (P : Fin 3 → OrbitSourceForm) (hP : ∀ i, (P i).IsHomogeneous 2) (i : Fin 3) :
    quadraticPresentationLinearMap ((quadraticCoefficientMatrix P).row i) = P i := by
  change (∑ j, ((quadraticCoefficientMatrix P).row i) j • quadraticMonomialBasis j) = P i
  rw [eq_binaryQuadraticForm_of_isHomogeneous (hP i)]
  simp [quadraticCoefficientMatrix, Matrix.row, Fin.sum_univ_succ, quadraticMonomialBasis,
    Algebra.smul_def, binaryQuadraticForm,
    orbitPolynomialS, orbitPolynomialLambda]
  ring

/-- The target coefficients are constructed from the inverse of the
quadratic coefficient matrix, whose nonsingularity follows from independence. -/
theorem exists_linear_quadratic_monomial_normalization
    (P : Fin 3 → OrbitSourceForm) (hP : ∀ i, (P i).IsHomogeneous 2)
    (hfull : LinearIndependent ℂ P) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℂ, A.det ≠ 0 ∧
      ∀ i, ∑ j, MvPolynomial.C (A i j) * P j = quadraticMonomialBasis i := by
  let M := quadraticCoefficientMatrix P
  have hrows : LinearIndependent ℂ M.row := by
    apply LinearIndependent.of_comp quadraticPresentationLinearMap
    have heq : quadraticPresentationLinearMap ∘ M.row = P := by
      funext i
      exact quadraticPresentation_coefficientMatrix P hP i
    rwa [heq]
  have hM : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)
  refine ⟨M⁻¹, (isUnit_iff_ne_zero.mp (M.isUnit_nonsing_inv_det hM)), ?_⟩
  intro i
  have hrow : (∑ j, (M⁻¹ i j) • M.row j) = (1 : Matrix (Fin 3) (Fin 3) ℂ).row i := by
    funext k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row, Matrix.mul_apply]
      using congrFun (congrFun (M.nonsing_inv_mul hM) i) k
  have hh := congrArg quadraticPresentationLinearMap hrow
  simp only [map_sum, map_smul] at hh
  calc
    (∑ j, MvPolynomial.C (M⁻¹ i j) * P j) =
        ∑ j, (M⁻¹ i j) • quadraticPresentationLinearMap (M.row j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [quadraticPresentation_coefficientMatrix P hP j]
      simp only [Algebra.smul_def, ← MvPolynomial.C_eq_algebraMap]
    _ = quadraticPresentationLinearMap ((1 : Matrix (Fin 3) (Fin 3) ℂ).row i) := hh
    _ = quadraticMonomialBasis i := by
      simp [quadraticPresentationLinearMap, Matrix.row, Matrix.one_apply]

/-- A full quadratic jet is put into monomial coordinates by an actual
invertible linear target change. -/
theorem exists_target_full_quadratic_monomial_normalization
    (g : PointedMapGerm 2 3) (P : Fin 3 → OrbitSourceForm)
    (hP : ∀ i, (P i).IsHomogeneous 2) (hfull : LinearIndependent ℂ P)
    (htail : ∀ i, g.1.component i - coordinatePolynomialAlgHom 2 (P i) ∈
      maximalIdeal 2 ^ 3) (c : Germ 2)
    (hdiv : ∀ i j, c ∣ jacobian (g.1.component i) (g.1.component j)) :
    ∃ f : PointedMapGerm 2 3, g.RightLeftEquivalent f ∧
      (∀ i, f.1.component i - coordinatePolynomialAlgHom 2 (quadraticMonomialBasis i) ∈
        maximalIdeal 2 ^ 3) ∧
      ∀ i j, c ∣ jacobian (f.1.component i) (f.1.component j) := by
  obtain ⟨A, hAdet, hA⟩ := exists_linear_quadratic_monomial_normalization P hP hfull
  obtain ⟨T, hT⟩ := exists_equiv_linear_matrix A hAdet
  let f := T.forward.comp g
  have hcomponent (i : Fin 3) : f.1.component i =
      ∑ j, constRingHom 2 (A i j) * g.1.component j := by
    rw [PointedMapGerm.component_comp_eq_pullback, ← PointedMapGerm.pullback_coordinate,
      hT, map_sum]
    simp only [map_mul, PointedMapGerm.pullback_constRingHom, PointedMapGerm.pullback_coordinate]
  refine ⟨f, ?_, ?_, ?_⟩
  · refine ⟨PointedEquivGerm.identity 2, T, ?_⟩
    rw [PointedEquivGerm.identity_forward, PointedMapGerm.comp_identity]
  · intro i
    have hsum := (maximalIdeal 2 ^ 3).sum_mem (fun j (_ : j ∈ Finset.univ) =>
      (maximalIdeal 2 ^ 3).mul_mem_left (constRingHom 2 (A i j)) (htail j))
    have heq : f.1.component i - coordinatePolynomialAlgHom 2 (quadraticMonomialBasis i) =
        ∑ j, constRingHom 2 (A i j) *
          (g.1.component j - coordinatePolynomialAlgHom 2 (P j)) := by
      rw [hcomponent, ← hA i, map_sum]
      simp only [map_mul, coordinatePolynomialAlgHom_C, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    exact hsum
  · have hspan (i : Fin 3) : f.1.component i ∈ Submodule.span ℂ (Set.range g.1.component) := by
      rw [hcomponent]
      apply Submodule.sum_mem
      intro j _
      change A i j • g.1.component j ∈ _
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
    intro i j
    exact dvd_jacobian_of_mem_linear_span g.1.component c hdiv (hspan i) (hspan j)

/-- Three independent quadratic jets contradict injectivity in the presence
of the nonunit common minor divisor supplied by the reduction. -/
theorem full_quadratic_jet_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (P : Fin 3 → OrbitSourceForm)
    (hP : ∀ i, (P i).IsHomogeneous 2) (hfull : LinearIndependent ℂ P)
    (htail : ∀ i, g.1.component i - coordinatePolynomialAlgHom 2 (P i) ∈
      maximalIdeal 2 ^ 3) (c : Germ 2) (hc : c ∈ maximalIdeal 2)
    (hdiv : ∀ i j, c ∣ jacobian (g.1.component i) (g.1.component j)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨f, hgf, hftail, hdivf⟩ :=
    exists_target_full_quadratic_monomial_normalization g P hP hfull htail c hdiv
  have hthird : f.1.component 2 ∈ maximalIdeal 2 ^ 2 := by
    have hproduct : coordinatePolynomialAlgHom 2 (quadraticMonomialBasis 2) ∈
        maximalIdeal 2 ^ 2 := by
      simpa [quadraticMonomialBasis, coordinatePolynomialAlgHom_X, pow_two] using
        Ideal.mul_mem_mul (coordinate_mem_maximalIdeal (0 : Fin 2))
          (coordinate_mem_maximalIdeal (1 : Fin 2))
    have hh := (maximalIdeal 2 ^ 2).add_mem
      ((Ideal.pow_le_pow_right (by omega : 2 ≤ 3)) (hftail 2)) hproduct
    simpa only [sub_add_cancel] using hh
  have hno : ∀ z : Fin 2 → ℂ, z ≠ 0 →
      ¬ (MvPolynomial.eval z (quadraticMonomialBasis 0) = 0 ∧
        MvPolynomial.eval z (quadraticMonomialBasis 1) = 0) := by
    intro z hz hzero
    simp only [quadraticMonomialBasis, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_pow, MvPolynomial.eval_X, sq_eq_zero_iff] at hzero
    apply hz
    ext i
    fin_cases i
    · exact hzero.1
    · exact hzero.2
  have hpair : ¬ ∃ u : ℂ, quadraticMonomialBasis 1 =
      MvPolynomial.C u * quadraticMonomialBasis 0 := by
    rintro ⟨u, hu⟩
    have hh := congrArg (MvPolynomial.eval ![0, (1 : ℂ)]) hu
    simp [quadraticMonomialBasis] at hh
  have hne : quadraticMonomialBasis 0 ≠ 0 := by
    simp [quadraticMonomialBasis]
  intro hg
  exact basepointFree_quadratic_pencil_not_hasInjectiveRepresentative f
    (quadraticMonomialBasis 0) (quadraticMonomialBasis 1)
    ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).pow 2)
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow 2)
    hne hpair hno (hftail 0) (hftail 1) hthird c hc hdivf
    (hgf.hasInjectiveRepresentative hg)

end OnLeConjecture.DTwo
