/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ECNineGlobalNormDegree

/-!
# A global matrix for the C9 determinant norm

The basis element indexed by `(i,j)` has weight `i+j`. Multiplication by a
section of degree `N` therefore has a matrix entry from column `c` to row
`r` of degree `N + weight c - weight r`. Homogenizing every entry to that
degree produces a matrix of binary forms. Its determinant is homogeneous of
degree `9N` and dehomogenizes to the determinant norm on `x = 1`.

This realizes the homogeneous norm form as a determinant. It also explains
why a drop in the degree of the affine determinant is a zero in the
complementary chart.
-/

public section

noncomputable section

open scoped BigOperators

namespace OnLeConjecture.DThree.ECNineGlobalNorm

open _root_.Polynomial

/-- A weighted matrix of homogeneous forms whose entries vanish when the
required entry degree would be negative has homogeneous determinant. -/
theorem isHomogeneous_det_of_weighted_entries
    {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial (Fin 2) R)) (weight : ι → ℕ) (D : ℕ)
    (hhomogeneous : ∀ row column,
      (M row column).IsHomogeneous
        ((D + weight column) - weight row))
    (hzero : ∀ row column, D + weight column < weight row →
      M row column = 0) :
    M.det.IsHomogeneous (Fintype.card ι * D) := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ _
  intro σ _hσ
  by_cases hnegative : ∃ i, D + weight i < weight (σ i)
  · obtain ⟨i, hi⟩ := hnegative
    have hentry : M (σ i) i = 0 := hzero (σ i) i hi
    have hproduct : ∏ i, M (σ i) i = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hentry
    rw [hproduct, mul_zero]
    exact MvPolynomial.isHomogeneous_zero (Fin 2) R _
  · have hle (i : ι) : weight (σ i) ≤ D + weight i := by
      exact Nat.le_of_not_gt fun hi ↦ hnegative ⟨i, hi⟩
    have hproduct :
        (∏ i, M (σ i) i).IsHomogeneous
          (∑ i, ((D + weight i) - weight (σ i))) := by
      exact MvPolynomial.IsHomogeneous.prod Finset.univ _ _
        (fun i _hi ↦ hhomogeneous (σ i) i)
    have hdegree :
        ∑ i, ((D + weight i) - weight (σ i)) =
          Fintype.card ι * D := by
      have hpoint (i : ι) :
          ((D + weight i) - weight (σ i)) + weight (σ i) =
            D + weight i :=
        Nat.sub_add_cancel (hle i)
      have hsum := Finset.sum_congr rfl
        (fun i (_hi : i ∈ (Finset.univ : Finset ι)) ↦ hpoint i)
      simp only [Finset.sum_add_distrib] at hsum
      rw [Equiv.sum_comp σ weight] at hsum
      have hconstant : ∑ _i : ι, D = Fintype.card ι * D := by
        simp [Nat.mul_comm]
      rw [hconstant] at hsum
      omega
    rw [hdegree] at hproduct
    simpa using hproduct.C_mul ((Equiv.Perm.sign σ : ℤ) : R)

end OnLeConjecture.DThree.ECNineGlobalNorm

namespace OnLeConjecture.DThree

open _root_.Polynomial Module

/-- The multiplication matrix with each entry homogenized to the degree
specified by the weights of its row and column. -/
@[expose]
def eCNineGlobalLeftMulMatrix (R : Form ℂ) (N : ℕ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) (Form ℂ) :=
  fun row column ↦
    ((Algebra.leftMulMatrix eCNineUnitBasis
      (eCNineUnitDifferenceElement R)) row column).homogenize
        ((N + eCNineUnitBasisWeight column) -
          eCNineUnitBasisWeight row)

/-- The weighted multiplication matrix in the complementary chart. Each
entry is reflected at its prescribed degree. -/
@[expose]
def eCNineCapitalXChartLeftMulMatrix (R : Form ℂ) (N : ℕ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ[X] :=
  fun row column ↦
    ((Algebra.leftMulMatrix eCNineUnitBasis
      (eCNineUnitDifferenceElement R)) row column).reflect
        ((N + eCNineUnitBasisWeight column) -
          eCNineUnitBasisWeight row)

/-- Each entry of the global multiplication matrix has its prescribed
homogeneous degree. -/
theorem eCNineGlobalLeftMulMatrix_entry_isHomogeneous
    (R : Form ℂ) (N : ℕ) (row column : Fin 3 × Fin 3) :
    (eCNineGlobalLeftMulMatrix R N row column).IsHomogeneous
      ((N + eCNineUnitBasisWeight column) -
        eCNineUnitBasisWeight row) := by
  exact Polynomial.isHomogeneous_homogenize _

/-- An entry is zero when its prescribed degree would be negative. -/
theorem eCNineGlobalLeftMulMatrix_entry_eq_zero_of_lt
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (row column : Fin 3 × Fin 3)
    (hdegree : N + eCNineUnitBasisWeight column <
      eCNineUnitBasisWeight row) :
    eCNineGlobalLeftMulMatrix R N row column = 0 := by
  obtain hzero | hbound := eCNineUnitLeftMulMatrix_entry_bound hR row column
  · simp [eCNineGlobalLeftMulMatrix, hzero]
  · omega

/-- The determinant of the global multiplication matrix is homogeneous of
degree `9N`. -/
theorem eCNineGlobalLeftMulMatrix_det_isHomogeneous
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    (eCNineGlobalLeftMulMatrix R N).det.IsHomogeneous (9 * N) := by
  have hdet := ECNineGlobalNorm.isHomogeneous_det_of_weighted_entries
    (eCNineGlobalLeftMulMatrix R N) eCNineUnitBasisWeight N
    (eCNineGlobalLeftMulMatrix_entry_isHomogeneous R N)
    (eCNineGlobalLeftMulMatrix_entry_eq_zero_of_lt hR)
  norm_num at hdet ⊢
  exact hdet

/-- Dehomogenizing an entry at `x = 1` recovers the original unit chart
multiplication matrix entry. -/
theorem eCNineGlobalLeftMulMatrix_entry_dehomogenize
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (row column : Fin 3 × Fin 3) :
    MvPolynomial.aeval ![X, (1 : ℂ[X])]
        (eCNineGlobalLeftMulMatrix R N row column) =
      (Algebra.leftMulMatrix eCNineUnitBasis
        (eCNineUnitDifferenceElement R)) row column := by
  obtain hzero | hbound := eCNineUnitLeftMulMatrix_entry_bound hR row column
  · simp [eCNineGlobalLeftMulMatrix, hzero]
  · apply Polynomial.aeval_homogenize_X_one
    exact Nat.le_sub_of_add_le hbound

/-- Dehomogenizing a global matrix entry at `X = 1` gives its reflected
entry in the complementary chart. -/
theorem eCNineGlobalLeftMulMatrix_entry_complementary_dehomogenize
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N)
    (row column : Fin 3 × Fin 3) :
    MvPolynomial.aeval ![(1 : ℂ[X]), X]
        (eCNineGlobalLeftMulMatrix R N row column) =
      eCNineCapitalXChartLeftMulMatrix R N row column := by
  obtain hzero | hbound := eCNineUnitLeftMulMatrix_entry_bound hR row column
  · simp [eCNineGlobalLeftMulMatrix,
      eCNineCapitalXChartLeftMulMatrix, hzero]
  · exact ECNineGlobalNorm.aeval_one_X_homogenize_eq_reflect _ _
      (Nat.le_sub_of_add_le hbound)

/-- Dehomogenizing the global matrix determinant at `x = 1` gives the unit
chart determinant norm. -/
theorem eCNineGlobalLeftMulMatrix_det_dehomogenize
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    MvPolynomial.aeval ![X, (1 : ℂ[X])]
        (eCNineGlobalLeftMulMatrix R N).det =
      eCNineUnitDifferenceNorm R := by
  let evaluation : Form ℂ →+* ℂ[X] :=
    MvPolynomial.eval₂Hom (algebraMap ℂ ℂ[X]) ![X, (1 : ℂ[X])]
  calc
    MvPolynomial.aeval ![X, (1 : ℂ[X])]
        (eCNineGlobalLeftMulMatrix R N).det =
        evaluation (eCNineGlobalLeftMulMatrix R N).det := rfl
    _ = (evaluation.mapMatrix (eCNineGlobalLeftMulMatrix R N)).det :=
      evaluation.map_det _
    _ = (Algebra.leftMulMatrix eCNineUnitBasis
        (eCNineUnitDifferenceElement R)).det := by
      have hmatrix :
          evaluation.mapMatrix (eCNineGlobalLeftMulMatrix R N) =
            Algebra.leftMulMatrix eCNineUnitBasis
              (eCNineUnitDifferenceElement R) := by
        funext row column
        change MvPolynomial.aeval ![X, (1 : ℂ[X])]
            (eCNineGlobalLeftMulMatrix R N row column) = _
        exact eCNineGlobalLeftMulMatrix_entry_dehomogenize hR row column
      rw [hmatrix]
    _ = eCNineUnitDifferenceNorm R :=
      (eCNineUnitDifferenceNorm_eq_matrix_det R).symm

/-- The global norm form is the determinant of the homogenized weighted
multiplication matrix. -/
theorem eCNineGlobalDifferenceNormForm_eq_matrix_det
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    eCNineGlobalDifferenceNormForm R N =
      (eCNineGlobalLeftMulMatrix R N).det := by
  apply Polynomial.homogenize_eq_of_isHomogeneous
  · exact eCNineGlobalLeftMulMatrix_det_isHomogeneous hR
  · exact eCNineGlobalLeftMulMatrix_det_dehomogenize hR

/-- The determinant of the reflected complementary chart matrix is the
complementary chart norm. -/
theorem eCNineCapitalXChartLeftMulMatrix_det
    {R : Form ℂ} {N : ℕ} (hR : R.IsHomogeneous N) :
    (eCNineCapitalXChartLeftMulMatrix R N).det =
      eCNineCapitalXChartDifferenceNorm R N := by
  let evaluation : Form ℂ →+* ℂ[X] :=
    MvPolynomial.eval₂Hom (algebraMap ℂ ℂ[X]) ![(1 : ℂ[X]), X]
  have hmatrix :
      evaluation.mapMatrix (eCNineGlobalLeftMulMatrix R N) =
        eCNineCapitalXChartLeftMulMatrix R N := by
    funext row column
    change MvPolynomial.aeval ![(1 : ℂ[X]), X]
        (eCNineGlobalLeftMulMatrix R N row column) = _
    exact eCNineGlobalLeftMulMatrix_entry_complementary_dehomogenize
      hR row column
  calc
    (eCNineCapitalXChartLeftMulMatrix R N).det =
        (evaluation.mapMatrix (eCNineGlobalLeftMulMatrix R N)).det := by
      rw [hmatrix]
    _ = evaluation (eCNineGlobalLeftMulMatrix R N).det :=
      (evaluation.map_det _).symm
    _ = MvPolynomial.aeval ![(1 : ℂ[X]), X]
        (eCNineGlobalDifferenceNormForm R N) := by
      change MvPolynomial.aeval ![(1 : ℂ[X]), X]
          (eCNineGlobalLeftMulMatrix R N).det = _
      rw [eCNineGlobalDifferenceNormForm_eq_matrix_det hR]
    _ = eCNineCapitalXChartDifferenceNorm R N :=
      eCNineGlobalDifferenceNormForm_complementary_dehomogenize hR

/-- For a hard section, the determinant of the global multiplication matrix
is nonzero and has exact total degree `9N`. -/
theorem eCNineHardGlobalLeftMulMatrix_det_totalDegree
    {omega : ℂ} (homega : IsPrimitiveRoot omega 3)
    (R : Form ℂ) (Rzero : ESourceRing ℂ)
    (coefficient : ℂ) (N : ℕ)
    (hhomogeneous : R.IsHomogeneous N)
    (hR : R = eSourceCubeSubstitutionForm Rzero +
      MvPolynomial.C coefficient * formT ^ N)
    (hcoefficient : coefficient ≠ 0) (hnotdiv : ¬ 3 ∣ N) :
    (eCNineGlobalLeftMulMatrix R N).det.totalDegree = 9 * N := by
  rw [← eCNineGlobalDifferenceNormForm_eq_matrix_det hhomogeneous]
  exact eCNineHardGlobalDifferenceNormForm_totalDegree homega R Rzero
    coefficient N hhomogeneous hR hcoefficient hnotdiv

end OnLeConjecture.DThree
