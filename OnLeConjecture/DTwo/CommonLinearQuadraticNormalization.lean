/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.FullQuadraticJetExclusion

/-!
# Normalization of a quadratic pencil with a common projective zero

The common projective zero determines a linear factor. Independence of the
two quadratics makes the remaining two linear forms a basis, and an explicit
inverse coefficient matrix changes the pencil to `L²,LM`.
-/

public section

namespace OnLeConjecture.DTwo

private noncomputable def pairPresentationLinearMap (F G : OrbitSourceForm) :
    (Fin 2 → ℂ) →ₗ[ℂ] OrbitSourceForm where
  toFun v := v 0 • F + v 1 • G
  map_add' v w := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

private theorem exists_inverse_pair_coefficients
    (P Q F G : OrbitSourceForm) (hPQ : LinearIndependent ℂ (![P, Q] : Fin 2 → OrbitSourceForm))
    (a b c d : ℂ) (hP : P = MvPolynomial.C a * F + MvPolynomial.C b * G)
    (hQ : Q = MvPolynomial.C c * F + MvPolynomial.C d * G) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det ≠ 0 ∧
      ∀ i, ∑ j, MvPolynomial.C (A i j) * (![P, Q] : Fin 2 → OrbitSourceForm) j =
        (![F, G] : Fin 2 → OrbitSourceForm) i := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![a, b; c, d]
  let L := pairPresentationLinearMap F G
  have hLM : L ∘ M.row = (![P, Q] : Fin 2 → OrbitSourceForm) := by
    funext i
    fin_cases i
    · change a • F + b • G = P
      simp [hP, Algebra.smul_def]
    · change c • F + d • G = Q
      simp [hQ, Algebra.smul_def]
  have hrows : LinearIndependent ℂ M.row := by
    apply LinearIndependent.of_comp L
    rwa [hLM]
  have hM : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)
  refine ⟨M⁻¹, isUnit_iff_ne_zero.mp (M.isUnit_nonsing_inv_det hM), ?_⟩
  intro i
  have hrow : (∑ j, M⁻¹ i j • M.row j) = (1 : Matrix (Fin 2) (Fin 2) ℂ).row i := by
    ext k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row, Matrix.mul_apply]
      using congrFun (congrFun (M.nonsing_inv_mul hM) i) k
  have hLi (j : Fin 2) : L (M.row j) = (![P, Q] : Fin 2 → OrbitSourceForm) j := congrFun hLM j
  have hh := congrArg L hrow
  simp only [map_sum, map_smul] at hh
  simp only [hLi, Algebra.smul_def, ← MvPolynomial.C_eq_algebraMap] at hh
  rw [hh]
  fin_cases i <;> simp [L, pairPresentationLinearMap, Matrix.row, Matrix.one_apply]

/-- A common nonzero zero and independence construct both the source linear
coordinates and the invertible target matrix for a common-factor pencil. -/
theorem exists_common_linear_quadratic_pencil_normalization
    (P Q : OrbitSourceForm) (hP : P.IsHomogeneous 2) (hQ : Q.IsHomogeneous 2)
    (hPQ : LinearIndependent ℂ (![P, Q] : Fin 2 → OrbitSourceForm))
    (z : Fin 2 → ℂ) (hz : z ≠ 0)
    (hPz : MvPolynomial.eval z P = 0) (hQz : MvPolynomial.eval z Q = 0) :
    ∃ r s t u : ℂ, r * u - s * t ≠ 0 ∧
      ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det ≠ 0 ∧
        (∑ j, MvPolynomial.C (A 0 j) * (![P, Q] : Fin 2 → OrbitSourceForm) j =
          binaryLinearForm r s ^ 2) ∧
        (∑ j, MvPolynomial.C (A 1 j) * (![P, Q] : Fin 2 → OrbitSourceForm) j =
          binaryLinearForm r s * binaryLinearForm t u) := by
  let a := binaryQuadraticCoefficients P 0
  let b := binaryQuadraticCoefficients P 1
  let c := binaryQuadraticCoefficients P 2
  let d := binaryQuadraticCoefficients Q 0
  let e := binaryQuadraticCoefficients Q 1
  let f := binaryQuadraticCoefficients Q 2
  have hPeq : P = binaryQuadraticForm a b c := eq_binaryQuadraticForm_of_isHomogeneous hP
  have hQeq : Q = binaryQuadraticForm d e f := eq_binaryQuadraticForm_of_isHomogeneous hQ
  have hPzero : a * z 0 ^ 2 + b * z 0 * z 1 + c * z 1 ^ 2 = 0 := by
    simpa [hPeq, binaryQuadraticForm, orbitPolynomialS, orbitPolynomialLambda] using hPz
  have hQzero : d * z 0 ^ 2 + e * z 0 * z 1 + f * z 1 ^ 2 = 0 := by
    simpa [hQeq, binaryQuadraticForm, orbitPolynomialS, orbitPolynomialLambda] using hQz
  by_cases hz1 : z 1 = 0
  · have hz0 : z 0 ≠ 0 := by
      intro hzero
      apply hz
      ext i
      fin_cases i
      · exact hzero
      · exact hz1
    have ha : a = 0 := by
      simpa only [hz1, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
        mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), hz0, or_false] using hPzero
    have hd : d = 0 := by
      simpa only [hz1, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
        mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), hz0, or_false] using hQzero
    let L := binaryLinearForm 0 1
    let M := binaryLinearForm 1 0
    have hfactorP : P = MvPolynomial.C c * L ^ 2 + MvPolynomial.C b * (L * M) := by
      rw [hPeq, ha]
      simp [L, M, binaryLinearForm, binaryQuadraticForm]
      ring
    have hfactorQ : Q = MvPolynomial.C f * L ^ 2 + MvPolynomial.C e * (L * M) := by
      rw [hQeq, hd]
      simp [L, M, binaryLinearForm, binaryQuadraticForm]
      ring
    obtain ⟨A, hA, hnorm⟩ := exists_inverse_pair_coefficients P Q (L ^ 2) (L * M)
      hPQ c b f e hfactorP hfactorQ
    exact ⟨0, 1, 1, 0, by norm_num, A, hA, hnorm 0, hnorm 1⟩
  · let v := z 0 / z 1
    have hzeroP : a * v ^ 2 + b * v + c = 0 := by
      dsimp only [v]
      field_simp
      linear_combination hPzero
    have hzeroQ : d * v ^ 2 + e * v + f = 0 := by
      dsimp only [v]
      field_simp
      linear_combination hQzero
    have hc : c = -a * v ^ 2 - b * v := by linear_combination hzeroP
    have hf : f = -d * v ^ 2 - e * v := by linear_combination hzeroQ
    let L := binaryLinearForm 1 (-v)
    let M := binaryLinearForm 0 1
    have hfactorP : P = MvPolynomial.C a * L ^ 2 +
        MvPolynomial.C (b + 2 * a * v) * (L * M) := by
      rw [hPeq, hc]
      simp only [L, M, binaryLinearForm, binaryQuadraticForm,
        map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]
      ring
    have hfactorQ : Q = MvPolynomial.C d * L ^ 2 +
        MvPolynomial.C (e + 2 * d * v) * (L * M) := by
      rw [hQeq, hf]
      simp only [L, M, binaryLinearForm, binaryQuadraticForm,
        map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, map_zero]
      ring
    obtain ⟨A, hA, hnorm⟩ := exists_inverse_pair_coefficients P Q (L ^ 2) (L * M)
      hPQ a (b + 2 * a * v) d (e + 2 * d * v) hfactorP hfactorQ
    exact ⟨1, -v, 0, 1, by simp, A, hA, hnorm 0, hnorm 1⟩

end OnLeConjecture.DTwo
