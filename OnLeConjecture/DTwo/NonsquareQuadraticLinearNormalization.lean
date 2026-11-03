/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.QuadraticJetAlgebra
public import OnLeConjecture.Analytic.MatrixLinearCoordinates
public import OnLeConjecture.Analytic.AnalyticPointBasis

/-!
# Source coordinates for a nonsquare quadratic jet

A quadratic with nonzero discriminant is a difference of two squares of
independent linear forms. The corresponding invertible analytic source
change acts simultaneously on every scalar multiple of that jet.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

theorem binaryLinearForm_sq_sub_sq (r s t u : ℂ) :
    binaryLinearForm r s ^ 2 - binaryLinearForm t u ^ 2 =
      binaryQuadraticForm (r ^ 2 - t ^ 2) (2 * r * s - 2 * t * u) (s ^ 2 - u ^ 2) := by
  simp only [binaryLinearForm, binaryQuadraticForm, map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem exists_difference_squares_of_quadratic_discriminant_ne_zero
    (Q : OrbitSourceForm) (hQ : Q.IsHomogeneous 2)
    (hdisc : binaryQuadraticDiscriminant Q ≠ 0) :
    ∃ r s t u : ℂ, r * u - s * t ≠ 0 ∧
      Q = binaryLinearForm r s ^ 2 - binaryLinearForm t u ^ 2 := by
  let a := binaryQuadraticCoefficients Q 0
  let b := binaryQuadraticCoefficients Q 1
  let c := binaryQuadraticCoefficients Q 2
  have hform : Q = binaryQuadraticForm a b c := eq_binaryQuadraticForm_of_isHomogeneous hQ
  have hdis : b ^ 2 - 4 * a * c ≠ 0 := hdisc
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hz
      apply hdis
      simp [ha, hz]
    refine ⟨b / 2, (c + 1) / 2, b / 2, (c - 1) / 2, ?_, ?_⟩
    · have heq : b / 2 * ((c - 1) / 2) - (c + 1) / 2 * (b / 2) = -b / 2 := by ring
      rw [heq]
      exact div_ne_zero (neg_ne_zero.mpr hb) (by norm_num)
    · rw [binaryLinearForm_sq_sub_sq, hform, ha]
      congr 1 <;> ring
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq a (by decide : 0 < 2)
    have hrne : r ≠ 0 := by
      intro hz
      apply ha
      simpa [hz] using hr.symm
    let s := b / (2 * r)
    have hs : 2 * r * s = b := by dsimp only [s]; field_simp
    have hnonzero : s ^ 2 - c ≠ 0 := by
      intro hz
      apply hdis
      rw [← hr, ← hs]
      linear_combination 4 * r ^ 2 * hz
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ 2 - c) (by decide : 0 < 2)
    have hune : u ≠ 0 := by
      intro hz
      apply hnonzero
      simpa [hz] using hu.symm
    refine ⟨r, s, 0, u, ?_, ?_⟩
    · simpa using mul_ne_zero hrne hune
    · rw [binaryLinearForm_sq_sub_sq, hform]
      simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_zero, zero_mul, hr, hs, hu,
        sub_sub_cancel]

theorem exists_nonsquare_quadratic_source_normalization
    (Q : OrbitSourceForm) (hQ : Q.IsHomogeneous 2)
    (hdisc : binaryQuadraticDiscriminant Q ≠ 0) :
    ∃ e : PointedEquivGerm 2,
      e.forward.pullbackRingHom (coordinatePolynomialAlgHom 2 Q) =
        coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) := by
  obtain ⟨r, s, t, u, hdet, hform⟩ :=
    exists_difference_squares_of_quadratic_discriminant_ne_zero Q hQ hdisc
  obtain ⟨a, ha⟩ := exists_equiv_linear_matrix
    (!![r, s; t, u] : Matrix (Fin 2) (Fin 2) ℂ)
    (by simpa [Matrix.det_fin_two] using hdet)
  have ha0 : a.forward.pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinatePolynomialAlgHom 2 (binaryLinearForm r s) := by
    simp only [binaryLinearForm, orbitPolynomialS, orbitPolynomialLambda,
      map_add, map_mul, coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
    simpa [Fin.sum_univ_succ] using ha 0
  have ha1 : a.forward.pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinatePolynomialAlgHom 2 (binaryLinearForm t u) := by
    simp only [binaryLinearForm, orbitPolynomialS, orbitPolynomialLambda,
      map_add, map_mul, coordinatePolynomialAlgHom_C, coordinatePolynomialAlgHom_X]
    simpa [Fin.sum_univ_succ] using ha 1
  have hpull : a.pullbackAlgEquiv (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) =
      coordinatePolynomialAlgHom 2 Q := by
    change a.forward.pullbackRingHom _ = _
    simp only [orbitPolynomialPhi, orbitPolynomialS, orbitPolynomialLambda, map_sub,
      map_pow, coordinatePolynomialAlgHom_X, ha0, ha1, hform]
  refine ⟨a.symm, ?_⟩
  have hback := congrArg a.pullbackAlgEquiv.symm hpull
  rw [a.pullbackAlgEquiv.symm_apply_apply] at hback
  exact hback.symm

end OnLeConjecture.DTwo
