/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticHenselFactorization
public import OnLeConjecture.Analytic.IntersectionResultant

/-!
# Intersection contributions of residue root clusters

A coprime residue factorization lifts to analytic polynomial factors.
A factor whose residue is `(X - c)^m` becomes distinguished after the
translation `X ↦ X + c`. Its resultant order is the intersection
multiplicity of this translated factor with the translated second
polynomial. The first factor must be translated even when `c ≠ 0`.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Translation of an analytic polynomial to the residue point `(c, 0)`. -/
@[expose] noncomputable def rootTranslation (P : Polynomial (Germ 1)) (c : ℂ) :
    Polynomial (Germ 1) := P.taylor (constRingHom 1 c)

@[simp] theorem rootTranslation_monic (P : Polynomial (Germ 1)) (c : ℂ) :
    (rootTranslation P c).Monic ↔ P.Monic := by
  simp only [Monic, rootTranslation, leadingCoeff_taylor]

@[simp] theorem rootTranslation_natDegree (P : Polynomial (Germ 1)) (c : ℂ) :
    (rootTranslation P c).natDegree = P.natDegree := natDegree_taylor _ _

theorem rootTranslation_residue (P : Polynomial (Germ 1)) (c : ℂ) :
    (rootTranslation P c).map (valueRingHom 1) =
      (P.map (valueRingHom 1)).taylor c := by
  simp only [rootTranslation, map_taylor, valueRingHom_const]

theorem resultant_rootTranslation (P Q : Polynomial (Germ 1)) (c : ℂ) :
    (rootTranslation P c).resultant (rootTranslation Q c) = P.resultant Q :=
  resultant_taylor P Q (constRingHom 1 c)

/-- A residue root cluster becomes a distinguished polynomial at its
own center. -/
theorem rootTranslation_coeff_mem_maximalIdeal
    (P : Polynomial (Germ 1)) (c : ℂ) (m : ℕ)
    (hresidue : P.map (valueRingHom 1) = (X - C c) ^ m) :
    ∀ j, j < m → (rootTranslation P c).coeff j ∈ maximalIdeal 1 := by
  have hzero : (rootTranslation P c).map (valueRingHom 1) = X ^ m := by
    rw [rootTranslation_residue, hresidue, taylor_pow]
    simp only [map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  intro j hj
  apply mem_maximalIdeal_iff.mpr
  have h := congrArg (fun p ↦ p.coeff j) hzero
  simpa only [coeff_map, coeff_X_pow, if_neg (Nat.ne_of_lt hj)] using h

/-- The resultant of a root cluster measures the analytic intersection
at the corresponding residue point, not at the untranslated origin. -/
theorem exists_root_cluster_intersection_eq_resultant_order
    (P Q : Polynomial (Germ 1)) (c : ℂ) (m : ℕ) (hm : 0 < m)
    (hP : P.Monic) (hdegree : P.natDegree = m)
    (hresidue : P.map (valueRingHom 1) = (X - C c) ^ m)
    (hresultant : P.resultant Q ≠ 0) :
    ∃ hfinite : PlaneCurve.HasFiniteIntersection
      (firstCoordinatePolynomialEvaluation (rootTranslation P c))
      (firstCoordinatePolynomialEvaluation (rootTranslation Q c)),
      PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation (rootTranslation P c))
        (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) hfinite =
          (vanishingOrder (P.resultant Q)).toNat := by
  have hmonic := (rootTranslation_monic P c).mpr hP
  have hdeg : (rootTranslation P c).natDegree = (m - 1) + 1 := by
    rw [rootTranslation_natDegree, hdegree, Nat.sub_add_cancel hm]
  have hdist : ∀ j, j < (m - 1) + 1 →
      (rootTranslation P c).coeff j ∈ maximalIdeal 1 := by
    simpa only [Nat.sub_add_cancel hm] using
      rootTranslation_coeff_mem_maximalIdeal P c m hresidue
  have hne : (rootTranslation P c).resultant (rootTranslation Q c) ≠ 0 := by
    rwa [resultant_rootTranslation]
  have hf := hasFiniteIntersection_of_resultant_ne_zero (m - 1)
    (rootTranslation P c) (rootTranslation Q c) hmonic hdeg hdist hne
  refine ⟨hf, ?_⟩
  rw [intersectionMultiplicity_eq_resultant_order (m - 1)
    (rootTranslation P c) (rootTranslation Q c) hmonic hdeg hdist hf,
      resultant_rootTranslation]

/-- Monic factorization makes the usual resultant multiplicative in its
first polynomial without any degree padding. -/
theorem resultant_monic_mul_left (A B Q : Polynomial (Germ 1))
    (hA : A.Monic) (hB : B.Monic) :
    (A * B).resultant Q = A.resultant Q * B.resultant Q := by
  change (A * B).resultant Q (A * B).natDegree Q.natDegree = _
  rw [hA.natDegree_mul hB]
  exact resultant_mul_left A B Q Q.natDegree le_rfl

/-- Splitting off a prescribed full residue root cluster separates its
local intersection contribution from the complementary resultant. -/
theorem exists_root_cluster_factorization_and_intersection
    (P Q : Polynomial (Germ 1)) (hP : P.Monic)
    (c : ℂ) (m n : ℕ) (hm : 0 < m) (hdegree : P.natDegree = m + n)
    (B₀ : ℂ[X]) (hB₀ : B₀.Monic) (hBn : B₀.natDegree = n)
    (hBvalue : B₀.eval c ≠ 0)
    (hresidue : P.map (valueRingHom 1) = (X - C c) ^ m * B₀)
    (hresultant : P.resultant Q ≠ 0) :
    ∃ A B : Polynomial (Germ 1), A.Monic ∧ A.natDegree = m ∧ B.Monic ∧
      B.natDegree = n ∧ A.map (valueRingHom 1) = (X - C c) ^ m ∧
      B.map (valueRingHom 1) = B₀ ∧ P = A * B ∧ B.resultant Q ≠ 0 ∧
      ∃ hfinite : PlaneCurve.HasFiniteIntersection
        (firstCoordinatePolynomialEvaluation (rootTranslation A c))
        (firstCoordinatePolynomialEvaluation (rootTranslation Q c)),
        (vanishingOrder (P.resultant Q)).toNat =
          PlaneCurve.intersectionMultiplicity
            (firstCoordinatePolynomialEvaluation (rootTranslation A c))
            (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) hfinite +
              (vanishingOrder (B.resultant Q)).toNat := by
  have hcoprime : IsCoprime (X - C c) B₀ := by
    apply (isUnit_resultant_iff_isCoprime (monic_X_sub_C c)).mp
    simpa only [natDegree_X_sub_C, resultant_X_sub_C_left B₀ B₀.natDegree c le_rfl]
      using hBvalue.isUnit
  obtain ⟨A, B, hA, hAm, hB, hBn', hAres, hBres, hfactor⟩ :=
    exists_analytic_hensel_factorization m n P hP hdegree ((X - C c) ^ m) B₀
      ((monic_X_sub_C c).pow m) hB₀ (by simp) hBn hcoprime.pow_left hresidue
  have hres : P.resultant Q = A.resultant Q * B.resultant Q := by
    rw [hfactor, resultant_monic_mul_left A B Q hA hB]
  have hne := mul_ne_zero_iff.mp (hres ▸ hresultant)
  obtain ⟨hf, hinter⟩ := exists_root_cluster_intersection_eq_resultant_order
    A Q c m hm hA hAm hAres hne.1
  refine ⟨A, B, hA, hAm, hB, hBn', hAres, hBres, hfactor, hne.2, hf, ?_⟩
  rw [hres, vanishingOrder_mul, ENat.toNat_add
    (vanishingOrder_eq_top_iff.not.mpr hne.1) (vanishingOrder_eq_top_iff.not.mpr hne.2), hinter]

/-- A residue root determines its entire analytic factor without a
supplied complementary factorization. Its degree is exactly the residue
root multiplicity. The complementary resultant is the remaining
contribution. -/
theorem exists_residue_root_factorization_and_intersection
    (P Q : Polynomial (Germ 1)) (hP : P.Monic) (c : ℂ)
    (hroot : (P.map (valueRingHom 1)).IsRoot c)
    (hresultant : P.resultant Q ≠ 0) :
    ∃ A B : Polynomial (Germ 1), A.Monic ∧ B.Monic ∧
      A.natDegree = (P.map (valueRingHom 1)).rootMultiplicity c ∧
      A.natDegree + B.natDegree = P.natDegree ∧
      A.map (valueRingHom 1) = (X - C c) ^ A.natDegree ∧
      (B.map (valueRingHom 1)).eval c ≠ 0 ∧ P = A * B ∧ B.resultant Q ≠ 0 ∧
      ∃ hfinite : PlaneCurve.HasFiniteIntersection
        (firstCoordinatePolynomialEvaluation (rootTranslation A c))
        (firstCoordinatePolynomialEvaluation (rootTranslation Q c)),
        (vanishingOrder (P.resultant Q)).toNat =
          PlaneCurve.intersectionMultiplicity
            (firstCoordinatePolynomialEvaluation (rootTranslation A c))
            (firstCoordinatePolynomialEvaluation (rootTranslation Q c)) hfinite +
              (vanishingOrder (B.resultant Q)).toNat := by
  let p := P.map (valueRingHom 1)
  let m := p.rootMultiplicity c
  let B₀ := p /ₘ (X - C c) ^ m
  have hp : p.Monic := hP.map _
  have hpow : ((X - C c) ^ m : ℂ[X]).Monic := (monic_X_sub_C c).pow m
  have hfactor : (X - C c) ^ m * B₀ = p := pow_mul_divByMonic_rootMultiplicity_eq p c
  have hB₀ : B₀.Monic := hpow.of_mul_monic_left (hfactor ▸ hp)
  have hdegree : P.natDegree = m + B₀.natDegree := by
    have h := congrArg Polynomial.natDegree hfactor
    rw [hpow.natDegree_mul hB₀, natDegree_pow, natDegree_X_sub_C, mul_one,
      hP.natDegree_map] at h
    exact h.symm
  have hm : 0 < m := (rootMultiplicity_pos hp.ne_zero).mpr hroot
  have hvalue : B₀.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hp.ne_zero
  obtain ⟨A, B, hA, hAm, hB, hBn, hAres, hBres, hAB, hBne, hf, hinter⟩ :=
    exists_root_cluster_factorization_and_intersection P Q hP c m B₀.natDegree
      hm hdegree B₀ hB₀ rfl hvalue hfactor.symm hresultant
  refine ⟨A, B, hA, hB, hAm, ?_, ?_, ?_, hAB, hBne, hf, hinter⟩
  · rw [hAm, hBn, ← hdegree]
  · rwa [hAm]
  · rwa [hBres]

end OnLeConjecture.Analytic.Germ
