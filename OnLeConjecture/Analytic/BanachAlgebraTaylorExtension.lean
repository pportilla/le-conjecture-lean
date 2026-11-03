/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CubicResidueConvergence
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Extension of scalar Taylor series to Banach algebras

A convergent scalar Taylor series in two commuting variables can be evaluated
in a complex Banach algebra. The construction in this file will be applied to
an endomorphism algebra and a scalar multiple of its identity.
-/

public section

namespace OnLeConjecture.Analytic

open scoped BigOperators NNReal ENNReal

namespace Germ

variable {A : Type*} [NormedRing A]
  [NormedAlgebra ℂ A] [NormOneClass A]

omit [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] in
private theorem algebraPairProjection_diagonal_list
    (m j : ℕ) (X Y : A) :
    List.map (fun i : Fin (m + j) ↦ if i.1 < m then X else Y)
        (List.finRange (m + j)) =
      List.replicate m X ++ List.replicate j Y := by
  apply List.ext_getElem
  · simp
  · intro n hnleft hnright
    simp only [List.length_map, List.length_finRange] at hnleft
    by_cases hn : n < m
    · simp [List.getElem_map, hn]
    · have hnj : n - m < j := by omega
      simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast, hn,
        ↓reduceIte]
      rw [List.getElem_append_right (by simpa using le_of_not_gt hn)]
      symm
      exact List.getElem_replicate (by simpa using hnj)

/-- Select one of the two algebra coordinates in a multilinear monomial. -/
@[expose] noncomputable def algebraPairProjection (m j : ℕ)
    (i : Fin (m + j)) : A × A →L[ℂ] A :=
  if i.1 < m then
    ContinuousLinearMap.fst ℂ A A
  else
    ContinuousLinearMap.snd ℂ A A

omit [NormOneClass A] in
@[simp]
theorem algebraPairProjection_apply
    (m j : ℕ) (i : Fin (m + j)) (X Y : A) :
    Germ.algebraPairProjection m j i (X, Y) =
      if i.1 < m then X else Y := by
  by_cases hi : i.1 < m <;>
    simp [Germ.algebraPairProjection, hi]

/-- The ordered algebra monomial which evaluates to `X ^ m * Y ^ j`. -/
@[expose] noncomputable def algebraMixedMonomial (m j : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (m + j) ↦ A × A) A :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ (m + j) A).compContinuousLinearMap
    (Germ.algebraPairProjection m j)

omit [NormOneClass A] in
@[simp]
theorem algebraMixedMonomial_apply_diagonal
    (m j : ℕ) (X Y : A) :
    Germ.algebraMixedMonomial m j
        (fun _ : Fin (m + j) ↦ (X, Y)) =
      X ^ m * Y ^ j := by
  simp only [Germ.algebraMixedMonomial,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_eq_map,
    Germ.algebraPairProjection_apply]
  rw [algebraPairProjection_diagonal_list]
  simp

/-- The operator norm of an ordered algebra monomial is at most one. -/
theorem norm_algebraMixedMonomial_le_one (m j : ℕ) :
    ‖Germ.algebraMixedMonomial (A := A) m j‖ ≤ 1 := by
  calc
    ‖Germ.algebraMixedMonomial (A := A) m j‖ ≤
        ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ (m + j) A‖ *
          ∏ i, ‖Germ.algebraPairProjection m j i‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * ∏ _i : Fin (m + j), 1 := by
      apply mul_le_mul
      · simp
      · apply Finset.prod_le_prod
        · intro i hi
          exact norm_nonneg (Germ.algebraPairProjection (A := A) m j i)
        · intro i hi
          by_cases hindex : i.1 < m
          · rw [Germ.algebraPairProjection, if_pos hindex]
            exact ContinuousLinearMap.norm_fst_le ℂ A A
          · rw [Germ.algebraPairProjection, if_neg hindex]
            exact ContinuousLinearMap.norm_snd_le ℂ A A
      · positivity
      · positivity
    _ = 1 := by simp

/-- A monomial whose total degree has been identified with `d`. -/
@[expose] noncomputable def algebraHomogeneousMonomial
    (d : ℕ) (i : Fin (d + 1)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin d ↦ A × A) A :=
  let hdegree : i.1 + (d - i.1) = d :=
    Nat.add_sub_of_le (Nat.lt_succ_iff.mp i.2)
  ContinuousMultilinearMap.domDomCongr
    (Fin.castOrderIso hdegree)
    (Germ.algebraMixedMonomial i.1 (d - i.1))

omit [NormOneClass A] in
@[simp]
theorem algebraHomogeneousMonomial_apply_diagonal
    (d : ℕ) (i : Fin (d + 1)) (X Y : A) :
    Germ.algebraHomogeneousMonomial d i (fun _ : Fin d ↦ (X, Y)) =
      X ^ i.1 * Y ^ (d - i.1) := by
  rw [Germ.algebraHomogeneousMonomial,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact Germ.algebraMixedMonomial_apply_diagonal i.1 (d - i.1) X Y

/-- Every homogeneous algebra monomial has operator norm at most one. -/
theorem norm_algebraHomogeneousMonomial_le_one
    (d : ℕ) (i : Fin (d + 1)) :
    ‖Germ.algebraHomogeneousMonomial (A := A) d i‖ ≤ 1 := by
  calc
    ‖Germ.algebraHomogeneousMonomial (A := A) d i‖ =
        ‖Germ.algebraMixedMonomial (A := A) i.1 (d - i.1)‖ := by
      exact ContinuousMultilinearMap.norm_domDomCongr ℂ (A × A) A _ _
    _ ≤ 1 := Germ.norm_algebraMixedMonomial_le_one i.1 (d - i.1)

/-- Extension of a scalar two variable Taylor series to an ordered Banach
algebra evaluation. -/
@[expose] noncomputable def banachAlgebraExtensionSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) :
    FormalMultilinearSeries ℂ (A × A) A :=
  fun d ↦ ∑ i : Fin (d + 1),
    Germ.mixedCoefficient p d i.1 •
      Germ.algebraHomogeneousMonomial d i

omit [NormOneClass A] in
/-- Evaluation of one homogeneous coefficient of the extended series. -/
theorem banachAlgebraExtensionSeries_apply_diagonal
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (d : ℕ) (X Y : A) :
    Germ.banachAlgebraExtensionSeries p d
        (fun _ : Fin d ↦ (X, Y)) =
      ∑ i : Fin (d + 1),
        (algebraMap ℂ A) (Germ.mixedCoefficient p d i.1) *
          (X ^ i.1 * Y ^ (d - i.1)) := by
  simp only [Germ.banachAlgebraExtensionSeries, sum_apply, smul_apply,
    Germ.algebraHomogeneousMonomial_apply_diagonal, Algebra.smul_def]

/-- The norm of an extended homogeneous coefficient is bounded by a uniform
exponential multiple of the original coefficient norm. -/
theorem norm_banachAlgebraExtensionSeries_le
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ) :
    ‖Germ.banachAlgebraExtensionSeries (A := A) p d‖ ≤
      (2 : ℝ) ^ (2 * d + 1) * ‖p d‖ := by
  calc
    ‖Germ.banachAlgebraExtensionSeries (A := A) p d‖ ≤
        ∑ i : Fin (d + 1),
          ‖Germ.mixedCoefficient p d i.1 •
            Germ.algebraHomogeneousMonomial (A := A) d i‖ :=
      by
        simpa [Germ.banachAlgebraExtensionSeries] using
          norm_sum_le Finset.univ
            (fun i : Fin (d + 1) ↦
              Germ.mixedCoefficient p d i.1 •
                Germ.algebraHomogeneousMonomial (A := A) d i)
    _ ≤ ∑ _i : Fin (d + 1), (2 : ℝ) ^ d * ‖p d‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖Germ.mixedCoefficient p d i.1 •
            Germ.algebraHomogeneousMonomial (A := A) d i‖ ≤
            ‖Germ.mixedCoefficient p d i.1‖ *
              ‖Germ.algebraHomogeneousMonomial (A := A) d i‖ :=
          ContinuousMultilinearMap.opNorm_smul_le _ _
        _ ≤ ‖Germ.mixedCoefficient p d i.1‖ * 1 := by
          gcongr
          exact Germ.norm_algebraHomogeneousMonomial_le_one d i
        _ ≤ (2 : ℝ) ^ d * ‖p d‖ := by
          simpa using Germ.norm_mixedCoefficient_le_pow_two p d i.1
    _ = ((d + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ d * ‖p d‖) := by
      simp
    _ ≤ (2 : ℝ) ^ (d + 1) * ((2 : ℝ) ^ d * ‖p d‖) := by
      gcongr
      exact_mod_cast Nat.le_of_lt (d + 1).lt_two_pow_self
    _ = (2 : ℝ) ^ (2 * d + 1) * ‖p d‖ := by
      rw [show 2 * d + 1 = (d + 1) + d by omega, pow_add]
      ring

/-- An exponential coefficient bound gives a positive convergence radius in
an arbitrary complex normed domain. -/
theorem radius_pos_of_norm_le_mul_pow_general
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (q : FormalMultilinearSeries ℂ E F)
    {C R : ℝ} (_hC : 0 < C) (hR : 0 < R)
    (hq : ∀ k, ‖q k‖ ≤ C * R ^ k) :
    0 < q.radius := by
  let rho : ℝ≥0 := ⟨R⁻¹, (inv_pos.mpr hR).le⟩
  have hrho : 0 < rho := by
    exact_mod_cast inv_pos.mpr hR
  have hle : (rho : ℝ≥0∞) ≤ q.radius := by
    apply q.le_radius_of_bound C
    intro k
    calc
      ‖q k‖ * (rho : ℝ) ^ k ≤
          (C * R ^ k) * (rho : ℝ) ^ k := by
        gcongr
        exact hq k
      _ = C := by
        change (C * R ^ k) * (R⁻¹) ^ k = C
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne', one_pow,
          mul_one]
  exact (show 0 < (rho : ℝ≥0∞) by exact_mod_cast hrho).trans_le hle

/-- Banach algebra extension preserves a positive convergence radius. -/
theorem banachAlgebraExtensionSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius) :
    0 < (Germ.banachAlgebraExtensionSeries (A := A) p).radius := by
  obtain ⟨C, R, hC, hR, hpBound⟩ := p.le_mul_pow_of_radius_pos hp
  apply Germ.radius_pos_of_norm_le_mul_pow_general
    (C := 2 * C) (R := 4 * R)
    (Germ.banachAlgebraExtensionSeries (A := A) p)
      (mul_pos zero_lt_two hC) (mul_pos (by norm_num) hR)
  intro d
  refine (Germ.norm_banachAlgebraExtensionSeries_le
    (A := A) p d).trans ?_
  calc
    (2 : ℝ) ^ (2 * d + 1) * ‖p d‖ ≤
        (2 : ℝ) ^ (2 * d + 1) * (C * R ^ d) := by
      gcongr
      exact hpBound d
    _ = (2 * C) * (4 * R) ^ d := by
      rw [show 2 * d + 1 = 1 + 2 * d by omega, pow_add, pow_mul]
      ring

end Germ

end OnLeConjecture.Analytic
