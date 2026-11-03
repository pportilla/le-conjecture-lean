/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.QuadraticInvariantMajorant
public import OnLeConjecture.Analytic.WeightedAntidiagonal
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Convergence estimates for quadratic invariant descent

This file develops coefficient estimates for a two variable analytic power
series. A homogeneous multilinear coefficient is expanded according to the
number of arguments on the first coordinate axis. The coefficients with even
first coordinate degree are then regrouped after the substitution
`u = x ^ 2`.
-/

public section

namespace OnLeConjecture.Analytic

open scoped BigOperators
open scoped NNReal ENNReal

namespace Germ

/-- The first coordinate vector in `Source 2`. -/
@[expose] noncomputable def firstAxis : Source 2 :=
  fun i ↦ if i = 0 then 1 else 0

/-- The second coordinate vector in `Source 2`. -/
@[expose] noncomputable def secondAxis : Source 2 :=
  fun i ↦ if i = 1 then 1 else 0

@[simp]
theorem firstAxis_apply_zero : Germ.firstAxis 0 = 1 := by
  simp [Germ.firstAxis]

@[simp]
theorem firstAxis_apply_one : Germ.firstAxis 1 = 0 := by
  simp [Germ.firstAxis]

@[simp]
theorem secondAxis_apply_zero : Germ.secondAxis 0 = 0 := by
  simp [Germ.secondAxis]

@[simp]
theorem secondAxis_apply_one : Germ.secondAxis 1 = 1 := by
  simp [Germ.secondAxis]

@[simp]
theorem norm_firstAxis : ‖Germ.firstAxis‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    fin_cases i <;> simp
  · simpa using norm_le_pi_norm Germ.firstAxis (0 : Fin 2)

@[simp]
theorem norm_secondAxis : ‖Germ.secondAxis‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    fin_cases i <;> simp
  · simpa using norm_le_pi_norm Germ.secondAxis (1 : Fin 2)

/-- A point in `Source 2` written in the coordinate basis. -/
@[expose] noncomputable def planePoint (x y : ℂ) : Source 2 :=
  x • Germ.firstAxis + y • Germ.secondAxis

@[simp]
theorem planePoint_apply_zero (x y : ℂ) :
    Germ.planePoint x y 0 = x := by
  simp [Germ.planePoint]

@[simp]
theorem planePoint_apply_one (x y : ℂ) :
    Germ.planePoint x y 1 = y := by
  simp [Germ.planePoint]

/-- The arguments used to extract the coefficient with first coordinate
degree `i` from a homogeneous multilinear map of degree `d`. -/
@[expose] noncomputable def mixedArguments (d : ℕ) (s : Finset (Fin d)) :
    Fin d → Source 2 :=
  s.piecewise (fun _ ↦ Germ.firstAxis) (fun _ ↦ Germ.secondAxis)

/-- The coefficient of first coordinate degree `i` obtained by expanding a
homogeneous multilinear coefficient of degree `d`. -/
@[expose] noncomputable def mixedCoefficient
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d i : ℕ) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard i,
    p d (Germ.mixedArguments d s)

/-- The coordinate projection selected by a position in a mixed monomial. -/
@[expose] noncomputable def mixedCoordinateProjection (m j : ℕ)
    (i : Fin (m + j)) : Source 2 →L[ℂ] ℂ :=
  if i.1 < m then
    ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)
  else
    ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)

/-- The multilinear map whose value on the diagonal is `u ^ m * y ^ j`. -/
@[expose] noncomputable def mixedMonomial (m j : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (m + j) ↦ Source 2) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ (m + j) ℂ).compContinuousLinearMap
    (Germ.mixedCoordinateProjection m j)

@[simp]
theorem mixedCoordinateProjection_apply_planePoint
    (m j : ℕ) (i : Fin (m + j)) (u y : ℂ) :
    Germ.mixedCoordinateProjection m j i (Germ.planePoint u y) =
      if i.1 < m then u else y := by
  by_cases hi : i.1 < m
  · simp [Germ.mixedCoordinateProjection, hi]
  · simp [Germ.mixedCoordinateProjection, hi]

/-- Evaluation of a mixed monomial on the diagonal. -/
theorem mixedMonomial_apply_diagonal (m j : ℕ) (u y : ℂ) :
    Germ.mixedMonomial m j
        (fun _ : Fin (m + j) ↦ Germ.planePoint u y) =
      u ^ m * y ^ j := by
  simp only [Germ.mixedMonomial,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    Germ.mixedCoordinateProjection_apply_planePoint]
  rw [List.prod_ofFn]
  rw [Fin.prod_univ_add]
  simp

/-- Every mixed coordinate monomial has operator norm at most one. -/
theorem norm_mixedMonomial_le_one (m j : ℕ) :
    ‖Germ.mixedMonomial m j‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro z
  simp only [Germ.mixedMonomial,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn,
    norm_prod]
  calc
    ∏ i, ‖Germ.mixedCoordinateProjection m j i (z i)‖ ≤
        ∏ i, ‖z i‖ := by
      apply Finset.prod_le_prod
      · intro i _
        exact norm_nonneg _
      · intro i _
        by_cases hi : i.1 < m
        · simp only [Germ.mixedCoordinateProjection, hi, if_pos,
            ContinuousLinearMap.proj_apply]
          exact norm_le_pi_norm (z i) (0 : Fin 2)
        · simp only [Germ.mixedCoordinateProjection, hi]
          exact norm_le_pi_norm (z i) (1 : Fin 2)
    _ = 1 * ∏ i, ‖z i‖ := by rw [one_mul]

/-- A mixed coefficient is bounded by the corresponding binomial coefficient
times the operator norm of the homogeneous coefficient. -/
theorem norm_mixedCoefficient_le
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d i : ℕ) :
    ‖Germ.mixedCoefficient p d i‖ ≤
      (d.choose i : ℝ) * ‖p d‖ := by
  classical
  calc
    ‖Germ.mixedCoefficient p d i‖ ≤
        ∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard i,
          ‖p d (Germ.mixedArguments d s)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin d)).powersetCard i,
          ‖p d‖ := by
      apply Finset.sum_le_sum
      intro s hs
      calc
        ‖p d (Germ.mixedArguments d s)‖ ≤
            ‖p d‖ * ∏ k, ‖Germ.mixedArguments d s k‖ :=
          (p d).le_opNorm _
        _ = ‖p d‖ := by
          have haxis (k : Fin d) :
              ‖Germ.mixedArguments d s k‖ = 1 := by
            by_cases hk : k ∈ s
            · simp [Germ.mixedArguments, hk]
            · simp [Germ.mixedArguments, hk]
          simp_rw [haxis]
          simp
    _ = (d.choose i : ℝ) * ‖p d‖ := by
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The binomial estimate with a power of two in place of the binomial
coefficient. -/
theorem norm_mixedCoefficient_le_pow_two
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d i : ℕ) :
    ‖Germ.mixedCoefficient p d i‖ ≤
      (2 : ℝ) ^ d * ‖p d‖ := by
  refine (Germ.norm_mixedCoefficient_le p d i).trans ?_
  gcongr
  exact_mod_cast Nat.choose_le_two_pow d i

/-- A term in the coordinate expansion of a homogeneous multilinear map. -/
theorem apply_piecewise_smul_axes
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (s : Finset (Fin d)) (x y : ℂ) :
    p d (s.piecewise (fun _ ↦ x • Germ.firstAxis)
        (fun _ ↦ y • Germ.secondAxis)) =
      x ^ s.card * y ^ (d - s.card) *
        p d (Germ.mixedArguments d s) := by
  classical
  let c : Fin d → ℂ := s.piecewise (fun _ ↦ x) (fun _ ↦ y)
  have harguments :
      s.piecewise (fun _ ↦ x • Germ.firstAxis)
          (fun _ ↦ y • Germ.secondAxis) =
        fun i ↦ c i • Germ.mixedArguments d s i := by
    funext i
    by_cases hi : i ∈ s
    · simp [c, Germ.mixedArguments, hi]
    · simp [c, Germ.mixedArguments, hi]
  rw [harguments, (p d).map_smul_univ]
  change (∏ i, c i) * p d (Germ.mixedArguments d s) = _
  congr 1
  simp only [c]
  rw [Finset.prod_piecewise]
  simp [Finset.card_sdiff_of_subset]

/-- Expansion of a homogeneous multilinear coefficient in the two coordinate
directions. -/
theorem homogeneous_apply_planePoint
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ) (x y : ℂ) :
    p d (fun _ : Fin d ↦ Germ.planePoint x y) =
      ∑ s : Finset (Fin d),
        x ^ s.card * y ^ (d - s.card) *
          p d (Germ.mixedArguments d s) := by
  classical
  have h := (p d).map_add_univ
    (fun _ : Fin d ↦ x • Germ.firstAxis)
    (fun _ : Fin d ↦ y • Germ.secondAxis)
  rw [show (fun _ : Fin d ↦ Germ.planePoint x y) =
      (fun _ : Fin d ↦ x • Germ.firstAxis) +
        (fun _ : Fin d ↦ y • Germ.secondAxis) by
      funext i
      rfl]
  rw [h]
  apply Finset.sum_congr rfl
  intro s hs
  exact Germ.apply_piecewise_smul_axes p d s x y

/-- Expansion grouped by the first coordinate degree. -/
theorem homogeneous_apply_planePoint_grouped
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ) (x y : ℂ) :
    p d (fun _ : Fin d ↦ Germ.planePoint x y) =
      ∑ i ∈ Finset.range (d + 1),
        x ^ i * y ^ (d - i) * Germ.mixedCoefficient p d i := by
  classical
  rw [Germ.homogeneous_apply_planePoint]
  rw [← Finset.powerset_univ (α := Fin d)]
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Germ.mixedCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsCard : s.card = i := (Finset.mem_powersetCard.mp hs).2
  rw [hsCard]

/-- The polynomial obtained from one homogeneous coefficient by setting the
second coordinate equal to one. -/
@[expose] noncomputable def mixedPolynomial
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.monomial i (Germ.mixedCoefficient p d i)

/-- Reflection of the first variable in `mixedPolynomial`. -/
@[expose] noncomputable def reflectedMixedPolynomial
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.monomial i
      (((-1 : ℂ) ^ i) * Germ.mixedCoefficient p d i)

theorem eval_mixedPolynomial
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ) (x : ℂ) :
    Polynomial.eval x (Germ.mixedPolynomial p d) =
      p d (fun _ : Fin d ↦ Germ.planePoint x 1) := by
  rw [Germ.homogeneous_apply_planePoint_grouped]
  rw [Germ.mixedPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_comm]

theorem eval_reflectedMixedPolynomial
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ) (x : ℂ) :
    Polynomial.eval x (Germ.reflectedMixedPolynomial p d) =
      p d (fun _ : Fin d ↦ Germ.planePoint (-x) 1) := by
  rw [Germ.homogeneous_apply_planePoint_grouped]
  rw [Germ.reflectedMixedPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [one_pow, mul_one]
  rw [show -x = (-1 : ℂ) * x by exact neg_eq_neg_one_mul x,
    mul_pow]
  ac_rfl

theorem coeff_mixedPolynomial {p : FormalMultilinearSeries ℂ (Source 2) ℂ}
    {d i : ℕ} (hi : i ≤ d) :
    (Germ.mixedPolynomial p d).coeff i = Germ.mixedCoefficient p d i := by
  classical
  simp [Germ.mixedPolynomial, Polynomial.coeff_monomial, hi]

theorem coeff_reflectedMixedPolynomial
    {p : FormalMultilinearSeries ℂ (Source 2) ℂ}
    {d i : ℕ} (hi : i ≤ d) :
    (Germ.reflectedMixedPolynomial p d).coeff i =
      (-1 : ℂ) ^ i * Germ.mixedCoefficient p d i := by
  classical
  simp [Germ.reflectedMixedPolynomial, Polynomial.coeff_monomial, hi]

/-- Reflection changes the sign of the first coordinate of a plane point. -/
theorem firstCoordinateReflection_planePoint (x y : ℂ) :
    Germ.firstCoordinateReflection (Germ.planePoint x y) =
      Germ.planePoint (-x) y := by
  ext i
  fin_cases i
  · simp
  · simp

/-- Odd mixed coefficients vanish when the diagonal homogeneous polynomial is
fixed by first coordinate reflection. -/
theorem mixedCoefficient_eq_zero_of_odd_of_diagonal_reflection
    {p : FormalMultilinearSeries ℂ (Source 2) ℂ} {d i : ℕ}
    (hreflection : ∀ z : Source 2,
      p d (fun _ : Fin d ↦ Germ.firstCoordinateReflection z) =
        p d (fun _ : Fin d ↦ z))
    (hi : i ≤ d) (hiOdd : Odd i) :
    Germ.mixedCoefficient p d i = 0 := by
  have hpolynomial : Germ.reflectedMixedPolynomial p d =
      Germ.mixedPolynomial p d := by
    apply Polynomial.funext
    intro x
    rw [Germ.eval_reflectedMixedPolynomial, Germ.eval_mixedPolynomial]
    rw [← Germ.firstCoordinateReflection_planePoint x 1]
    exact hreflection (Germ.planePoint x 1)
  have hcoeff := congrArg (Polynomial.coeff · i) hpolynomial
  rw [Germ.coeff_reflectedMixedPolynomial hi,
    Germ.coeff_mixedPolynomial hi, hiOdd.neg_one_pow, neg_one_mul] at hcoeff
  exact CharZero.neg_eq_self_iff.mp hcoeff

/-- Eventual reflection invariance of a function forces reflection invariance
of every diagonal homogeneous coefficient of any power series representing
the function. -/
theorem diagonal_reflection_of_hasFPowerSeriesAt
    {F : Source 2 → ℂ}
    {p : FormalMultilinearSeries ℂ (Source 2) ℂ}
    (hp : HasFPowerSeriesAt F p 0)
    (hreflection : (F ∘ Germ.firstCoordinateReflection) =ᶠ[nhds 0] F) :
    ∀ d (z : Source 2),
      p d (fun _ : Fin d ↦ Germ.firstCoordinateReflection z) =
        p d (fun _ : Fin d ↦ z) := by
  have hpReflection : HasFPowerSeriesAt
      (F ∘ Germ.firstCoordinateReflection)
      (p.compContinuousLinearMap Germ.firstCoordinateReflection) 0 := by
    have hpAtImage : HasFPowerSeriesAt F p
        (Germ.firstCoordinateReflection (0 : Source 2)) := by
      simpa using hp
    have h := hpAtImage.compContinuousLinearMap
      (u := Germ.firstCoordinateReflection) (x := (0 : Source 2))
    simpa using h
  have hpDifference : HasFPowerSeriesAt
      ((F ∘ Germ.firstCoordinateReflection) - F)
      (p.compContinuousLinearMap Germ.firstCoordinateReflection - p) 0 :=
    hpReflection.sub hp
  have hzero :
      ((F ∘ Germ.firstCoordinateReflection) - F) =ᶠ[nhds 0]
        (0 : Source 2 → ℂ) := by
    filter_upwards [hreflection] with z hz
    change F (Germ.firstCoordinateReflection z) - F z = 0
    change F (Germ.firstCoordinateReflection z) = F z at hz
    exact sub_eq_zero.mpr hz
  have hpZero : HasFPowerSeriesAt (0 : Source 2 → ℂ)
      (p.compContinuousLinearMap Germ.firstCoordinateReflection - p) 0 :=
    hpDifference.congr hzero
  intro d z
  have hcoeff := hpZero.apply_eq_zero d z
  simp only [FormalMultilinearSeries.compContinuousLinearMap_apply,
    FormalMultilinearSeries.sub_apply,
    sub_apply] at hcoeff
  change p d (fun _ : Fin d ↦ Germ.firstCoordinateReflection z) -
      p d (fun _ : Fin d ↦ z) = 0 at hcoeff
  exact sub_eq_zero.mp hcoeff

/-- Odd mixed coefficients vanish for an eventually reflection invariant
analytic function. -/
theorem mixedCoefficient_eq_zero_of_odd_of_eventually_reflection
    {F : Source 2 → ℂ}
    {p : FormalMultilinearSeries ℂ (Source 2) ℂ}
    (hp : HasFPowerSeriesAt F p 0)
    (hreflection : (F ∘ Germ.firstCoordinateReflection) =ᶠ[nhds 0] F)
    {d i : ℕ} (hi : i ≤ d) (hiOdd : Odd i) :
    Germ.mixedCoefficient p d i = 0 := by
  apply Germ.mixedCoefficient_eq_zero_of_odd_of_diagonal_reflection
    (Germ.diagonal_reflection_of_hasFPowerSeriesAt hp hreflection d)
    hi hiOdd

/-- A mixed monomial whose total degree has been identified with `k`. -/
@[expose] noncomputable def compressedMonomial (k : ℕ) (m : Fin (k + 1)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k ↦ Source 2) ℂ :=
  let hdegree : m.1 + (k - m.1) = k :=
    Nat.add_sub_of_le (Nat.lt_succ_iff.mp m.2)
  ContinuousMultilinearMap.domDomCongr
    (Fin.castOrderIso hdegree)
    (Germ.mixedMonomial m.1 (k - m.1))

/-- Evaluation of a compressed monomial on the diagonal. -/
theorem compressedMonomial_apply_diagonal (k : ℕ) (m : Fin (k + 1))
    (u y : ℂ) :
    Germ.compressedMonomial k m
        (fun _ : Fin k ↦ Germ.planePoint u y) =
      u ^ m.1 * y ^ (k - m.1) := by
  rw [Germ.compressedMonomial,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact Germ.mixedMonomial_apply_diagonal m.1 (k - m.1) u y

/-- A compressed monomial has operator norm at most one. -/
theorem norm_compressedMonomial_le_one (k : ℕ) (m : Fin (k + 1)) :
    ‖Germ.compressedMonomial k m‖ ≤ 1 := by
  rw [Germ.compressedMonomial,
    ContinuousMultilinearMap.norm_domDomCongr]
  exact Germ.norm_mixedMonomial_le_one m.1 (k - m.1)

/-- Regrouping the coefficients with even first coordinate degree after the
substitution `u = x ^ 2`. -/
@[expose] noncomputable def quadraticCompressedSeries
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) :
    FormalMultilinearSeries ℂ (Source 2) ℂ :=
  fun k ↦ ∑ m : Fin (k + 1),
    Germ.mixedCoefficient p (k + m.1) (2 * m.1) •
      Germ.compressedMonomial k m

/-- Evaluation of the compressed homogeneous coefficient on the diagonal. -/
theorem quadraticCompressedSeries_apply_diagonal
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (k : ℕ) (u y : ℂ) :
    Germ.quadraticCompressedSeries p k
        (fun _ : Fin k ↦ Germ.planePoint u y) =
      ∑ m : Fin (k + 1),
        Germ.mixedCoefficient p (k + m.1) (2 * m.1) *
          (u ^ m.1 * y ^ (k - m.1)) := by
  simp only [Germ.quadraticCompressedSeries, sum_apply, smul_apply,
    Germ.compressedMonomial_apply_diagonal, smul_eq_mul]

/-- The norm of a compressed homogeneous coefficient is bounded by the sum
of the corresponding binomial majorants. -/
theorem norm_quadraticCompressedSeries_le_sum
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (k : ℕ) :
    ‖Germ.quadraticCompressedSeries p k‖ ≤
      ∑ m : Fin (k + 1),
        (2 : ℝ) ^ (k + m.1) * ‖p (k + m.1)‖ := by
  calc
    ‖Germ.quadraticCompressedSeries p k‖ ≤
        ∑ m : Fin (k + 1),
          ‖Germ.mixedCoefficient p (k + m.1) (2 * m.1) •
            Germ.compressedMonomial k m‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ m : Fin (k + 1),
        (2 : ℝ) ^ (k + m.1) * ‖p (k + m.1)‖ := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        ‖Germ.mixedCoefficient p (k + m.1) (2 * m.1) •
            Germ.compressedMonomial k m‖ =
            ‖Germ.mixedCoefficient p (k + m.1) (2 * m.1)‖ *
              ‖Germ.compressedMonomial k m‖ := by
          rw [norm_smul]
        _ ≤ ‖Germ.mixedCoefficient p (k + m.1) (2 * m.1)‖ * 1 := by
          gcongr
          exact Germ.norm_compressedMonomial_le_one k m
        _ ≤ (2 : ℝ) ^ (k + m.1) * ‖p (k + m.1)‖ := by
          simpa using Germ.norm_mixedCoefficient_le_pow_two p
            (k + m.1) (2 * m.1)

/-- An exponential operator norm bound gives a positive convergence radius. -/
theorem radius_pos_of_norm_le_mul_pow
    (q : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {C R : ℝ} (_hC : 0 < C) (hR : 0 < R)
    (hq : ∀ k, ‖q k‖ ≤ C * R ^ k) :
    0 < q.radius := by
  let ρ : ℝ≥0 := ⟨R⁻¹, (inv_pos.mpr hR).le⟩
  have hρ : 0 < ρ := by
    exact_mod_cast inv_pos.mpr hR
  have hle : (ρ : ℝ≥0∞) ≤ q.radius := by
    apply q.le_radius_of_bound C
    intro k
    calc
      ‖q k‖ * (ρ : ℝ) ^ k ≤
          (C * R ^ k) * (ρ : ℝ) ^ k := by
        gcongr
        exact hq k
      _ = C := by
        change (C * R ^ k) * (R⁻¹) ^ k = C
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne', one_pow,
          mul_one]
  exact (show 0 < (ρ : ℝ≥0∞) by exact_mod_cast hρ).trans_le hle

/-- Compression of the even first coordinate coefficients preserves a
positive convergence radius. -/
theorem quadraticCompressedSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hp : 0 < p.radius) :
    0 < (Germ.quadraticCompressedSeries p).radius := by
  obtain ⟨C, r, hC, hr, hpBound⟩ := p.le_mul_pow_of_radius_pos hp
  let A : ℝ := max 1 (2 * r)
  let B : ℝ := 2 * A ^ 2
  have hAOne : 1 ≤ A := le_max_left _ _
  have hANonneg : 0 ≤ A := zero_le_one.trans hAOne
  have hB : 0 < B := mul_pos zero_lt_two (sq_pos_of_pos (zero_lt_one.trans_le hAOne))
  apply Germ.radius_pos_of_norm_le_mul_pow
    (Germ.quadraticCompressedSeries p) (mul_pos zero_lt_two hC) hB
  intro k
  refine (Germ.norm_quadraticCompressedSeries_le_sum p k).trans ?_
  calc
    (∑ m : Fin (k + 1),
        (2 : ℝ) ^ (k + m.1) * ‖p (k + m.1)‖) ≤
        ∑ _m : Fin (k + 1), C * A ^ (2 * k) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmle : m.1 ≤ k := Nat.lt_succ_iff.mp m.2
      have hdegree : k + m.1 ≤ 2 * k := by omega
      calc
        (2 : ℝ) ^ (k + m.1) * ‖p (k + m.1)‖ ≤
            (2 : ℝ) ^ (k + m.1) *
              (C * r ^ (k + m.1)) := by
          gcongr
          exact hpBound (k + m.1)
        _ = C * (2 * r) ^ (k + m.1) := by
          rw [mul_pow]
          ring
        _ ≤ C * A ^ (k + m.1) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg zero_le_two hr.le)
              (le_max_right _ _) _) hC.le
        _ ≤ C * A ^ (2 * k) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hAOne hdegree) hC.le
    _ = ((k + 1 : ℕ) : ℝ) * (C * A ^ (2 * k)) := by
      simp
    _ ≤ ((2 : ℝ) ^ (k + 1)) * (C * A ^ (2 * k)) := by
      gcongr
      exact_mod_cast Nat.le_of_lt (k + 1).lt_two_pow_self
    _ = (2 * C) * B ^ k := by
      simp only [B]
      rw [pow_add, pow_one, pow_mul]
      ring

/-- A term in the absolutely convergent coordinate expansion. -/
@[expose] noncomputable def mixedTerm
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (i j : ℕ) (x y : ℂ) : ℂ :=
  Germ.mixedCoefficient p (i + j) i * x ^ i * y ^ j

/-- A geometric bound on the homogeneous coefficients gives absolute
summability of the corresponding double coordinate series. -/
theorem summable_mixedTerm_of_geometric_bound
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {C r : ℝ} (_hC : 0 < C) (hr : 0 < r)
    (hp : ∀ d, ‖p d‖ ≤ C * r ^ d)
    {x y : ℂ}
    (hx : 2 * r * ‖x‖ < 1) (hy : 2 * r * ‖y‖ < 1) :
    Summable (fun z : ℕ × ℕ ↦
      Germ.mixedTerm p z.1 z.2 x y) := by
  let a : ℝ := 2 * r * ‖x‖
  let b : ℝ := 2 * r * ‖y‖
  have haNonneg : 0 ≤ a := mul_nonneg (mul_nonneg zero_le_two hr.le) (norm_nonneg x)
  have hbNonneg : 0 ≤ b := mul_nonneg (mul_nonneg zero_le_two hr.le) (norm_nonneg y)
  have haSummable : Summable (fun i : ℕ ↦ a ^ i) :=
    summable_geometric_of_lt_one haNonneg hx
  have hbSummable : Summable (fun j : ℕ ↦ b ^ j) :=
    summable_geometric_of_lt_one hbNonneg hy
  have habSummable : Summable (fun z : ℕ × ℕ ↦
      C * a ^ z.1 * b ^ z.2) := by
    have hproduct : Summable (fun z : ℕ × ℕ ↦ a ^ z.1 * b ^ z.2) :=
      haSummable.mul_of_nonneg hbSummable
        (fun i ↦ pow_nonneg haNonneg i) (fun j ↦ pow_nonneg hbNonneg j)
    simpa only [mul_assoc] using hproduct.mul_left C
  apply (Summable.of_nonneg_of_le
    (fun z ↦ norm_nonneg (Germ.mixedTerm p z.1 z.2 x y))
    (fun z ↦ ?_) habSummable).of_norm
  rcases z with ⟨i, j⟩
  change ‖Germ.mixedCoefficient p (i + j) i * x ^ i * y ^ j‖ ≤
    C * a ^ i * b ^ j
  calc
    ‖Germ.mixedCoefficient p (i + j) i * x ^ i * y ^ j‖ =
        ‖Germ.mixedCoefficient p (i + j) i‖ * ‖x‖ ^ i * ‖y‖ ^ j := by
      simp only [norm_mul, norm_pow]
    _ ≤ ((2 : ℝ) ^ (i + j) * ‖p (i + j)‖) *
          ‖x‖ ^ i * ‖y‖ ^ j := by
      gcongr
      exact Germ.norm_mixedCoefficient_le_pow_two p (i + j) i
    _ ≤ ((2 : ℝ) ^ (i + j) * (C * r ^ (i + j))) *
          ‖x‖ ^ i * ‖y‖ ^ j := by
      gcongr
      exact hp (i + j)
    _ = C * a ^ i * b ^ j := by
      simp only [a, b, pow_add, mul_pow]
      ring

/-- Reindexing a finite sum over even natural numbers. -/
theorem sum_even_range_eq {E : Type*} [AddCommMonoid E]
    (d : ℕ) (f : ℕ → E) :
    (∑ i ∈ Finset.range (d + 1), if Even i then f i else 0) =
      ∑ m : Fin (d / 2 + 1), f (2 * m.1) := by
  classical
  rw [← Finset.sum_filter]
  symm
  change (∑ m ∈ (Finset.univ : Finset (Fin (d / 2 + 1))),
      f (2 * m.1)) =
    ∑ i ∈ (Finset.range (d + 1)).filter Even, f i
  apply Finset.sum_nbij (fun m : Fin (d / 2 + 1) ↦ 2 * m.1)
  · intro m hm
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range]
      have hmle : m.1 ≤ d / 2 := Nat.lt_succ_iff.mp m.2
      have htwo : m.1 * 2 ≤ d := (Nat.le_div_iff_mul_le zero_lt_two).mp hmle
      omega
    · exact ⟨m.1, by omega⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    apply Fin.ext
    exact Nat.mul_left_cancel zero_lt_two heq
  · intro i hi
    change i ∈ (Finset.range (d + 1)).filter Even at hi
    rw [Finset.mem_filter] at hi
    rcases hi.2 with ⟨m, hm⟩
    have hile : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi.1)
    have hmi : m * 2 = i := by omega
    have hmle : m ≤ d / 2 := by
      apply (Nat.le_div_iff_mul_le zero_lt_two).mpr
      rw [hmi]
      exact hile
    refine ⟨⟨m, Nat.lt_succ_of_le hmle⟩, Finset.mem_univ _, ?_⟩
    change 2 * m = i
    omega
  · intro m hm
    rfl

/-- When all odd mixed coefficients vanish, a homogeneous coefficient is the
sum over its even first coordinate degrees. -/
theorem homogeneous_apply_planePoint_even
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ)
    (hodd : ∀ i, i ≤ d → Odd i → Germ.mixedCoefficient p d i = 0)
    (x y : ℂ) :
    p d (fun _ : Fin d ↦ Germ.planePoint x y) =
      ∑ m : Fin (d / 2 + 1),
        Germ.mixedCoefficient p d (2 * m.1) *
          x ^ (2 * m.1) * y ^ (d - 2 * m.1) := by
  rw [Germ.homogeneous_apply_planePoint_grouped]
  let term : ℕ → ℂ := fun i ↦
    x ^ i * y ^ (d - i) * Germ.mixedCoefficient p d i
  calc
    (∑ i ∈ Finset.range (d + 1),
        x ^ i * y ^ (d - i) * Germ.mixedCoefficient p d i) =
        ∑ i ∈ Finset.range (d + 1),
          if Even i then term i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases i.even_or_odd with hiEven | hiOdd
      · simp [hiEven, term]
      · rw [if_neg (Nat.not_even_iff_odd.mpr hiOdd)]
        have hile : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        rw [hodd i hile hiOdd]
        simp
    _ = ∑ m : Fin (d / 2 + 1), term (2 * m.1) :=
      sum_even_range_eq d term
    _ = ∑ m : Fin (d / 2 + 1),
        Germ.mixedCoefficient p d (2 * m.1) *
          x ^ (2 * m.1) * y ^ (d - 2 * m.1) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [term]
      ring

/-- A coordinate term after replacing the first coordinate by its square. -/
@[expose] noncomputable def quadraticMixedTerm
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (m j : ℕ) (x y : ℂ) : ℂ :=
  Germ.mixedCoefficient p (2 * m + j) (2 * m) *
    (x ^ 2) ^ m * y ^ j

/-- The double series obtained from the even first coordinate coefficients is
absolutely summable on a sufficiently small coordinate polydisc. -/
theorem summable_quadraticMixedTerm_of_geometric_bound
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hp : ∀ d, ‖p d‖ ≤ C * r ^ d)
    {x y : ℂ}
    (hx : 2 * r * ‖x‖ < 1) (hy : 2 * r * ‖y‖ < 1) :
    Summable (fun z : ℕ × ℕ ↦
      Germ.quadraticMixedTerm p z.1 z.2 x y) := by
  have hall := Germ.summable_mixedTerm_of_geometric_bound
    p hC hr hp hx hy
  have hinjective : Function.Injective
      (fun z : ℕ × ℕ ↦ (2 * z.1, z.2)) := by
    intro z w hzw
    have hfirst := congrArg (fun q : ℕ × ℕ ↦ q.1) hzw
    have hsecond := congrArg (fun q : ℕ × ℕ ↦ q.2) hzw
    apply Prod.ext
    · exact Nat.mul_left_cancel zero_lt_two
        hfirst
    · exact hsecond
  have heven := hall.comp_injective hinjective
  refine heven.congr (fun z ↦ ?_)
  simp only [Function.comp_apply, Germ.quadraticMixedTerm,
    Germ.mixedTerm, pow_mul]

/-- Grouping the compressed double series by the ordinary total degree gives
the sum of the compressed formal multilinear series. -/
theorem quadraticCompressedSeries_sum_eq_tsum_quadraticMixedTerm
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {x y : ℂ}
    (hsum : Summable (fun z : ℕ × ℕ ↦
      Germ.quadraticMixedTerm p z.1 z.2 x y)) :
    (Germ.quadraticCompressedSeries p).sum
        (Germ.planePoint (x ^ 2) y) =
      ∑' z : ℕ × ℕ, Germ.quadraticMixedTerm p z.1 z.2 x y := by
  have hgrouped := tsum_weightedAntidiagonal 1 zero_lt_one
    (fun m j ↦ Germ.quadraticMixedTerm p m j x y) hsum
  rw [FormalMultilinearSeries.sum]
  rw [← hgrouped]
  apply tsum_congr
  intro k
  rw [Germ.quadraticCompressedSeries_apply_diagonal]
  let e : Fin (k + 1) ≃ Fin (k / 1 + 1) :=
    (Fin.castOrderIso (by omega)).toEquiv
  apply Fintype.sum_equiv e
  intro m
  simp only [Germ.quadraticMixedTerm, one_mul]
  have hem : (e m).1 = m.1 := by
    rfl
  rw [hem]
  have hdegree : 2 * m.1 + (k - m.1) = k + m.1 := by
    omega
  rw [hdegree]
  ring

/-- Grouping the even coordinate terms by the original total degree recovers
the sum of a reflection invariant formal multilinear series. -/
theorem formalSeries_sum_eq_tsum_quadraticMixedTerm
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hreflection : ∀ d (z : Source 2),
      p d (fun _ : Fin d ↦ Germ.firstCoordinateReflection z) =
        p d (fun _ : Fin d ↦ z))
    {x y : ℂ}
    (hsum : Summable (fun z : ℕ × ℕ ↦
      Germ.quadraticMixedTerm p z.1 z.2 x y)) :
    p.sum (Germ.planePoint x y) =
      ∑' z : ℕ × ℕ, Germ.quadraticMixedTerm p z.1 z.2 x y := by
  have hgrouped := tsum_weightedAntidiagonal 2 zero_lt_two
    (fun m j ↦ Germ.quadraticMixedTerm p m j x y) hsum
  rw [FormalMultilinearSeries.sum]
  rw [← hgrouped]
  apply tsum_congr
  intro d
  rw [Germ.homogeneous_apply_planePoint_even p d
    (fun i hi hiOdd ↦
      Germ.mixedCoefficient_eq_zero_of_odd_of_diagonal_reflection
        (hreflection d) hi hiOdd)]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Germ.quadraticMixedTerm]
  have hmle : 2 * m.1 ≤ d := by
    have hm' : m.1 ≤ d / 2 := Nat.lt_succ_iff.mp m.2
    have := (Nat.le_div_iff_mul_le zero_lt_two).mp hm'
    omega
  rw [show 2 * m.1 + (d - 2 * m.1) = d by omega]
  rw [pow_mul]

/-- On a sufficiently small polydisc, quadratic substitution in the
compressed series recovers the original reflection invariant series. -/
theorem quadraticCompressedSeries_sum_quadratic_eq
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (hp : ∀ d, ‖p d‖ ≤ C * r ^ d)
    (hreflection : ∀ d (z : Source 2),
      p d (fun _ : Fin d ↦ Germ.firstCoordinateReflection z) =
        p d (fun _ : Fin d ↦ z))
    {x y : ℂ}
    (hx : 2 * r * ‖x‖ < 1) (hy : 2 * r * ‖y‖ < 1) :
    (Germ.quadraticCompressedSeries p).sum
        (Germ.planePoint (x ^ 2) y) =
      p.sum (Germ.planePoint x y) := by
  have hsum := Germ.summable_quadraticMixedTerm_of_geometric_bound
    p hC hr hp hx hy
  rw [Germ.quadraticCompressedSeries_sum_eq_tsum_quadraticMixedTerm p hsum,
    Germ.formalSeries_sum_eq_tsum_quadraticMixedTerm p hreflection hsum]

@[simp]
theorem planePoint_coordinates (z : Source 2) :
    Germ.planePoint (z 0) (z 1) = z := by
  ext i
  fin_cases i <;> simp

theorem quadraticMap_eq_planePoint (z : Source 2) :
    Germ.quadraticMap z = Germ.planePoint (z 0 ^ 2) (z 1) := by
  ext i
  fin_cases i <;> simp

/-- Each coordinate is small enough for the geometric majorant in some
neighborhood of the origin. -/
theorem eventually_geometric_coordinate_bound {r : ℝ} (hr : 0 < r)
    (i : Fin 2) :
    ∀ᶠ z : Source 2 in nhds 0, 2 * r * ‖z i‖ < 1 := by
  have htwoR : 0 < 2 * r := mul_pos zero_lt_two hr
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨(2 * r)⁻¹, inv_pos.mpr htwoR, ?_⟩
  intro z hz
  have hzNorm : ‖z‖ < (2 * r)⁻¹ := by
    simpa only [dist_zero_right] using hz
  have hzi : ‖z i‖ < (2 * r)⁻¹ :=
    (norm_le_pi_norm z i).trans_lt hzNorm
  calc
    2 * r * ‖z i‖ < 2 * r * (2 * r)⁻¹ :=
      mul_lt_mul_of_pos_left hzi htwoR
    _ = 1 := mul_inv_cancel₀ htwoR.ne'

/-- Reflection invariant analytic germs descend through the quadratic map. -/
theorem quadraticInvariantDescent_of_convergent_compression :
    Germ.QuadraticInvariantDescent := by
  intro f hfInvariant
  rcases f with ⟨f, hf⟩
  change IsAnalyticGerm f at hf
  induction f using Filter.Germ.inductionOn with
  | _ F =>
      rw [isAnalyticGerm_ofFun] at hf
      change Germ.reflectionAlgEquiv (Germ.ofFunction F hf) =
        Germ.ofFunction F hf at hfInvariant
      have hreflection :
          (F ∘ Germ.firstCoordinateReflection) =ᶠ[nhds 0] F := by
        rw [Germ.reflectionAlgEquiv,
          PointedEquivGerm.pullbackAlgEquiv_apply,
          PointedEquivGerm.pullbackRingEquiv_apply] at hfInvariant
        change Germ.compPointed (Germ.ofFunction F hf)
            Germ.firstCoordinateReflectionGerm =
          Germ.ofFunction F hf at hfInvariant
        rw [Germ.firstCoordinateReflectionGerm,
          Germ.compPointed_ofFunction] at hfInvariant
        apply Filter.Germ.coe_eq.mp
        exact congrArg Subtype.val hfInvariant
      rcases hf with ⟨p, hp⟩
      let q := Germ.quadraticCompressedSeries p
      have hqRadius : 0 < q.radius :=
        Germ.quadraticCompressedSeries_radius_pos p hp.radius_pos
      have hqAnalytic : AnalyticAt ℂ q.sum 0 :=
        (q.hasFPowerSeriesOnBall hqRadius).analyticAt
      refine ⟨Germ.ofFunction q.sum hqAnalytic, ?_⟩
      obtain ⟨C, r, hC, hr, hpBound⟩ :=
        p.le_mul_pow_of_radius_pos hp.radius_pos
      have hpReflection :=
        Germ.diagonal_reflection_of_hasFPowerSeriesAt hp hreflection
      have hpSum : HasFPowerSeriesAt p.sum p 0 :=
        (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
      have hFSeries : F =ᶠ[nhds 0] p.sum := by
        filter_upwards [hp.eventually_hasSum_sub,
          hpSum.eventually_hasSum_sub] with z hzF hzSum
        simpa only [sub_zero] using hzF.unique hzSum
      have hxSmall :=
        Germ.eventually_geometric_coordinate_bound hr (0 : Fin 2)
      have hySmall :=
        Germ.eventually_geometric_coordinate_bound hr (1 : Fin 2)
      rw [Germ.quadraticSubstitutionAlgHom]
      change Germ.compPointed (Germ.ofFunction q.sum hqAnalytic)
          Germ.quadraticMapGerm = Germ.ofFunction F ⟨p, hp⟩
      rw [Germ.quadraticMapGerm, Germ.compPointed_ofFunction]
      apply Germ.ofFunction_eq_of_eventuallyEq
      filter_upwards [hxSmall, hySmall, hFSeries] with z hx hy hzF
      change q.sum (Germ.quadraticMap z) = F z
      rw [Germ.quadraticMap_eq_planePoint]
      calc
        q.sum (Germ.planePoint (z 0 ^ 2) (z 1)) =
            p.sum (Germ.planePoint (z 0) (z 1)) := by
          exact Germ.quadraticCompressedSeries_sum_quadratic_eq
            p hC hr hpBound hpReflection hx hy
        _ = p.sum z := by rw [Germ.planePoint_coordinates]
        _ = F z := hzF.symm

/-- The completed analytic Taylor image is closed under compression of even
outer coefficients. -/
theorem evenOuterTaylorImageClosure : Germ.EvenOuterTaylorImageClosure :=
  Germ.evenOuterTaylorImageClosure_iff_quadraticInvariantDescent.mpr
    Germ.quadraticInvariantDescent_of_convergent_compression

end Germ

end OnLeConjecture.Analytic
