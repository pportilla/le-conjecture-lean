/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BanachAlgebraTaylorExtension
public import OnLeConjecture.Analytic.GeneralDivisionState

/-!
# Banach algebra extension in finitely many coordinates

A scalar Taylor coefficient is expanded over coordinate words. Each word
defines an ordered multilinear algebra monomial with norm at most one.
The resulting extension in `n` coordinates has coefficient norm at most
`n^d` times the original degree `d` coefficient norm, and hence converges
on a neighborhood whenever the scalar Taylor series does.
-/

public section

open scoped BigOperators NNReal ENNReal

namespace OnLeConjecture.Analytic.Germ

@[simp]
theorem norm_coordinateVector {n : ℕ} (i : Fin n) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector, Pi.norm_single]

/-- The coefficient indexed by an ordered word of scalar coordinates. -/
@[expose] noncomputable def coordinateWordCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (d : ℕ) (w : Fin d → Fin n) : ℂ :=
  p d (fun i => coordinateVector (w i))

theorem norm_coordinateWordCoefficient_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (d : ℕ) (w : Fin d → Fin n) :
    ‖coordinateWordCoefficient p d w‖ ≤ ‖p d‖ := by
  simpa [coordinateWordCoefficient] using
    (p d).le_opNorm (fun i => coordinateVector (w i))

/-- Expansion of a scalar homogeneous coefficient over coordinate words.
-/
theorem homogeneous_apply_coordinateWords {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (d : ℕ) (z : Source n) :
    p d (fun _ => z) = ∑ w : Fin d → Fin n,
      coordinateWordCoefficient p d w * ∏ i, z (w i) := by
  classical
  have hz : ∑ j : Fin n, z j • coordinateVector j = z := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  calc
    p d (fun _ => z) = p d (fun _ => ∑ j : Fin n, z j • coordinateVector j) := by rw [hz]
    _ = ∑ w : Fin d → Fin n, p d (fun i => z (w i) • coordinateVector (w i)) :=
      (p d).toMultilinearMap.map_sum (fun _ j => z j • coordinateVector j)
    _ = ∑ w : Fin d → Fin n, coordinateWordCoefficient p d w * ∏ i, z (w i) := by
      apply Finset.sum_congr rfl
      intro w _hw
      rw [(p d).map_smul_univ]
      simp [coordinateWordCoefficient, mul_comm]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]

/-- The ordered algebra monomial selected by a word of coordinates. -/
@[expose] noncomputable def coordinateWordMonomial {n d : ℕ} (w : Fin d → Fin n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin d => Fin n → A) A :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ d A).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (R := ℂ) (w i))

omit [NormOneClass A] in
@[simp]
theorem coordinateWordMonomial_apply_diagonal {n d : ℕ}
    (w : Fin d → Fin n) (X : Fin n → A) :
    coordinateWordMonomial w (fun _ => X) = (List.ofFn fun i => X (w i)).prod := by
  simp [coordinateWordMonomial, ContinuousMultilinearMap.mkPiAlgebraFin_apply]

theorem norm_coordinateWordMonomial_le_one {n d : ℕ} (w : Fin d → Fin n) :
    ‖coordinateWordMonomial (A := A) w‖ ≤ 1 := by
  calc
    ‖coordinateWordMonomial (A := A) w‖ ≤
        ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ d A‖ *
          ∏ i, ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => A) (w i)‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * ∏ _i : Fin d, 1 := by
      apply mul_le_mul
      · simp
      · apply Finset.prod_le_prod
        · intro i _hi
          positivity
        · intro i _hi
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro z
          simpa using norm_le_pi_norm z (w i)
      · positivity
      · positivity
    _ = 1 := by simp

/-- The ordered Banach algebra extension of a scalar Taylor series in any
finite number of variables. -/
@[expose] noncomputable def finiteBanachExtensionSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) :
    FormalMultilinearSeries ℂ (Fin n → A) A :=
  fun d => ∑ w : Fin d → Fin n,
    coordinateWordCoefficient p d w • coordinateWordMonomial w

omit [NormOneClass A] in
theorem finiteBanachExtensionSeries_apply_diagonal {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (d : ℕ) (X : Fin n → A) :
    finiteBanachExtensionSeries p d (fun _ => X) =
      ∑ w : Fin d → Fin n, coordinateWordCoefficient p d w •
        (List.ofFn fun i => X (w i)).prod := by
  simp only [finiteBanachExtensionSeries, sum_apply, smul_apply,
    coordinateWordMonomial_apply_diagonal]

set_option maxHeartbeats 800000 in
-- Elaborating the finite word sum expands several multilinear-map instances.
theorem norm_finiteBanachExtensionSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (d : ℕ) :
    ‖finiteBanachExtensionSeries (A := A) p d‖ ≤ (n : ℝ) ^ d * ‖p d‖ := by
  calc
    ‖finiteBanachExtensionSeries (A := A) p d‖ ≤
        ∑ w : Fin d → Fin n,
          ‖coordinateWordCoefficient p d w • coordinateWordMonomial (A := A) w‖ :=
      by
        simpa only [finiteBanachExtensionSeries] using
          norm_sum_le Finset.univ (fun w : Fin d → Fin n =>
            coordinateWordCoefficient p d w • coordinateWordMonomial (A := A) w)
    _ ≤ ∑ _w : Fin d → Fin n, ‖p d‖ := by
      apply Finset.sum_le_sum
      intro w _hw
      calc
        ‖coordinateWordCoefficient p d w • coordinateWordMonomial (A := A) w‖ ≤
            ‖coordinateWordCoefficient p d w‖ * ‖coordinateWordMonomial (A := A) w‖ :=
          ContinuousMultilinearMap.opNorm_smul_le _ _
        _ ≤ ‖p d‖ * 1 := by
          gcongr
          · exact norm_coordinateWordCoefficient_le p d w
          · exact norm_coordinateWordMonomial_le_one w
        _ = ‖p d‖ := mul_one _
    _ = (n : ℝ) ^ d * ‖p d‖ := by simp

/-- The finite-coordinate Banach extension has positive convergence
radius, including the zero-variable case. -/
theorem finiteBanachExtensionSeries_radius_pos {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (hp : 0 < p.radius) :
    0 < (finiteBanachExtensionSeries (A := A) p).radius := by
  obtain ⟨C, R, hC, hR, hpBound⟩ := p.le_mul_pow_of_radius_pos hp
  apply radius_pos_of_norm_le_mul_pow_general
    (C := C) (R := ((n : ℝ) + 1) * R)
    (finiteBanachExtensionSeries (A := A) p) hC (mul_pos (by positivity) hR)
  intro d
  calc
    ‖finiteBanachExtensionSeries (A := A) p d‖ ≤ (n : ℝ) ^ d * ‖p d‖ :=
      norm_finiteBanachExtensionSeries_le p d
    _ ≤ ((n : ℝ) + 1) ^ d * (C * R ^ d) := by
      gcongr
      · exact le_add_of_nonneg_right zero_le_one
      · exact hpBound d
    _ = C * (((n : ℝ) + 1) * R) ^ d := by rw [mul_pow]; ring

set_option maxHeartbeats 800000 in
-- The analytic-series theorem elaborates the nested Banach algebra instances.
/-- The convergent extension defines an analytic function on a neighborhood
of the zero tuple in the Banach algebra. -/
theorem finiteBanachExtensionSeries_analyticAt [CompleteSpace A] {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (hp : 0 < p.radius) :
    AnalyticAt ℂ (finiteBanachExtensionSeries (A := A) p).sum 0 :=
  ((finiteBanachExtensionSeries (A := A) p).hasFPowerSeriesOnBall
    (finiteBanachExtensionSeries_radius_pos (A := A) p hp)).hasFPowerSeriesAt.analyticAt

/-- The extension is analytic at each point in its convergence ball. -/
theorem finiteBanachExtensionSeries_analyticAt_of_mem [CompleteSpace A] {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (hp : 0 < p.radius)
    (X : Fin n → A)
    (hX : X ∈ Metric.eball 0 (finiteBanachExtensionSeries (A := A) p).radius) :
    AnalyticAt ℂ (finiteBanachExtensionSeries (A := A) p).sum X := by
  exact ((finiteBanachExtensionSeries (A := A) p).hasFPowerSeriesOnBall
    (finiteBanachExtensionSeries_radius_pos (A := A) p hp)).analyticAt_of_mem hX

omit [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] in
/-- Scalar evaluation of each extended coefficient recovers the original
homogeneous polynomial. -/
theorem finiteBanachExtensionSeries_scalar_diagonal {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (d : ℕ) (z : Source n) :
    finiteBanachExtensionSeries (A := ℂ) p d (fun _ => z) = p d (fun _ => z) := by
  rw [finiteBanachExtensionSeries_apply_diagonal, homogeneous_apply_coordinateWords]
  simp only [List.prod_ofFn, smul_eq_mul]

omit [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] in
/-- Scalar evaluation of the full extension agrees with the original
Taylor-series sum. -/
theorem finiteBanachExtensionSeries_scalar_sum {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (z : Source n) :
    (finiteBanachExtensionSeries (A := ℂ) p).sum z = p.sum z := by
  apply tsum_congr
  intro d
  exact finiteBanachExtensionSeries_scalar_diagonal p d z

section EndomorphismEvaluation

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]

/-- A scalar evaluation functional intertwines an ordered product of
endomorphisms with the corresponding product of scalar coordinates. -/
theorem linearEvaluation_list_prod {n : ℕ} (L : S →L[ℂ] ℂ)
    (X : Fin n → S →L[ℂ] S) (z : Source n)
    (hL : ∀ i s, L (X i s) = z i * L s) (w : List (Fin n)) (s : S) :
    L ((w.map X).prod s) = (w.map z).prod * L s := by
  induction w generalizing s with
  | nil => simp
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, hL, ih]
      ring

/-- Evaluation compatibility for each extended Taylor coefficient. This
applies in particular to one companion endomorphism and scalar identities.
Only the stated intertwining identities are needed, not commutation. -/
theorem linearEvaluation_finiteBanachExtensionSeries
    {n : ℕ} (p : FormalMultilinearSeries ℂ (Source n) ℂ)
    (L : S →L[ℂ] ℂ) (X : Fin n → S →L[ℂ] S) (z : Source n)
    (hL : ∀ i s, L (X i s) = z i * L s) (d : ℕ) (s : S) :
    L (finiteBanachExtensionSeries p d (fun _ => X) s) =
      p d (fun _ => z) * L s := by
  rw [finiteBanachExtensionSeries_apply_diagonal,
    homogeneous_apply_coordinateWords]
  simp only [sum_apply, smul_apply, map_sum, map_smul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _hw
  have hprod := linearEvaluation_list_prod L X z hL (List.ofFn w) s
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def] at hprod
  rw [hprod]
  simp only [smul_eq_mul]
  ring

/-- Evaluation of the convergent endomorphism extension agrees with the
scalar Taylor sum wherever both displayed series converge. -/
theorem linearEvaluation_finiteBanachExtensionSeries_sum
    [CompleteSpace S] {n : ℕ} (p : FormalMultilinearSeries ℂ (Source n) ℂ)
    (L : S →L[ℂ] ℂ) (X : Fin n → S →L[ℂ] S) (z : Source n)
    (hL : ∀ i s, L (X i s) = z i * L s) (s : S)
    (hX : X ∈ Metric.eball 0
      (finiteBanachExtensionSeries (A := S →L[ℂ] S) p).radius)
    (hz : z ∈ Metric.eball 0 p.radius) :
    L ((finiteBanachExtensionSeries (A := S →L[ℂ] S) p).sum X s) = p.sum z * L s := by
  let evaluation : (S →L[ℂ] S) →L[ℂ] ℂ :=
    L.comp (ContinuousLinearMap.apply ℂ S s)
  have hextended := evaluation.hasSum
    ((finiteBanachExtensionSeries (A := S →L[ℂ] S) p).hasSum hX)
  have hscalar := (p.hasSum hz).mul_right (L s)
  have hterms : (fun d => evaluation (finiteBanachExtensionSeries p d (fun _ => X))) =
      (fun d => p d (fun _ => z) * L s) := by
    funext d
    exact linearEvaluation_finiteBanachExtensionSeries p L X z hL d s
  rw [hterms] at hextended
  exact hextended.unique hscalar

end EndomorphismEvaluation

/-- One companion operator followed by scalar identities for all retained
coordinates. -/
@[expose] noncomputable def finiteDivisionOperatorInput {n : ℕ} (d : ℕ)
    (z : Source (n + 1)) (a : Fin (d + 1) → ℂ) :
    Fin (n + 1) → GeneralDivisionEndomorphism d :=
  Fin.cases (generalDivisionOperator (z 0) a)
    (fun i => z i.succ • (1 : GeneralDivisionEndomorphism d))

/-- The finite-division input satisfies the scalar evaluation identities
required by the Banach extension. -/
theorem evaluation_finiteDivisionOperatorInput {n : ℕ} (d : ℕ)
    (z : Source (n + 1)) (a : Fin (d + 1) → ℂ)
    (i : Fin (n + 1)) (s : GeneralDivisionState d) :
    generalDivisionStateEvaluationLinear (z 0) a
      (finiteDivisionOperatorInput d z a i s) =
        z i * generalDivisionStateEvaluationLinear (z 0) a s := by
  induction i using Fin.cases with
  | zero =>
      simpa only [finiteDivisionOperatorInput, Fin.cases_zero,
        generalDivisionStateEvaluationLinear_apply] using
        generalDivisionStateEvaluation_operator (z 0) a s
  | succ i =>
      change generalDivisionStateEvaluationLinear (z 0) a
        ((z i.succ • (1 : GeneralDivisionEndomorphism d)) s) = _
      simp only [smul_apply, one_apply_eq_self, map_smul, smul_eq_mul]

/-- Applying finite-state evaluation to the convergent extension recovers
the scalar Taylor sum in all source coordinates. -/
theorem finiteDivisionStateEvaluation_extension_sum {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source (n + 1)) ℂ) (d : ℕ)
    (z : Source (n + 1)) (a : Fin (d + 1) → ℂ)
    (hX : finiteDivisionOperatorInput d z a ∈ Metric.eball 0
      (finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p).radius)
    (hz : z ∈ Metric.eball 0 p.radius) :
    generalDivisionStateEvaluationLinear (z 0) a
      ((finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p).sum
        (finiteDivisionOperatorInput d z a) (generalDivisionInitialState d)) =
      p.sum z := by
  have hevaluation := linearEvaluation_finiteBanachExtensionSeries_sum p
    (generalDivisionStateEvaluationLinear (z 0) a) (finiteDivisionOperatorInput d z a) z
    (evaluation_finiteDivisionOperatorInput d z a) (generalDivisionInitialState d) hX hz
  have hinitial : generalDivisionStateEvaluationLinear (z 0) a
      (generalDivisionInitialState d) = 1 := by
    simp [generalDivisionStateEvaluationLinear_apply, generalDivisionStateEvaluation,
      generalDivisionInitialState]
  simpa only [hinitial, mul_one] using hevaluation

end OnLeConjecture.Analytic.Germ
